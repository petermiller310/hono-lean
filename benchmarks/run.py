#!/usr/bin/env python3
"""Validate, then measure in-process build and lookup costs for two fixed workloads."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import random
import statistics
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tests'))
import compare_hono as comparison


def validate_config(config):
    for key in ('seed', 'routes', 'queries', 'warmupSamples', 'samples', 'buildIterations', 'lookupIterations'):
        if type(config.get(key)) is not int:
            raise ValueError(f'{key} must be an integer')
    if config['routes'] < 4 or config['queries'] < 4 or config['samples'] < 2:
        raise ValueError('Use at least four routes/queries and two measured samples')
    if min(config[k] for k in ('warmupSamples', 'buildIterations', 'lookupIterations')) < 1:
        raise ValueError('Warmup and iteration counts must be positive')


def workloads(config):
    rng = random.Random(config['seed'])
    route = lambda pattern, i: dict(method='ALL' if i % 5 == 0 else 'GET', pattern=pattern, handler=f'r{i}')
    shared = [route(f'/api/v1/students/s{i}', i) for i in range(config['routes'])]
    overlapping = [route((f'/:kind{i}/:id{i}/*', f'/students/:id{i}/*',
        '/students/*', f'/students/:id{i}/worksheets/*')[i % 4], i) for i in range(config['routes'])]
    result = []
    for name, routes in [('shared-prefix', shared), ('overlapping', overlapping)]:
        second = list(routes); rng.shuffle(second)
        requests = []
        for i in range(config['queries']):
            if name == 'shared-prefix':
                path = f'/api/v1/students/s{rng.randrange(config["routes"])}'
                if i % 4 == 2: path = f'/api/v1/students/missing{i}'
                method = 'POST' if i % 4 == 3 else 'GET'
            else:
                path = (f'/students/s{i}', f'/students/s{i}/worksheets',
                    f'/students/s{i}/worksheets/w{i}/extra', f'/other/s{i}')[i % 4]
                method = 'HEAD' if i % 8 == 7 else 'GET'
            requests.append(dict(method=method, path=path))
        result.append(dict(name=name, banks=[dict(routes=routes), dict(routes=second)], requests=requests))
    return result


def expected(work):
    return [dict(name=w['name'], observations=[[comparison.reference(bank['routes'], q)
        for q in w['requests']] for bank in w['banks']]) for w in work]


def digest(items):
    return sum(item['registration'] + len(item['handler']) + len(item['params']) + 1
        + sum(len(k) + len(v) for k, v in item['params'].items()) for item in items) % 2**32


def validate_samples(outputs, wanted, config):
    if len(outputs) != len(wanted): raise ValueError('Wrong workload count')
    for output, oracle in zip(outputs, wanted):
        if output['name'] != oracle['name']: raise ValueError('Workload order/name differs')
        banks = [[digest(items) for items in bank] for bank in oracle['observations']]
        for phase, iterations in [('build', config['buildIterations']), ('lookup', config['lookupIterations'])]:
            if len(output[phase]) != config['samples']: raise ValueError('Wrong sample count')
            for i, sample in enumerate(output[phase]):
                offset = config['warmupSamples'] + i
                checksum = sum(banks[(offset + n) % len(banks)][0] if phase == 'build'
                    else banks[0][(offset + n) % len(banks[0])] for n in range(iterations)) % 2**32
                if type(sample['nanos']) is not int or sample['nanos'] <= 0:
                    raise ValueError('Nonpositive or noninteger elapsed nanoseconds')
                if not comparison.same_json(sample['checksum'], checksum):
                    raise ValueError(f'{output["name"]} {phase} checksum differs')


def invoke(command, document):
    return json.loads(comparison.command(command, input=json.dumps(document)))


def validate_preflight(observed, wanted, runtime):
    if not comparison.same_json(observed, wanted):
        raise ValueError(f'{runtime} semantic preflight differs; no timings accepted')


def summarize(outputs, config):
    result = {}
    for w in outputs:
        result[w['name']] = {}
        for phase, count in [('build', config['buildIterations']), ('lookup', config['lookupIterations'])]:
            times = [s['nanos'] / count for s in w[phase]]
            result[w['name']][phase] = dict(medianNsPerOp=statistics.median(times),
                minNsPerOp=min(times), maxNsPerOp=max(times))
    return result


def source_hashes():
    files = [ROOT / 'BenchMain.lean', ROOT / 'lakefile.toml', *sorted((ROOT / 'HonoLean').rglob('*.lean')),
        *sorted((ROOT / 'benchmarks').glob('*.py')), *sorted((ROOT / 'benchmarks').glob('*.ts'))]
    return {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    source = parser.add_mutually_exclusive_group(required=True)
    source.add_argument('--hono', type=Path)
    source.add_argument('--fetch', action='store_true')
    parser.add_argument('--config', type=Path, default=ROOT / 'benchmarks/config.json')
    parser.add_argument('--smoke', action='store_true', help='Small semantic/timing-shape check; no speed threshold')
    parser.add_argument('--report', type=Path, default=ROOT / '.benchmark-results/report.json')
    args = parser.parse_args()
    config = json.loads(args.config.read_text())
    if args.smoke: config.update(routes=16, queries=8, warmupSamples=1, samples=2, buildIterations=2, lookupIterations=32)
    validate_config(config)
    hono = comparison.verify_checkout(args.hono) if args.hono else comparison.fetch_checkout()
    bun_version = comparison.command(['bun', '--version']).strip()
    if bun_version != comparison.BASELINE['bunVersion']: raise ValueError('Wrong Bun version')
    comparison.command(['lake', 'build', 'router-bench'], cwd=ROOT)
    work = workloads(config)
    for w in work:
        for bank in w['banks']:
            for route in bank['routes']: comparison.validate_route(route)
    wanted = expected(work)
    commands = dict(lean=[str(ROOT / '.lake/build/bin/router-bench')],
        hono=['bun', str(ROOT / 'benchmarks/hono.ts'), str(hono)])
    document = dict(config=config, workloads=work)
    for runtime, command in commands.items():
        observed = invoke(command, dict(document, mode='validate'))
        validate_preflight(observed, wanted, runtime)
    measurements = {runtime: invoke(command, dict(document, mode='measure')) for runtime, command in commands.items()}
    for output in measurements.values(): validate_samples(output, wanted, config)
    trace = ROOT / '.lake/build/ir/BenchMain.c.o.export.trace'
    compile_log = json.loads(trace.read_text())['log'] if trace.exists() else []
    prefix = comparison.command(['lake', 'env', 'lean', '--print-prefix']).strip()
    sanitize = lambda text: text.replace(str(ROOT), '<project>').replace(prefix, '<lean-toolchain>')
    compile_log = [dict(item, message=sanitize(item['message'])) for item in compile_log]
    report = dict(config=config, inputSha256=hashlib.sha256(json.dumps(document, sort_keys=True).encode()).hexdigest(),
        honoRevision=comparison.command(['git', '-C', str(hono), 'rev-parse', 'HEAD']).strip(),
        leanVersion=comparison.command(['lake', 'env', 'lean', '--version']).strip(), bunVersion=bun_version,
        pythonVersion=platform.python_version(), platform=platform.platform(), machine=platform.machine(),
        cpu=platform.processor() or 'unavailable', cpuCount=os.cpu_count(),
        cCompiler=sanitize(comparison.command(['lake', 'env', 'leanc', '--version']).strip()), compileLog=compile_log,
        binarySha256=hashlib.sha256((ROOT / '.lake/build/bin/router-bench').read_bytes()).hexdigest(),
        projectRevision=comparison.command(['git', '-C', str(ROOT), 'rev-parse', 'HEAD']).strip(),
        projectDirty=bool(comparison.command(['git', '-C', str(ROOT), 'status', '--porcelain']).strip()),
        sourceSha256=source_hashes(), measurements=measurements,
        summary={runtime: summarize(output, config) for runtime, output in measurements.items()},
        workloads=[dict(name=w['name'], variants=len(w['banks']), routes=len(w['banks'][0]['routes']),
            queries=len(w['requests']), matchesPerQuery=[len(x) for x in oracle['observations'][0]])
            for w, oracle in zip(work, wanted)],
        boundaries=dict(build='fresh core router + array push; current batch roots retained until stop; post-stop lookup sink excluded; Lean teardown outside, Hono GC may occur in samples',
            lookup='one existing router + core lookup + small length/ordinal digest',
            excluded='process startup, external JSON/text parsing, output formatting, semantic preflight',
            asymmetry='Lean uses pre-parsed typed paths; Hono add/match split canonical text internally',
            caches='fresh routers in a warm process; Hono module-level pattern cache is warm, not cold-start construction',
            environment='sequential runtime processes; no CPU affinity, power, load or GC isolation; CPU brand unavailable'))
    args.report.parent.mkdir(parents=True, exist_ok=True)
    args.report.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(dict(inputSha256=report['inputSha256'], config=config, summary=report['summary']), indent=2))
    print(f'Preflight and sample checksums passed; raw samples: {args.report}')


if __name__ == '__main__':
    main()
