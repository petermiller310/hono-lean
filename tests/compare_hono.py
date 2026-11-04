#!/usr/bin/env python3
"""Compare the compiled Lean JSON adapter with one exact raw Hono TrieRouter."""
import argparse
import hashlib
import json
import platform
import random
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BASELINE = json.loads((ROOT / 'comparison/baseline.json').read_text())
CORPUS = ROOT / 'examples/v1.json'
METHOD = re.compile(r'[A-Z]+\Z')
COMPONENT = r'(?:[A-Za-z0-9_-]+|:[A-Za-z_][A-Za-z0-9_]*)'
PATTERN = re.compile('/' + COMPONENT + '(?:/' + COMPONENT + r')*(?:/\*)?\Z')
PATH = re.compile(r'(?:/|/[A-Za-z0-9_-]+(?:/[A-Za-z0-9_-]+)*)\Z')


def command(args, **kwargs):
    return subprocess.run(args, check=True, text=True, capture_output=True, **kwargs).stdout


def verify_checkout(path):
    path = Path(path).resolve()
    if not (path / '.git').exists():
        raise ValueError(f'Not a Hono Git checkout: {path}')
    if command(['git', '-C', str(path), 'rev-parse', 'HEAD']).strip() != BASELINE['revision']:
        raise ValueError('Hono checkout is not at the pinned revision')
    if command(['git', '-C', str(path), 'status', '--porcelain', '--untracked-files=all']).strip():
        raise ValueError('Hono checkout has tracked or untracked changes')
    if not (path / 'src/router/trie-router/router.ts').is_file():
        raise ValueError('Pinned raw TrieRouter source is missing')
    return path


def fetch_checkout():
    path = ROOT / '.hono-cache'
    if path.exists():
        return verify_checkout(path)  # Never reset or clean an existing directory.
    path.mkdir()
    command(['git', 'init', str(path)])
    command(['git', '-C', str(path), 'remote', 'add', 'origin', BASELINE['repository']])
    command(['git', '-C', str(path), 'fetch', '--depth=1', 'origin', BASELINE['revision']])
    command(['git', '-C', str(path), 'checkout', '--detach', 'FETCH_HEAD'])
    return verify_checkout(path)


def valid_method(value):
    return isinstance(value, str) and METHOD.fullmatch(value) is not None and value != 'ALL'


def validate_route(route):
    assert route['method'] == 'ALL' or valid_method(route['method']), route
    assert isinstance(route['handler'], str), route
    pattern = route['pattern']
    assert pattern in ('/', '*', '/*') or PATTERN.fullmatch(pattern), route
    names = [part[1:] for part in pattern.split('/') if part.startswith(':')]
    assert len(names) == len(set(names)), route


def reference(routes, request):
    assert valid_method(request['method']) and PATH.fullmatch(request['path']), request
    path = [] if request['path'] == '/' else request['path'][1:].split('/')
    output = []
    for ordinal, route in enumerate(routes):
        if route['method'] not in ('ALL', request['method']):
            continue
        pattern = route['pattern']
        prefix = [] if pattern in ('/', '*', '/*') else pattern[1:].split('/')
        wildcard = pattern in ('*', '/*') or (prefix and prefix[-1] == '*')
        if prefix and prefix[-1] == '*':
            prefix = prefix[:-1]
        if len(path) < len(prefix) or (not wildcard and len(path) != len(prefix)):
            continue
        params = {}
        for component, segment in zip(prefix, path):
            if component.startswith(':'):
                params[component[1:]] = segment
            elif component != segment:
                break
        else:
            output.append(dict(registration=ordinal, handler=route['handler'], params=params))
    return output


def expected_trace(case):
    routes = list(case['routes'])
    for route in routes:
        validate_route(route)
    results = []
    for step in case['steps']:
        if step['op'] == 'register':
            validate_route(step['route'])
            assert same_json(step.get('expectedRegistration', len(routes)), len(routes))
            results.append(dict(registration=len(routes)))
            routes.append(step['route'])
        else:
            assert step['op'] == 'lookup'
            matches = reference(routes, step['request'])
            assert same_json(step.get('expected', matches), matches), 'Fixture expectation disagrees with matching rules'
            results.append(dict(matches=matches))
    return dict(results=results, nextRegistration=len(routes))


def generated_cases(seed, count):
    rng = random.Random(seed)
    cases = []
    for index in range(count):
        base = rng.choice(['students', 'a', 'grade_2', 'constructor'])
        value = rng.choice(['s1', 'new', 'skill-7', '__proto__'])
        first, second = rng.sample(BASELINE['parameterNames'], 2)
        route = lambda method, pattern, handler: dict(method=method, pattern=pattern, handler=handler)
        routes = [route('GET', f'/{base}/:{first}', 'same'), route('ALL', f'/{base}/*', 'log'),
            route('POST', f'/{base}/:{first}', 'write'), route('GET', f'/:{first}/:{second}', 'general'),
            route('GET', f'/{base}/new', ''), route('GET', '*', 'global'),
            route('GET', f'/{base}/:{second}/*', 'named-suffix')]
        rng.shuffle(routes)
        lookup = lambda method, path: dict(op='lookup', request=dict(method=method, path=path))
        steps = [lookup('GET', f'/{base}/{value}'), lookup('POST', f'/{base}/{value}'),
            lookup('HEAD', f'/{base}/{value}'), lookup('GET', f'/{base}'),
            lookup('GET', f'/{base}/{value}/x'), lookup('GET', '/other/y'), lookup('GET', '/'),
            dict(op='register', route=route('GET', f'/{base}/:{first}', 'same')),
            lookup('GET', f'/{base}/s2'),
            dict(op='register', route=route('ALL', f'/{base}/:{first}/worksheets/*', 'worksheets')),
            lookup('GET', f'/{base}/{value}/worksheets'), lookup('GET', f'/{base}/new'),
            dict(op='register', route=dict(routes[0])), lookup('GET', f'/{base}/{value}'),
            lookup('PURGE', f'/{base}/{value}'), lookup('GET', '/missing')]
        cases.append(dict(id=f'generated-{index:03}', routes=routes, steps=steps))
    return cases


D1_ROUTES = [dict(method='GET', pattern='/:__proto__', handler='capture')]
D1_EXPECTED = [dict(registration=0, handler='capture', params={'__proto__': 'alpha'})]
D1_BASELINE = [dict(registration=0, handler='capture', params={'__proto__': {}})]
D1_STEP = dict(op='lookup', request=dict(method='GET', path='/alpha'), expected=D1_EXPECTED,
               baselineDifference='D1', baselineExpected=D1_BASELINE)


def exact_d1(case, step_index, expected, observed):
    return (case.get('id') == 'parameter-name-is-data' and same_json(case['routes'], D1_ROUTES)
        and same_json(case['steps'], [D1_STEP]) and step_index == 0
        and same_json(expected, D1_EXPECTED) and same_json(observed, D1_BASELINE))


def same_json(left, right):
    # Canonical object-key order only; booleans, numbers, strings and arrays keep their types/order.
    return json.dumps(left, sort_keys=True, allow_nan=False) == json.dumps(right, sort_keys=True, allow_nan=False)


def compare(case, expected, lean, hono):
    if not same_json(lean, expected):
        raise ValueError('Lean output differs from the normative expected trace')
    if 'runnerError' in hono:
        raise ValueError(hono['runnerError'])
    if len(hono['results']) != len(expected['results']) or not same_json(hono['nextRegistration'], expected['nextRegistration']):
        raise ValueError('Hono trace length or registration counter differs')
    agreed = differences = 0
    for index, (step, want, actual) in enumerate(zip(case['steps'], expected['results'], hono['results'])):
        annotated = 'baselineDifference' in step or 'baselineExpected' in step
        if annotated:
            approved = (step['op'] == 'lookup'
                and exact_d1(case, index, want['matches'], actual.get('matches'))
                and same_json(actual, dict(matches=D1_BASELINE)))
            if not approved:
                raise ValueError('D1 annotation or exact observation differs from the approved witness')
            differences += 1
        elif not same_json(want, actual):
            raise ValueError(f'Hono differs at step {index}')
        elif step['op'] == 'lookup':
            agreed += 1
    lookups = [item['matches'] for item in hono['results'] if 'matches' in item]
    if len(hono['retained']) != len(lookups):
        raise ValueError('Missing retained raw Hono observations')
    for actual, retained in zip(lookups, hono['retained']):
        if not same_json(actual, retained['before']) or not same_json(retained['before'], retained['after']):
            raise ValueError('A retained raw Hono result changed after a later operation')
    return agreed, differences


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    source = parser.add_mutually_exclusive_group(required=True)
    source.add_argument('--hono', type=Path, help='Existing clean checkout at the exact baseline revision')
    source.add_argument('--fetch', action='store_true', help='Fetch the exact revision into ignored .hono-cache')
    parser.add_argument('--seed', type=int, default=BASELINE['seed'])
    parser.add_argument('--generated', type=int, default=BASELINE['generatedScenarios'])
    parser.add_argument('--report', type=Path, default=ROOT / '.comparison-results/report.json')
    args = parser.parse_args()
    if args.generated < 1:
        parser.error('--generated must be positive')
    hono_path = verify_checkout(args.hono) if args.hono else fetch_checkout()
    bun_version = command(['bun', '--version']).strip()
    if bun_version != BASELINE['bunVersion']:
        raise ValueError(f'Expected Bun {BASELINE["bunVersion"]}; got {bun_version}')
    corpus = json.loads(CORPUS.read_text())
    assert corpus['baseline']['revision'] == BASELINE['revision']
    cases = corpus['scenarios'] + generated_cases(args.seed, args.generated)
    expected = [expected_trace(case) for case in cases]
    hono_outputs = json.loads(command(['bun', str(ROOT / 'comparison/hono_runner.ts'), str(hono_path)], input=json.dumps(cases)))
    if len(hono_outputs) != len(cases):
        raise ValueError('Hono runner returned the wrong number of scenarios')
    failures = []
    agreed = differences = 0
    for case, want, hono in zip(cases, expected, hono_outputs):
        lean = json.loads(command([str(ROOT / '.lake/build/bin/hono-lean-json')], input=json.dumps(case)))
        try:
            a, d = compare(case, want, lean, hono)
            agreed += a
            differences += d
        except (ValueError, KeyError, TypeError) as error:
            failures.append(dict(reason=str(error), scenario=case, expected=want, lean=lean, hono=hono))
    report = dict(baseline=BASELINE, checkout=str(hono_path),
        verifiedRevision=command(['git', '-C', str(hono_path), 'rev-parse', 'HEAD']).strip(),
        bunVersion=bun_version, pythonVersion=platform.python_version(), seed=args.seed,
        generatedScenarios=args.generated, totalScenarios=len(cases),
        lookupObservations=sum(s['op'] == 'lookup' for c in cases for s in c['steps']),
        appendEvents=sum(s['op'] == 'register' for c in cases for s in c['steps']), agreeingLookups=agreed,
        exactD1Differences=differences, failures=failures,
        inputSha256=hashlib.sha256(json.dumps(cases, sort_keys=True).encode()).hexdigest())
    args.report.parent.mkdir(parents=True, exist_ok=True)
    args.report.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({key: value for key, value in report.items() if key not in ('baseline', 'failures')}, indent=2))
    print(f'Unexpected failures: {len(failures)}; report: {args.report}')
    if differences != 1:
        print(f'Expected exactly one approved D1 observation; saw {differences}')
    if failures or differences != 1:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
