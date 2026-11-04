#!/usr/bin/env python3
"""Finite selected-private-elements source evidence and initialization/registration/call composition."""
import argparse
import itertools
import json
import os
from pathlib import Path
import random
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
ENV = dict(os.environ, ASDF_BUN_VERSION='1.4.0', GIT_OPTIONAL_LOCKS='0')
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--hono', type=Path, required=True)
HONO = parser.parse_args().hono.resolve()


def invoke(command, packet=None):
    return subprocess.run(command, cwd=ROOT, env=ENV, text=True, capture_output=True, timeout=120,
                          input=None if packet is None else json.dumps(packet))


def model(packet):
    result = invoke(['lake', 'env', 'lean', '--run', 'verification/class-installation/Driver.lean'], packet)
    if result.returncode:
        raise AssertionError(result.stdout+result.stderr)
    return json.loads(result.stdout)


def native(packet):
    result = invoke(['bun', 'verification/class-installation/native.ts', str(HONO)], packet)
    if result.returncode:
        raise AssertionError(result.stdout+result.stderr)
    result = json.loads(result.stdout)
    assert result['revision'] == '5ca49b0720755c585c9a9835f0a479ceea36fb52'
    assert result['runtime'] == '1.4.0' and result['checkedPinnedBlobs'] == 315
    assert result['transpilation']['verified'] is False
    assert len(result['transpilation']['inputSha256']) == len(result['transpilation']['emittedSha256']) == 64
    return result


FALSY = {'u','n','f','z','empty'}
def units(text):
    data=text.encode('utf-16-le',errors='surrogatepass')
    return [int.from_bytes(data[i:i+2],'little') for i in range(0,len(data),2)]
def encoded(code):
    if code=='u':return dict(kind='undefined')
    if code=='n':return dict(kind='null')
    if code in ['f','t']:return dict(kind='bool',value=code=='t')
    if code in ['z','one']:return dict(kind='number',value=0 if code=='z' else 1)
    return dict(kind='string',units=[] if code=='empty' else units('x'))
def query_oracle(query):
    if query is None:return None
    node=dict((tuple(k),v) for k,v in query.get('nodeEntries',[]))
    temporary=dict((tuple(k),v) for k,v in query.get('parameterEntries',[]))
    matches=[]
    for index,r in enumerate(query['registrations']):
        if r['method'] not in [query['method'],units('ALL')]:continue
        keys=list(dict.fromkeys(tuple(k) for k in r['events']))
        captures=[]
        for at,key in enumerate(keys):
            old=node.get(key,'u');temp=temporary.get(key,'u')
            value=('u' if old in ['u','n'] else old) if query['kind']=='four' else old if (at==0 and old not in FALSY) or temp in ['u','n'] else temp
            captures.append(dict(key=list(key),value=encoded(value)))
        matches.append(dict(handler=r['handler'],score=index+1,keys=[list(k) for k in keys],captures=sorted(captures,key=lambda x:x['key'])))
    return dict(matches=matches,returned=dict(kind='undefined'),order=len(query['registrations']),nullPrototypes=True,methodValuesKept=True)
def query_case(registrations,kind='five'):
    return dict(counts=[0,2,1],priorDefinitions=2,baseObjects=3,baseArrays=2,existingStamps=[7,100],query=dict(
        receiver=0,target=1,kind=kind,method=units('GET'),registrations=registrations,
        nodeEntries=[[units('id'),'text'],[units('name'),'one']],parameterEntries=[[units('id'),'one'],[units('name'),'text']]))


def oracle(case):
    owners = [class_index for class_index, count in enumerate(case['counts']) for _ in range(count)]
    instance = dict(methodsLength=0, patternsLength=0, childrenOwnCount=0, childrenNullPrototype=True,
                    pattern='undefined', paramsIsModule=True, methodsPatternsDistinct=True, publicOwnCount=0, prototypeKept=True, methodIsFunction=True)
    return dict(instances=[instance]*len(owners), arraysIsolated=True, childrenIsolated=True, sharedParams=True,
                moduleNullPrototype=True, helperCalls=1+len(owners), order=0,
                classBrandMatrix=[[class_index == owner for owner in owners] for class_index in range(len(case['counts']))],
                unbrandedRejected=True, methodSharedMatrix=[[a == b for b in owners] for a in owners], query=query_oracle(case.get('query')))


class ClassInstallationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        for name in ['class-installation', 'nullobject', 'methods-push', 'private-call', 'search-entry']:
            result = invoke(['python3', f'verification/{name}/source.py', '--hono', str(HONO)])
            if result.returncode:
                raise AssertionError(result.stdout+result.stderr)

    def compare(self, cases):
        expected = [oracle(case) for case in cases]
        packet = dict(cases=cases)
        self.assertEqual(native(packet)['results'], expected)
        self.assertEqual(model(packet), expected)

    def test_class_identity_and_per_instance_allocations(self):
        cases = [dict(counts=list(counts), baseObjects=1+index%5, baseArrays=index%4,
                      existingStamps=[index, 2*index+17], priorDefinitions=index%4)
                 for index, counts in enumerate(counts for length in range(5) for counts in itertools.product(range(4), repeat=length))]
        self.compare(cases)
        print(f'Private class audit: {len(cases)} class/instance contexts, including zero-instance definitions', flush=True)

    def test_seeded_frames_and_long_identity_ranges(self):
        rng = random.Random(1729)
        cases = [dict(counts=[rng.randrange(6) for _ in range(rng.randrange(7))], baseObjects=rng.randrange(1, 12),
                      baseArrays=rng.randrange(12), priorDefinitions=rng.randrange(8), existingStamps=[rng.randrange(10000) for _ in range(rng.randrange(8))])
                 for _ in range(128)]
        cases += [dict(counts=[0, 32, 0, 16], existingStamps=[999999]), dict(counts=[1]*32), dict(counts=[0]*32)]
        self.compare(cases)
        print(f'Private class frame audit: {len(cases)} seeded/long contexts and prior stamps', flush=True)

    def test_exhaustive_initialization_registration_actual_call(self):
        events=[[],[units('id')],[units('id'),units('name')],[units('id'),units('id'),units('name')],
                [units('__proto__'),units('\ud800')],[units('name'),units('id')]]
        choices=[dict(method=units(m),handler=7,events=e) for m in ['GET','ALL','POST'] for e in events]
        cases=[query_case(list(seq),kind) for length in range(3) for seq in itertools.product(choices,repeat=length) for kind in ['four','five']]
        self.compare(cases)
        print(f'Class pipeline audit: {len(cases)} exhaustive initialized registration/call contexts',flush=True)

    def test_seeded_and_long_initialized_calls(self):
        rng=random.Random(1729);cases=[]
        alphabet=[units(t) for t in ['', 'id','name','__proto__','constructor','0','é','\ud800']]
        for _ in range(128):
            registrations=[dict(method=units(rng.choice(['GET','POST','ALL'])),handler=rng.randrange(3),
                                events=[rng.choice(alphabet) for _ in range(rng.randrange(7))]) for _ in range(rng.randrange(9))]
            for kind in ['four','five']:
                case=query_case(registrations,kind);q=case['query'];q['method']=units(rng.choice(['GET','POST','ALL']))
                q['nodeEntries']=[[k,rng.choice(['u','n','f','z','empty','text','one'])] for k in alphabet]
                q['parameterEntries']=[[k,rng.choice(['u','n','f','z','empty','text','one'])] for k in alphabet]
                if rng.randrange(2):q['receiver']=q['target']
                cases.append(case)
        for kind in ['four','five']:
            cases.append(query_case([dict(method=units('GET'),handler=1,events=[units(str(i)) for i in range(96)])],kind))
            cases.append(query_case([dict(method=units('ALL'),handler=1,events=[units('id')])]*65,kind))
        self.compare(cases)
        print(f'Class pipeline audit: {len(cases)} seeded/long initialized registration/call contexts',flush=True)

    def test_source_faults_and_erased_type_controls(self):
        fields = (ROOT/'verification/class-installation/fields.ts.txt').read_text()
        preamble = (ROOT/'verification/class-installation/preamble.ts.txt').read_text()
        case = dict(counts=[0, 2, 1])
        faults = [dict(fieldsSource=fields.replace('HandlerSet<T>>[] = []', 'HandlerSet<T>>[] = [null]')),
                  dict(fieldsSource=fields.replace('Node<T>[] = []', 'Node<T>[] = [null]')),
                  dict(fieldsSource=fields.replace('= createNullObject()', '= emptyParams')),
                  dict(fieldsSource=fields.replace('= emptyParams', '= createNullObject()')),
                  dict(fieldsSource=fields.replace('#pattern?: Pattern | string', '#pattern?: Pattern | string = null')),
                  dict(preambleSource=preamble.replace('order = 0', 'order = 7'))]
        for fault in faults:
            packet = dict(cases=[case], **fault)
            observed = native(packet)['results']
            self.assertEqual(model(packet), observed)
            self.assertNotEqual(observed, [oracle(case)])
        for variant in [fields.replace('HandlerSet<T>', 'OtherShape<U>'), fields.replace('#pattern?:', '#pattern:')]:
            packet = dict(cases=[case], fieldsSource=variant)
            self.assertEqual(native(packet)['results'], [oracle(case)])
            self.assertEqual(model(packet), [oracle(case)])

    def test_method_source_faults_and_type_controls(self):
        method=(ROOT/'verification/class-installation/method.ts.txt').read_text()
        case=query_case([dict(method=units('GET'),handler=1,events=[units('id'),units('name')]),
                         dict(method=units('ALL'),handler=2,events=[units('id'),units('name')])])
        for variant in [method.replace('let i = 0, len = node.#methods.length','let i = 1, len = node.#methods.length'),
                        method.replace('params?.[key] && !i','params?.[key] && i'),
                        method.rsplit('  }',1)[0]+'    return 9\n  }\n']:
            packet=dict(cases=[case],methodSource=variant);observed=native(packet)['results']
            self.assertEqual(model(packet),observed);self.assertNotEqual(observed,[oracle(case)])
        for variant in [method.replace('params?:','params:'),method.replace('HandlerParamsSet<T>','OtherShape<U>')]:
            packet=dict(cases=[case],methodSource=variant)
            self.assertEqual(native(packet)['results'],[oracle(case)]);self.assertEqual(model(packet),[oracle(case)])

    def test_native_method_first_and_readonly_boundary(self):
        self.assertEqual(native(dict(scopeProbes=True))['scope'], dict(methodSeenDuringField='function',result=7,
            duplicateThrows=True,fieldInitializers=1,readonlyRejected=True))

    def test_source_artifacts_and_hidden_checkout_edits(self):
        with tempfile.TemporaryDirectory(prefix='hono-class-installation-') as temporary:
            base = Path(temporary); script = base/'verification/class-installation/source.py'
            script.parent.mkdir(parents=True); shutil.copy(ROOT/'verification/class-installation/source.py', script)
            command = ['python3', str(script), '--hono', str(HONO)]
            self.assertEqual(invoke(command+['--write']).returncode, 0)
            self.assertEqual(invoke(command).returncode, 0)
            for relative in ['verification/class-installation/source.json', 'verification/class-installation/fields.ts.txt',
                             'verification/class-installation/preamble.ts.txt', 'verification/class-installation/method.ts.txt', 'HonoLean/Upstream/NodeClass/Generated.lean']:
                file = base/relative; original = file.read_bytes(); file.write_bytes(original+b'\n')
                self.assertNotEqual(invoke(command).returncode, 0, relative); file.write_bytes(original)
            clone = base/'checkout'; subprocess.run(['git', 'clone', '--shared', '--quiet', str(HONO), str(clone)], check=True)
            source = 'src/router/trie-router/node.ts'
            subprocess.run(['git', '-C', str(clone), 'update-index', '--assume-unchanged', source], check=True)
            file = clone/source; file.write_bytes(file.read_bytes()+b'\n')
            self.assertEqual(subprocess.check_output(['git', '-C', str(clone), 'status', '--porcelain']).strip(), b'')
            self.assertNotEqual(invoke(['python3', str(script), '--hono', str(clone)]).returncode, 0)
            self.assertNotEqual(invoke(['bun', 'verification/class-installation/native.ts', str(clone)], dict(cases=[])).returncode, 0)


if __name__ == '__main__':
    unittest.main(argv=['class-installation-tests'])
