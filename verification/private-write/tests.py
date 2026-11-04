#!/usr/bin/env python3
"""Guarded finite evidence for exact Hono private writes, separate from adequacy."""
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
VALUES = ['u','n','f','z','empty','one','text','unicode','objectA','objectB','array','fn','method']


def invoke(command, packet=None):
    return subprocess.run(command, cwd=ROOT, env=ENV, text=True, capture_output=True, timeout=180,
                          input=None if packet is None else json.dumps(packet))


def model(packet):
    result = invoke(['lake','env','lean','--run','verification/private-write/Driver.lean'],packet)
    if result.returncode: raise AssertionError(result.stdout+result.stderr)
    return json.loads(result.stdout)


def native(packet):
    result = invoke(['bun','verification/private-write/native.ts',str(HONO)],packet)
    if result.returncode: raise AssertionError(result.stdout+result.stderr)
    result = json.loads(result.stdout)
    assert result['revision']=='5ca49b0720755c585c9a9835f0a479ceea36fb52'
    assert result['runtime']=='1.4.0' and result['checkedPinnedBlobs']==315
    assert result['transpilation']['verified'] is False
    assert result['transpilation']['plainAssignmentInsertion'] is True
    return result


def encoded(code):
    if code=='u': return dict(kind='undefined')
    if code=='n': return dict(kind='null')
    if code in ['f','t']: return dict(kind='bool',value=code=='t')
    if code in ['z','one']: return dict(kind='number',value=0 if code=='z' else 1)
    if code in ['empty','text','unicode']: return dict(kind='string',units={'empty':[],'text':[120],'unicode':[55296,233]}[code])
    return dict(kind=code)


def oracle(case):
    target, source = case.get('target','child'), case.get('source','parent')
    op = case.get('op','propagation')
    if target not in ['parent','child'] or (op=='propagation' and source not in ['parent','child']):
        return dict(ok=False)
    before = [case.get('a','u'),case.get('b','n'),'shared']
    value = 'shared' if op=='reset' else before[0 if source=='parent' else 1] if op=='propagation' else case.get('rhs','one')
    after = before.copy(); after[0 if target=='parent' else 1] = value
    return dict(ok=True,returned=encoded(value),before=list(map(encoded,before)),after=list(map(encoded,after)),
                setterCalls=0,methodKept=True,publicUnchanged=True,frozenKept=True)


class PrivateWriteTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        for name in ['private-write','class-installation','nullobject']:
            result = invoke(['python3',f'verification/{name}/source.py','--hono',str(HONO)])
            if result.returncode: raise AssertionError(result.stdout+result.stderr)

    def compare(self,cases):
        expected=[oracle(c) for c in cases]
        self.assertEqual(native(dict(cases=cases))['results'],expected)
        self.assertEqual(model(dict(cases=cases)),expected)

    def test_exhaustive_value_alias_and_frozen_contexts(self):
        cases=[]
        for a,b in itertools.product(VALUES,repeat=2):
            for op in ['reset','propagation','wildcard','parameter']:
                for target in ['parent','child']:
                    for frozen in [False,True]:
                        for source in (['parent','child'] if op=='propagation' else ['parent']):
                            cases.append(dict(a=a,b=b,op=op,target=target,source=source,rhs=a,frozen=frozen))
        self.compare(cases)
        print(f'Private-write audit: {len(cases)} exhaustive value/alias/frozen contexts',flush=True)

    def test_seeded_identity_and_brand_failures(self):
        rng=random.Random(1729)
        codes=VALUES+['parent','child','foreign','plain','clone','proxy','shared']
        targets=['parent','child','foreign','plain','clone','proxy','null','undefined','zero']
        cases=[dict(a=rng.choice(codes),b=rng.choice(codes),rhs=rng.choice(codes),
                    op=rng.choice(['reset','propagation','wildcard','parameter']),target=rng.choice(targets),
                    source=rng.choice(targets),frozen=bool(rng.randrange(2))) for _ in range(384)]
        cases += [dict(op=op,target=target,a='fn',b='method',rhs='objectA')
                  for op in ['reset','propagation','wildcard','parameter'] for target in targets]
        self.compare(cases)
        print(f'Private-write audit: {len(cases)} seeded/brand/primitive/proxy-boundary observations',flush=True)

    def test_source_faults_and_method_kind(self):
        source={name:(ROOT/f'verification/private-write/{name}.ts.txt').read_text() for name in ['reset','propagation','wildcard','parameter']}
        variants=[('reset',source['reset'].replace('emptyParams','params')),
                  ('propagation',source['propagation'].replace('nextNode.#params','node.#params')),
                  ('propagation',source['propagation'].replace('= node.#params','= nextNode.#params')),
                  ('wildcard',source['wildcard'].replace('= params','= emptyParams')),
                  ('parameter',source['parameter'].replace('#params','#patterns')),
                  ('propagation',source['propagation'].replace('nextNode.#params','nextNode.#pushHandlerSets'))]
        for op,variant in variants:
            case=dict(op=op,a='text',b='one',rhs='objectA',frozen=True)
            packet=dict(cases=[case],**{op+'Source':variant})
            observed=native(packet)['results']
            self.assertEqual(model(packet),observed)
            self.assertNotEqual(observed,[oracle(case)],variant)
        case=dict(op='parameter',a='method',b='fn',rhs='one',frozen=True)
        self.compare([case])
        # Runtime this remains distinct from ordinary lexical bindings; a
        # supported source fault can store that strict receiver as DATA.
        variant=source['parameter'].replace('= params','= this')
        packet=dict(cases=[case],parameterSource=variant)
        self.assertEqual(model(packet),native(packet)['results'])
        self.assertNotEqual(model(packet),[oracle(case)])

    def test_source_artifacts_and_hidden_checkout_edits(self):
        with tempfile.TemporaryDirectory(prefix='hono-private-write-') as temporary:
            base=Path(temporary);script=base/'verification/private-write/source.py'
            script.parent.mkdir(parents=True);shutil.copy(ROOT/'verification/private-write/source.py',script)
            command=['python3',str(script),'--hono',str(HONO)]
            self.assertEqual(invoke(command+['--write']).returncode,0)
            generated=base/'HonoLean/Upstream/NodePrivateWrite/Generated.lean'
            generated.parent.mkdir(parents=True,exist_ok=True)
            shutil.copy(ROOT/'HonoLean/Upstream/NodePrivateWrite/Generated.lean',generated)
            self.assertEqual(invoke(command).returncode,0)
            for relative in ['verification/private-write/source.json','verification/private-write/reset.ts.txt',
                             'verification/private-write/propagation.ts.txt','verification/private-write/wildcard.ts.txt',
                             'verification/private-write/parameter.ts.txt','HonoLean/Upstream/NodePrivateWrite/Generated.lean']:
                file=base/relative;old=file.read_bytes();file.write_bytes(old+b'\n')
                self.assertNotEqual(invoke(command).returncode,0,relative);file.write_bytes(old)
            clone=base/'checkout';subprocess.run(['git','clone','--shared','--quiet',str(HONO),str(clone)],check=True)
            source='src/router/trie-router/node.ts'
            subprocess.run(['git','-C',str(clone),'update-index','--assume-unchanged',source],check=True)
            file=clone/source;file.write_bytes(file.read_bytes()+b'\n')
            self.assertEqual(subprocess.check_output(['git','-C',str(clone),'status','--porcelain']).strip(),b'')
            self.assertNotEqual(invoke(['python3',str(script),'--hono',str(clone)]).returncode,0)
            self.assertNotEqual(invoke(['bun','verification/private-write/native.ts',str(clone)],dict(cases=[])).returncode,0)


if __name__=='__main__':unittest.main(argv=['private-write-tests'])
