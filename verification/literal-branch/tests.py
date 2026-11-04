#!/usr/bin/env python3
"""Finite exact-branch/model/oracle evidence, distinct from native adequacy."""
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
OWNERS = ['root', 'parent', 'literal', 'wildcard', 'foreign']
BRANDED = OWNERS[:-1]
FALSY = ['u', 'n', 'f', 'z', 'empty']
GET, POST, ALL = [71,69,84], [80,79,83,84], [65,76,76]
ID, NAME = [105,100], [110,97,109,101]


def invoke(command, packet=None):
    return subprocess.run(command, cwd=ROOT, env=ENV, text=True, capture_output=True,
                          input=None if packet is None else json.dumps(packet), timeout=240)


def model(packet):
    result = invoke(['lake','env','lean','--run','verification/literal-branch/Driver.lean'], packet)
    if result.returncode: raise AssertionError(result.stdout + result.stderr)
    return json.loads(result.stdout)


def native(packet):
    result = invoke(['bun','verification/literal-branch/native.ts',str(HONO)], packet)
    if result.returncode: raise AssertionError(result.stdout + result.stderr)
    result = json.loads(result.stdout)
    assert result['revision']=='5ca49b0720755c585c9a9835f0a479ceea36fb52'
    assert result['runtime']=='1.4.0' and result['checkedPinnedBlobs']==315
    assert result['transpilation']['verified'] is False
    assert result['transpilation']['plainBranchInsertion'] is True
    return result


def encode(code):
    if code in OWNERS: return dict(kind=code)
    if code=='u': return dict(kind='undefined')
    if code=='n': return dict(kind='null')
    if code in ['f','t']: return dict(kind='bool',value=code=='t')
    if code in ['z','one']: return dict(kind='number',value=0 if code=='z' else 1)
    if code in ['empty','text']: return dict(kind='string',units=[] if code=='empty' else [120])
    raise AssertionError(code)


def oracle(case):
    """Independent branch decision plus mutable registration-record observations."""
    child, wildcard = case.get('child','literal'), case.get('wildcard','u')
    part, query = tuple(case.get('part',[108,105,116])), case.get('query',GET)
    children = {o:{} for o in BRANDED}
    children['parent'][part] = child
    if child in BRANDED: children[child][(42,)] = wildcard
    selected = children['parent'].get(part,'u')
    records, rows = [], {o:[] for o in BRANDED}
    for owner, registrations in [('literal',case.get('literal',[])),('wildcard',case.get('star',[]))]:
        for reg in registrations:
            keys = list(dict.fromkeys(tuple(k) for k in reg['keys']))
            rows[owner].append(len(records))
            records.append(dict(method=reg['method'],handler=reg['handler'],score=len(records)+1,keys=keys,captures=[]))
    params = {o:'shared' for o in OWNERS}; params['parent']='A'
    entries = {name:{tuple(key):value for key,value in case.get(field,[])}
               for name,field in [('A','entries'),('B','laterEntries')]}
    collected, temp = [], case.get('prefix',[]).copy()
    for iteration in range(2 if case.get('repeat') else 1):
        if iteration: params['parent']='B'
        if selected in FALSY: continue
        if selected not in BRANDED: return dict(ok=False)
        params[selected] = params['parent']
        if case.get('last','t') in FALSY:
            temp.append(selected)
            continue
        targets = ([children[selected].get((42,),'u')] if children[selected].get((42,),'u') not in FALSY else []) + [selected]
        for target in targets:
            if case.get('receiver','root') not in BRANDED or target not in BRANDED: return dict(ok=False)
            for index in rows[target]:
                record = records[index]
                if record['method'] != query and record['method'] != ALL: continue
                values = entries.get(params['parent'],{})
                record['captures'] = [dict(key=list(key),value=encode('u' if values.get(key,'u') in ['u','n'] else values[key])) for key in sorted(record['keys'])]
                collected.append(index)
    matches = [{k:records[i][k] for k in ['handler','score','keys','captures']} for i in collected]
    for match in matches: match['keys']=[list(k) for k in match['keys']]
    return dict(ok=True,next=encode(selected),temp=list(map(encode,temp)),matches=matches,
                sameRecords=[[a==b for b in collected] for a in collected],
                sameParams=[[a==b for b in collected] for a in collected],
                params=[[o,params[o]] for o in OWNERS],order=len(records),methodKept=True,nullPrototypes=True)


def registration(method, handler=10, keys=None):
    return dict(method=method,handler=handler,keys=[ID,NAME,ID] if keys is None else keys)


class LiteralBranchTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        for folder in ['literal-branch','class-installation','private-write','methods-push']:
            result=invoke(['python3',f'verification/{folder}/source.py','--hono',str(HONO)])
            if result.returncode: raise AssertionError(result.stdout+result.stderr)

    def compare(self,cases):
        expected=[oracle(c) for c in cases]
        self.assertEqual(native(dict(cases=cases))['results'],expected)
        self.assertEqual(model(dict(cases=cases)),expected)

    def test_exhaustive_paths_rows_and_aliases(self):
        profiles=[[],[registration(GET)],[registration(ALL,11)],
                  [registration(POST,10),registration(GET,10),registration(ALL,12)]]
        cases=[dict(child=child,wildcard=star,last=last,query=query,literal=literal,star=wild,
                    entries=[[ID,'text'],[NAME,'z']],prefix=prefix)
               for child,last,star,literal,wild,query,prefix in itertools.product(
                   ['u','literal'],['f','t'],['u','wildcard','literal'],profiles,profiles,
                   [GET,POST,ALL],[[],['parent']])]
        self.compare(cases)
        print(f'Literal branch audit: {len(cases)} exhaustive four-path/registration/alias contexts',flush=True)

    def test_seeded_truthiness_boundaries_and_retained_aliases(self):
        rng=random.Random(1729)
        codes=FALSY+['t','one','text','root','parent','literal','wildcard','foreign','plain']
        keys=[ID,NAME,[95,95,112,114,111,116,111,95,95],[55296],[48]]
        cases=[]
        for _ in range(384):
            regs=lambda:[registration(rng.choice([GET,POST,ALL]),rng.randrange(3),[rng.choice(keys) for _ in range(rng.randrange(5))]) for _ in range(rng.randrange(5))]
            cases.append(dict(child=rng.choice(codes),wildcard=rng.choice(codes),last=rng.choice(codes),receiver=rng.choice(codes),
                              query=rng.choice([GET,POST,ALL,[88]]),literal=regs(),star=regs(),
                              entries=[[key,rng.choice(FALSY+['t','one','text'])] for key in keys],
                              laterEntries=[[key,'text'] for key in keys],repeat=bool(rng.randrange(2)),
                              part=rng.choice([[42],[55296],[],[99,111,110,115,116,114,117,99,116,111,114]]),prefix=['root']))
        cases += [dict(child='literal',wildcard=star,last=last,receiver=receiver,literal=[registration(GET)],star=[registration(ALL)],
                       entries=[[ID,'one']],laterEntries=[[ID,'text']],repeat=True)
                  for star,last,receiver in itertools.product(['u','wildcard','literal'],codes,['root','foreign'])]
        cases.append(dict(wildcard='literal',literal=[registration(GET,7,[ID])]*32,entries=[[ID,'one']],laterEntries=[[ID,'z']],repeat=True))
        cases += [dict(literal=[registration(GET,7,[ID])],entries=[[ID,value]])
                  for value in ['u','n','f','z','empty','t','one','text']]
        self.compare(cases)
        print(f'Literal branch audit: {len(cases)} seeded/truthiness/retained-reference contexts',flush=True)

    def test_parsed_source_faults(self):
        source=(ROOT/'verification/literal-branch/source.ts.txt').read_text()
        case=dict(wildcard='wildcard',literal=[registration(GET,10)],star=[registration(ALL,20)],entries=[[ID,'text']])
        variants=[source.replace('if (nextNode)','if (!nextNode)'),
                  source.replace('if (isLast)','if (!isLast)'),
                  source.replace('nextNode.#params = node.#params','nextNode.#params = nextNode.#params'),
                  source.replace("nextNode.#children['*']",'nextNode'),
                  source.replace('tempNodes.push(nextNode)','tempNodes.push(node)'),
                  source.replace('const nextNode = node.#children[part]','const nextNode = node')]
        star_call="this.#pushHandlerSets(handlerSets, nextNode.#children['*'], method, node.#params)"
        direct_call='this.#pushHandlerSets(handlerSets, nextNode, method, node.#params)'
        variants.append(source.replace(star_call,'__SWAP__').replace(direct_call,star_call).replace('__SWAP__',direct_call))
        queue=dict(case,last='f')
        for variant in variants:
            packet=dict(branchSource=variant,cases=[case,queue])
            result=native(packet)['results']
            self.assertEqual(model(packet),result)
            self.assertNotEqual(result,[oracle(case),oracle(queue)],variant)

    def test_source_artifacts_and_hidden_checkout_edits(self):
        with tempfile.TemporaryDirectory(prefix='hono-literal-branch-') as temporary:
            base=Path(temporary);script=base/'verification/literal-branch/source.py'
            script.parent.mkdir(parents=True);shutil.copy(ROOT/'verification/literal-branch/source.py',script)
            command=['python3',str(script),'--hono',str(HONO)]
            self.assertEqual(invoke(command+['--write']).returncode,0)
            self.assertEqual(invoke(command).returncode,0)
            for relative in ['verification/literal-branch/source.json','verification/literal-branch/source.ts.txt',
                             'HonoLean/Upstream/NodeLiteralBranch/Generated.lean']:
                file=base/relative;old=file.read_bytes();file.write_bytes(old+b'\n')
                self.assertNotEqual(invoke(command).returncode,0,relative);file.write_bytes(old)
            clone=base/'checkout';subprocess.run(['git','clone','--shared','--quiet',str(HONO),str(clone)],check=True)
            source='src/router/trie-router/node.ts'
            subprocess.run(['git','-C',str(clone),'update-index','--assume-unchanged',source],check=True)
            file=clone/source;file.write_bytes(file.read_bytes()+b'\n')
            self.assertEqual(subprocess.check_output(['git','-C',str(clone),'status','--porcelain']).strip(),b'')
            self.assertNotEqual(invoke(['python3',str(script),'--hono',str(clone)]).returncode,0)
            self.assertNotEqual(invoke(['bun','verification/literal-branch/native.ts',str(clone)],dict(cases=[])).returncode,0)


if __name__=='__main__': unittest.main(argv=['literal-branch-tests'])
