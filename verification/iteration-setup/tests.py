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
    result = invoke(['lake','env','lean','--run','verification/iteration-setup/Driver.lean'], packet)
    if result.returncode: raise AssertionError(result.stdout + result.stderr)
    return json.loads(result.stdout)


def native(packet):
    result = invoke(['bun','verification/iteration-setup/native.ts',str(HONO)], packet)
    if result.returncode: raise AssertionError(result.stdout + result.stderr)
    result = json.loads(result.stdout)
    assert result['revision']=='5ca49b0720755c585c9a9835f0a479ceea36fb52'
    assert result['runtime']=='1.4.0' and result['checkedPinnedBlobs']==315
    assert result['transpilation']['verified'] is False
    assert result['transpilation']['plainEntryInsertion'] is True
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
    """Independent indexed setup, then mutable registration-record effects."""
    parts, nodes = case.get('parts',[[108,105,116]]), case.get('nodes',['parent'])
    i,j = case.get('i',0),case.get('j',0)
    assert 0 <= i < len(parts) and 0 <= j < len(nodes)
    parent = nodes[j]
    if parent not in BRANDED: return dict(ok=False)
    child, wildcard = case.get('child','literal'), case.get('wildcard','u')
    part, query = tuple(parts[i]),case.get('query',GET)
    last = i == len(parts)-1
    children = {o:{} for o in BRANDED}
    children[parent][part] = child
    if child in BRANDED: children[child][(42,)] = wildcard
    selected = children[parent].get(part,'u')
    records, rows = [], {o:[] for o in BRANDED}
    for owner, registrations in [('literal',case.get('literal',[])),('wildcard',case.get('star',[]))]:
        for reg in registrations:
            keys=list(dict.fromkeys(tuple(k) for k in reg['keys']))
            rows[owner].append(len(records))
            records.append(dict(method=reg['method'],handler=reg['handler'],score=len(records)+1,keys=keys,captures=[]))
    params={o:'shared' for o in OWNERS};params[parent]='A'
    entries={name:{tuple(key):value for key,value in case.get(field,[])}
             for name,field in [('A','entries'),('B','laterEntries')]}
    collected=[];temp=[]
    for iteration in range(2 if case.get('repeat') else 1):
        if iteration:params[parent]='B'
        temp=[]  # Source102 allocates a new queue in each supplied outer activation.
        if selected in FALSY:continue
        if selected not in BRANDED:return dict(ok=False)
        params[selected]=params[parent]
        if not last:
            temp.append(selected)
            continue
        targets=([children[selected].get((42,),'u')] if children[selected].get((42,),'u') not in FALSY else [])+[selected]
        for target in targets:
            if case.get('receiver','root') not in BRANDED or target not in BRANDED:return dict(ok=False)
            for index in rows[target]:
                record=records[index]
                if record['method'] != query and record['method'] != ALL:continue
                values=entries.get(params[parent],{})
                record['captures']=[dict(key=list(key),value=encode('u' if values.get(key,'u') in ['u','n'] else values[key])) for key in sorted(record['keys'])]
                collected.append(index)
    matches=[{k:records[index][k] for k in ['handler','score','keys','captures']} for index in collected]
    for match in matches:match['keys']=[list(k) for k in match['keys']]
    return dict(ok=True,next=encode(selected),node=encode(parent),temp=list(map(encode,temp)),matches=matches,
                setup=dict(len=len(parts),part=dict(kind='string',units=parts[i]),isLast=last,offsetsNull=True,
                           queueFresh=True,partsKept=True,nodesKept=True),
                sameRecords=[[a==b for b in collected] for a in collected],
                sameParams=[[a==b for b in collected] for a in collected],
                params=[[o,params[o]] for o in OWNERS],order=len(records),methodKept=True,nullPrototypes=True)


def registration(method, handler=10, keys=None):
    return dict(method=method,handler=handler,keys=[ID,NAME,ID] if keys is None else keys)


class IterationSetupTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        for folder in ['iteration-setup','literal-branch','class-installation','private-write','methods-push']:
            result=invoke(['python3',f'verification/{folder}/source.py','--hono',str(HONO)])
            if result.returncode:raise AssertionError(result.stdout+result.stderr)

    def compare(self,cases):
        expected=[oracle(c) for c in cases]
        self.assertEqual(native(dict(cases=cases))['results'],expected)
        self.assertEqual(model(dict(cases=cases)),expected)

    def test_exhaustive_indices_paths_rows_and_aliases(self):
        profiles=[[],[registration(GET)],[registration(ALL,11)],
                  [registration(POST,10),registration(GET,10),registration(ALL,12)]]
        part_profiles=[([[120]],0),([[120],[121]],0),([[120],[121]],1)]
        node_profiles=[(['parent'],0),(['root','parent'],1),(['parent','root'],0)]
        cases=[dict(child=child,wildcard=star,query=query,literal=literal,star=wild,
                    entries=[[ID,'text'],[NAME,'z']],parts=parts,i=i,nodes=nodes,j=j)
               for child,star,literal,wild,query,(parts,i),(nodes,j) in itertools.product(
                   ['u','literal'],['u','wildcard','literal'],profiles,profiles,
                   [GET,POST,ALL],part_profiles,node_profiles)]
        self.compare(cases)
        print(f'Iteration setup audit: {len(cases)} exhaustive indexed/four-path/registration/alias contexts',flush=True)

    def test_seeded_dense_indices_truthiness_and_retained_aliases(self):
        rng=random.Random(1729)
        codes=FALSY+['t','one','text','root','parent','literal','wildcard','foreign','plain']
        keys=[ID,NAME,[95,95,112,114,111,116,111,95,95],[55296],[48]]
        cases=[]
        for _ in range(384):
            regs=lambda:[registration(rng.choice([GET,POST,ALL]),rng.randrange(3),[rng.choice(keys) for _ in range(rng.randrange(5))]) for _ in range(rng.randrange(5))]
            parts=[rng.choice([[42],[55296],[],[120],[121]]) for _ in range(rng.randrange(1,6))]
            nodes=[rng.choice(BRANDED+['foreign','plain']) for _ in range(rng.randrange(1,5))]
            cases.append(dict(child=rng.choice(codes),wildcard=rng.choice(codes),receiver=rng.choice(codes),
                query=rng.choice([GET,POST,ALL,[88]]),literal=regs(),star=regs(),
                entries=[[key,rng.choice(FALSY+['t','one','text'])] for key in keys],
                laterEntries=[[key,'text'] for key in keys],repeat=bool(rng.randrange(2)),
                parts=parts,i=rng.randrange(len(parts)),nodes=nodes,j=rng.randrange(len(nodes))))
        cases += [dict(parts=[[120],[55296]],i=1,nodes=['root','parent'],j=1,wildcard=star,
                       literal=[registration(GET)],star=[registration(ALL)],entries=[[ID,'one']],
                       laterEntries=[[ID,'text']],repeat=True,receiver=receiver)
                  for star,receiver in itertools.product(['u','wildcard','literal'],['root','foreign'])]
        cases.append(dict(parts=[[120],[121]],i=1,nodes=['parent','root','literal'],j=2,
                          wildcard='literal',literal=[registration(GET,7,[ID])]*32,
                          entries=[[ID,'one']],laterEntries=[[ID,'z']],repeat=True))
        cases += [dict(parts=[[120]],nodes=['parent'],literal=[registration(GET,7,[ID])],entries=[[ID,value]])
                  for value in ['u','n','f','z','empty','t','one','text']]
        self.compare(cases)
        print(f'Iteration setup audit: {len(cases)} seeded/current-node/UTF16/retained-reference contexts',flush=True)

    def test_source_faults_and_erased_metadata(self):
        source={name:(ROOT/f'verification/iteration-setup/{name}.ts.txt').read_text() for name in ['search','iteration','entry']}
        case=dict(parts=[[120],[121]],i=1,nodes=['root','parent'],j=1,wildcard='wildcard',
                  literal=[registration(GET,10)],star=[registration(ALL,20)],entries=[[ID,'text']])
        nonlast=dict(case,i=0)
        star_call="this.#pushHandlerSets(handlerSets, nextNode.#children['*'], method, node.#params)"
        direct_call='this.#pushHandlerSets(handlerSets, nextNode, method, node.#params)'
        swapped=source['entry'].replace(star_call,'__SWAP__').replace(direct_call,star_call).replace('__SWAP__',direct_call)
        variants=[('search',source['search'].replace('parts.length','parts.length - 1')),
                  ('iteration',source['iteration'].replace('parts[i]','parts[0]')),
                  ('iteration',source['iteration'].replace('len - 1','len - -1')),
                  ('iteration',source['iteration'].replace('= []','= curNodes')),
                  ('iteration',source['iteration'].replace('= []','= [parts[i]]')),
                  ('entry',source['entry'].replace('curNodes[j]','curNodes[0]')),
                  ('entry',source['entry'].replace('nextNode.#params = node.#params','nextNode.#params = nextNode.#params')),
                  ('entry',swapped)]
        for name,variant in variants:
            packet=dict(cases=[case,nonlast],**{name+'Source':variant})
            observed=native(packet)['results']
            self.assertEqual(model(packet),observed)
            self.assertNotEqual(observed,[oracle(case),oracle(nonlast)],variant)
        controls=[('search',source['search'].replace('number[] | null','null | number[]')),
                  ('iteration',source['iteration'].replace('part: string','part: unknown'))]
        for name,variant in controls:
            self.assertNotEqual(variant,source[name])
            packet=dict(cases=[case,nonlast],**{name+'Source':variant})
            self.assertEqual(native(packet)['results'],[oracle(case),oracle(nonlast)])
            self.assertEqual(model(packet),[oracle(case),oracle(nonlast)])

    def test_source_artifacts_and_hidden_checkout_edits(self):
        with tempfile.TemporaryDirectory(prefix='hono-iteration-setup-') as temporary:
            base=Path(temporary);script=base/'verification/iteration-setup/source.py'
            script.parent.mkdir(parents=True);shutil.copy(ROOT/'verification/iteration-setup/source.py',script)
            command=['python3',str(script),'--hono',str(HONO)]
            self.assertEqual(invoke(command+['--write']).returncode,0)
            self.assertEqual(invoke(command).returncode,0)
            for relative in ['verification/iteration-setup/source.json','verification/iteration-setup/search.ts.txt',
                             'verification/iteration-setup/iteration.ts.txt','verification/iteration-setup/entry.ts.txt',
                             'HonoLean/Upstream/NodeIterationSetup/Generated.lean']:
                file=base/relative;old=file.read_bytes();file.write_bytes(old+b'\n')
                self.assertNotEqual(invoke(command).returncode,0,relative);file.write_bytes(old)
            clone=base/'checkout';subprocess.run(['git','clone','--shared','--quiet',str(HONO),str(clone)],check=True)
            source='src/router/trie-router/node.ts'
            subprocess.run(['git','-C',str(clone),'update-index','--assume-unchanged',source],check=True)
            file=clone/source;file.write_bytes(file.read_bytes()+b'\n')
            self.assertEqual(subprocess.check_output(['git','-C',str(clone),'status','--porcelain']).strip(),b'')
            self.assertNotEqual(invoke(['python3',str(script),'--hono',str(clone)]).returncode,0)
            self.assertNotEqual(invoke(['bun','verification/iteration-setup/native.ts',str(clone)],dict(cases=[])).returncode,0)


if __name__=='__main__':unittest.main(argv=['iteration-setup-tests'])
