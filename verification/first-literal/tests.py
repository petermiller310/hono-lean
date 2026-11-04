#!/usr/bin/env python3
"""Contiguous startup/first-literal evidence, separate from whole-search claims."""
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

ROOT=Path(__file__).resolve().parents[2]
ENV=dict(os.environ,ASDF_BUN_VERSION='1.4.0',GIT_OPTIONAL_LOCKS='0')
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--hono',type=Path,required=True)
HONO=parser.parse_args().hono.resolve()
GET,POST,ALL=[71,69,84],[80,79,83,84],[65,76,76]
ID,NAME=[105,100],[110,97,109,101]
OWNERS=['root','parent','literal','wildcard','foreign']
BRANDED=OWNERS[:-1]
FALSY=['u','n','f','z','empty']


def invoke(command,packet=None):
    return subprocess.run(command,cwd=ROOT,env=ENV,text=True,capture_output=True,
        input=None if packet is None else json.dumps(packet),timeout=240)


def model(packet):
    result=invoke(['lake','env','lean','--run','verification/first-literal/Driver.lean'],packet)
    if result.returncode:raise AssertionError(result.stdout+result.stderr)
    return json.loads(result.stdout)


def native(packet):
    result=invoke(['bun','verification/first-literal/native.ts',str(HONO)],packet)
    if result.returncode:raise AssertionError(result.stdout+result.stderr)
    result=json.loads(result.stdout)
    assert result['revision']=='5ca49b0720755c585c9a9835f0a479ceea36fb52'
    assert result['runtime']=='1.4.0' and result['checkedPinnedBlobs']==315
    assert result['transpilation']['verified'] is False
    assert result['transpilation']['importedPinnedSplit'] and result['transpilation']['plainEntryInsertion']
    assert result['transpilation']['contiguousSourceBytes']==1094
    assert result['transpilation']['sourceOverrides']==[key for key in ['startupSource','entrySource'] if key in packet]
    return result['results']


def partition(path):
    fields,field=[],[]
    for unit in path:
        if unit==47:fields.append(field);field=[]
        else:field.append(unit)
    fields.append(field)
    return fields[1:] if fields[0]==[] else fields


def encode(code):
    if code in OWNERS:return dict(kind=code)
    if code=='u':return dict(kind='undefined')
    if code=='n':return dict(kind='null')
    if code in ['f','t']:return dict(kind='bool',value=code=='t')
    if code in ['z','one']:return dict(kind='number',value=0 if code=='z' else 1)
    if code in ['empty','text']:return dict(kind='string',units=[] if code=='empty' else [120])
    raise AssertionError(code)


def oracle(case):
    """Initial maps/records, real reset, then ordered first-branch effects."""
    if case.get('receiver','root')!='root':return dict(ok=False)
    parts=partition(case.get('path',[47,108,105,116]));entered=bool(parts)
    child,star=case.get('child','literal'),case.get('wildcard','u')
    children={owner:{} for owner in BRANDED}
    if entered:children['root'][tuple(parts[0])]=child
    if child in BRANDED:children[child][(42,)]=star
    selected=children['root'].get(tuple(parts[0]),'u') if entered else 'u'
    rows={owner:[] for owner in BRANDED};records=[]
    for owner,field in [('root','root'),('literal','literal'),('wildcard','star')]:
        for registration in case.get(field,[]):
            rows[owner].append(len(records))
            records.append(dict(method=registration['method'],handler=registration['handler'],score=len(records)+1,
                keys=list(dict.fromkeys(tuple(key) for key in registration['keys']))))
    params={owner:'A' for owner in BRANDED};params['foreign']='shared'
    query=case.get('query',GET);groups=[];temp=[]
    for _ in range(2 if case.get('repeat') else 1):
        params['root']='shared'  # Actual startup reset precedes lookup and calls.
        group=[];temp=[]
        if entered and selected not in FALSY:
            if selected not in BRANDED:return dict(ok=False)
            params[selected]=params['root']
            if len(parts)>1:temp.append(selected)
            else:
                wildcard=children[selected].get((42,),'u')
                targets=([wildcard] if wildcard not in FALSY else [])+[selected]
                for target in targets:
                    if target not in BRANDED:return dict(ok=False)
                    for index in rows[target]:
                        if records[index]['method']==query or records[index]['method']==ALL:group.append(index)
        groups.append(group)
    collected=list(itertools.chain.from_iterable(groups))
    matches=[dict(handler=records[index]['handler'],score=records[index]['score'],
        keys=[list(k) for k in records[index]['keys']],
        captures=[dict(key=list(k),value=encode('u')) for k in sorted(records[index]['keys'])]) for index in collected]
    return dict(ok=True,entered=entered,next=encode(selected),node=encode('root' if entered else 'u'),temp=list(map(encode,temp)),
        setup=dict(parts=parts,len=len(parts),part=dict(kind='string',units=parts[0]) if entered else encode('u'),
            isLast=len(parts)==1 if entered else None,i=0 if entered else None,j=0 if entered else None,
            len2=1 if entered else None,offsetsNull=True,fresh=True,oldArraysKept=True),
        matches=matches,collectorSizes=list(map(len,groups)),sameRecords=[[a==b for b in collected] for a in collected],
        sameParams=[[a==b for b in collected] for a in collected],params=[[o,params[o]] for o in OWNERS],
        order=len(records),methodKept=True,nullPrototypes=True)


def registration(method,handler=10,keys=None):
    return dict(method=method,handler=handler,keys=[ID,NAME,ID] if keys is None else keys)


class FirstLiteralTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        for folder in ['search-setup','loop-entry','iteration-setup','literal-branch','class-installation','private-write','methods-push','splitpath','first-literal']:
            result=invoke(['python3',f'verification/{folder}/source.py','--hono',str(HONO)])
            if result.returncode:raise AssertionError(result.stdout+result.stderr)

    def compare(self,cases):
        expected=[oracle(case) for case in cases]
        self.assertEqual(native(dict(cases=cases)),expected)
        self.assertEqual(model(dict(cases=cases)),expected)

    def test_exhaustive_source_startup_aliases_and_rows(self):
        profiles=[[],[registration(GET)],[registration(ALL,11)],
            [registration(POST,10),registration(GET,10),registration(ALL,12)]]
        root_profiles=[[registration(GET,20)],[registration(ALL,21)]]
        cases=[dict(child=child,wildcard=star,root=root,literal=literal,star=wild,query=query,path=path,
                entries=[[ID,'one'],[NAME,'text']])
            for child,star,root,literal,wild,query,path in itertools.product(
                ['u','literal','root'],['u','wildcard','literal','root'],root_profiles,profiles,profiles,[GET,POST,ALL],
                [[47,108,105,116],[47,108,105,116,47,120],[47]])]
        self.compare(cases)
        print(f'First-literal audit: {len(cases)} exhaustive startup/all-four-branch/row/self/shared contexts',flush=True)

    def test_seeded_repeated_raw_collectors_and_reset(self):
        rng=random.Random(161803)
        keys=[ID,NAME,[95,95,112,114,111,116,111,95,95],[55296],[48]]
        codes=FALSY+['t','one','text','root','parent','literal','wildcard','foreign','plain']
        cases=[]
        for _ in range(384):
            regs=lambda:[registration(rng.choice([GET,POST,ALL]),rng.randrange(3),[rng.choice(keys) for _ in range(rng.randrange(5))]) for _ in range(rng.randrange(5))]
            cases.append(dict(path=rng.choice([[],[47],[47,47],[47,108,105,116],[47,120,47,55296],[42],[47,42],
                    [0,47,55296],[47,55296,47]]),child=rng.choice(codes),wildcard=rng.choice(codes),
                root=regs(),literal=regs(),star=regs(),query=rng.choice([GET,POST,ALL,[88]]),repeat=bool(rng.randrange(2)),
                entries=[[key,rng.choice(FALSY+['t','one','text'])] for key in keys],laterEntries=[[key,'text'] for key in keys]))
        cases += [dict(child='root',wildcard='root',root=[registration(GET,7,[ID])]*16,
                       repeat=True,entries=[[ID,'one']],laterEntries=[[ID,'text']]),
                  dict(child='parent',path=[47,108,105,116,47,120],repeat=True),dict(path=[],repeat=True)]
        cases += [dict(entries=[[ID,value]],child=child,wildcard=star,root=[registration(ALL)],
                       literal=[registration(GET)],star=[registration(ALL)],repeat=True)
                  for value,child,star in itertools.product(['u','n','f','z','empty','t','one','text'],['root','literal'],['u','root','wildcard'])]
        cases += [dict(receiver=receiver) for receiver in ['foreign','plain','u','n']]
        self.compare(cases)
        print(f'First-literal audit: {len(cases)} seeded/repeated-retained-collector/UTF16/reset/brand contexts',flush=True)

    def test_supported_source_faults_and_metadata(self):
        startup=(ROOT/'verification/search-setup/startup.ts.txt').read_text()
        entry=(ROOT/'verification/iteration-setup/entry.ts.txt').read_text()
        cases=[dict(child='literal',wildcard='wildcard',literal=[registration(GET,10)],star=[registration(ALL,20)],
                    root=[registration(ALL,30)],entries=[[ID,'one'],[NAME,'text']],repeat=True),
               dict(child='parent',path=[47,108,105,116,47,120],entries=[[ID,'text']]),
               dict(child='root',wildcard='root',root=[registration(GET,7)],entries=[[ID,'one']])]
        star_call="this.#pushHandlerSets(handlerSets, nextNode.#children['*'], method, node.#params)"
        direct_call='this.#pushHandlerSets(handlerSets, nextNode, method, node.#params)'
        swapped=entry.replace(star_call,'__SWAP__').replace(direct_call,star_call).replace('__SWAP__',direct_call)
        variants=[('startupSource',startup.replace('this.#params = emptyParams','this.#params = this.#params')),
            ('startupSource',startup.replace('splitPath(path)',"splitPath('')")),
            ('entrySource',entry.replace('nextNode.#params = node.#params','nextNode.#params = nextNode.#params')),
            ('entrySource',entry.replace('if (isLast)','if (!isLast)')),
            ('entrySource',entry.replace('tempNodes.push(nextNode)','tempNodes.push(node)')),
            ('entrySource',swapped),
            ('entrySource',entry.replace(star_call,direct_call))]
        expected=[oracle(case) for case in cases]
        for key,source in variants:
            self.assertNotEqual(source,startup if key=='startupSource' else entry)
            packet=dict(cases=cases,**{key:source})
            observed=native(packet)
            self.assertEqual(model(packet),observed,source)
            self.assertNotEqual(observed,expected,source)
        control=startup.replace('number[] | null','null | number[]')
        self.assertEqual(native(dict(cases=cases,startupSource=control)),expected)
        self.assertEqual(model(dict(cases=cases,startupSource=control)),expected)

    def test_contiguous_identity_components_and_hidden_edits(self):
        with tempfile.TemporaryDirectory(prefix='hono-first-literal-') as temporary:
            base=Path(temporary);script=base/'verification/first-literal/source.py'
            script.parent.mkdir(parents=True);shutil.copy(ROOT/'verification/first-literal/source.py',script)
            metadata=json.loads((ROOT/'verification/first-literal/source.json').read_text())
            for component in metadata['components']:
                for key in ['sourceMetadata','sourceCopy']:
                    relative=component[key];target=base/relative;target.parent.mkdir(parents=True,exist_ok=True)
                    shutil.copy(ROOT/relative,target)
            command=['python3',str(script),'--hono',str(HONO)]
            self.assertEqual(invoke(command+['--write']).returncode,0)
            self.assertEqual(invoke(command).returncode,0)
            for relative in ['verification/first-literal/source.json','verification/first-literal/full.ts.txt',
                    'HonoLean/Upstream/NodeFirstLiteral/Generated.lean','verification/search-setup/startup.ts.txt',
                    'verification/loop-entry/outer.ts.txt']:
                file=base/relative;saved=file.read_bytes();file.write_bytes(saved+b'\n')
                self.assertNotEqual(invoke(command).returncode,0,relative);file.write_bytes(saved)
            clone=base/'checkout'
            subprocess.run(['git','clone','--shared','--quiet',str(HONO),str(clone)],check=True)
            source='src/router/trie-router/node.ts'
            subprocess.run(['git','-C',str(clone),'update-index','--assume-unchanged',source],check=True)
            file=clone/source;file.write_bytes(file.read_bytes()+b'\n')
            self.assertEqual(subprocess.check_output(['git','-C',str(clone),'status','--porcelain']).strip(),b'')
            self.assertNotEqual(invoke(['python3',str(script),'--hono',str(clone)]).returncode,0)
            self.assertNotEqual(invoke(['bun','verification/first-literal/native.ts',str(clone)],dict(cases=[])).returncode,0)


if __name__=='__main__':unittest.main(argv=['first-literal-tests'])
