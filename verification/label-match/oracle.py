"""Independent Hono label decomposition and observable result contract, not a regex evaluator."""
from itertools import product
import random

LINE_TERMINATORS={10,13,8232,8233}
def units(text):
    raw=text.encode('utf-16-le',errors='surrogatepass')
    return [int.from_bytes(raw[i:i+2],'little')for i in range(0,len(raw),2)]

def string(value):return {'kind':'string','units':value}
UNDEFINED={'kind':'undefined'}
def decompose(label):
    if not label or label[0]!=58:return None
    tail=label[1:]
    if not tail:return None
    brace=next((i for i,c in enumerate(tail)if c in (123,125)),None)
    if brace is None:return tail,None
    if brace==0 or tail[brace]!=123 or tail[-1]!=125:return None
    body=tail[brace+1:-1]
    if not body or any(c in LINE_TERMINATORS for c in body):return None
    return tail[:brace],body

def descriptor(value,enumerable=True,configurable=True):
    return dict(kind='data',value=value,writable=True,enumerable=enumerable,configurable=configurable)

def observation(label):
    decoded=decompose(label)
    base=dict(outerPreserved=True,thisPreserved=True,oldFrames=True)
    if decoded is None:return dict(base,result={'kind':'null'},captures=None,view=None,ownNames=None)
    name,body=decoded
    captures=[string(label),string(name),UNDEFINED if body is None else string(body)]
    view={key:descriptor(value)for key,value in zip(['zero','one','two'],captures)}
    view.update(length=descriptor({'kind':'number','value':3},False,False),
                index=descriptor({'kind':'number','value':0}),input=descriptor(string(label)),groups=descriptor(UNDEFINED))
    return dict(base,result={'kind':'array','ref':1},captures=captures,view=view,
                ownNames=['0','1','2','groups','index','input','length'])

def contexts():
    # All short strings over syntax boundaries, an ordinary letter and a line terminator.
    exhaustive=[dict(label=list(label))for n in range(6)for label in product([58,123,125,97,10],repeat=n)]
    names=['id','__proto__','constructor','0','01','4294967295',':','/','\\','#','\x00','\ud800','\udc00','\ud800\udc00','名',
           '\n','\r','\u2028','\u2029','a\nb','a\rb','a\u2028b','a\u2029b','x'*96]
    bodies=['a','[0-9]+','[','(',')','[]','a}{b','{a}','a}}','\x00','\v','\f','\x85','\ud800','\udc00','\ud800\udc00','名',
            '\n','\r','\u2028','\u2029','a\nb','a\rb','a\u2028b','a\u2029b','a'*96,'']
    structured=[]
    for name in names:
        structured.append(dict(label=units(':'+name)))
        for body in bodies:structured.append(dict(label=units(':'+name+'{'+body+'}')))
    malformed=[dict(label=units(s))for s in ['','*','id',':',':{}',':{a}',':id{}',':id{a',':id}a',':id{a}tail',':id{a}\n',
                ':id{a}\r\n',':id{a}\u2028',':id{a}\u2029',':id{a}{b}',':id{a}tail}',':id{{a}}',':id\n',':id{a\nb}']]
    seed=random.Random(20261024)
    alphabet=[0,9,10,11,12,13,35,58,65,91,92,93,97,123,125,133,8232,8233,55296,56320,65535]
    random_cases=[dict(label=[seed.choice(alphabet)for _ in range(seed.randrange(40))])for _ in range(512)]
    # Focus exact boundary units in both syntactic positions; no Unicode normalization.
    boundary_units=[0,1,8,9,10,11,12,13,14,31,32,57,58,59,90,91,92,93,122,123,124,125,126,127,128,133,159,160,
                    255,256,55295,55296,56319,56320,57343,57344,8231,8232,8233,8234,65534,65535]
    unit_cases=[dict(label=label)for c in boundary_units for label in ([58,c],[58,105,100,123,c,125])]
    return dict(exhaustive=exhaustive,structured=structured,malformed=malformed,seeded=random_cases,units=unit_cases)

def pipeline_contexts():
    safe=list(range(48,58))+list(range(65,91))+list(range(97,123))
    cases=[]
    for lower,upper in product(safe,safe):
        if lower<=upper:
            label=[58,105,100,123,91,lower,45,upper,93,43,125]
            for query in [[lower,upper],[]]:cases.append(dict(label=label,input=query))
    for name,query in product(['constructor','__proto__','名','\ud800\x00\udc00','i\nd',':','/','\\'],
                              ['','12','12\n','12\r\n','12\u2028','x','１２','\ud800']):
        cases.append(dict(label=units(':'+name+'{[0-9]+}'),input=units(query)))
    return cases

def pipeline_observation(fixture):
    label,query=fixture['label'],fixture['input']
    decoded=decompose(label);assert decoded is not None
    name,body=decoded
    assert body is not None and len(body)==6 and body[0]==91 and body[2]==45 and body[4:]==[93,43]
    lower,upper=body[1],body[3]
    assert lower<=upper
    base=observation(label)
    hit=bool(query)and all(lower<=c<=upper for c in query)
    view=None
    if hit:
        view=dict(zero=descriptor(string(query)),length=descriptor({'kind':'number','value':1},False,False),
                  index=descriptor({'kind':'number','value':0}),input=descriptor(string(query)),groups=descriptor(UNDEFINED))
    base['pipeline']=dict(produced=dict(tuple={'kind':'array','ref':2},label=string(label),name=string(name),
                                       source=[94]+body+[36],flags=[],lastIndex=descriptor({'kind':'number','value':0},False,False)),
                          name=string(name),matcherSameAsTuple=True,m={'kind':'array','ref':3}if hit else{'kind':'null'},
                          execCaptures=[string(query)]if hit else None,execView=view)
    return base
