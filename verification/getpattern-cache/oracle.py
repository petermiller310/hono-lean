"""Independent label/key/descriptor/cache-history contract; no source interpreter."""
import copy
import importlib.util
from pathlib import Path
spec=importlib.util.spec_from_file_location('label_oracle',Path(__file__).resolve().parents[1]/'label-match/oracle.py')
label_oracle=importlib.util.module_from_spec(spec);spec.loader.exec_module(label_oracle)
units=label_oracle.units;decompose=label_oracle.decompose
U={'kind':'undefined'}
def string(value):return {'kind':'string','units':value}
def ref(value):return {'kind':'reference','id':value}
def normalize_value(value):
 if value['kind']=='array':return ref(['a0','a1'][value['ref']])
 if value['kind']=='object':return ref(['caller','oldRegex','cache','parent'][value['ref']])
 if value['kind']=='function':return ref('RegExp'if value['ref']==6 else'f'+str(value['ref']))
 return copy.deepcopy(value)
def truthy(value):
 k=value['kind']
 return False if k in ['undefined','null']else bool(value['value'])if k in ['number','bool']else bool(value['units'])if k=='string'else True

def primitive_text(value):
 k=value['kind']
 if k=='string':return value['units']
 if k in ['undefined','null']:return units(k)
 if k=='bool':return units('true'if value['value']else'false')
 if k=='number'and abs(value['value'])<=9007199254740991:return units(str(value['value']))
 raise ValueError('Outside primitive ToString model domain')
def key(label,next_value):return label+[35]+primitive_text(next_value)
def desc(value,writable=True,enumerable=True,configurable=True):
 return dict(kind='data',value=value,writable=writable,enumerable=enumerable,configurable=configurable)
def fields(items):
 return {tuple(f['key']):desc(normalize_value(f['value']),f.get('writable',True),f.get('enumerable',True),f.get('configurable',True))for f in items}

def history(fixture,block=False):
 own=fields(fixture.get('seed',[]));parent=fields(fixture.get('inherited',[]));extensible=fixture.get('extensible',True)
 graph=[];observations=[]
 for step in fixture['steps']:
  label=step['label'];next_value=step.get('next',U)
  matched=None if block else decompose(label)
  if not block and matched is None:value={'kind':'null'}
  else:
   cache_key=tuple(key(label,next_value))
   if fixture.get('cacheKind')=='undefined':observations.append({'ok':False});break
   current=own.get(cache_key,parent.get(cache_key));current_value=U if current is None else current['value']
   if truthy(current_value):value=current_value
   else:
    if block:raise ValueError('Cold block-only matching fixture needs separate capture contract')
    name,body=matched
    route_matcher={'kind':'bool','value':True}
    if body is not None:
     # This is the independent safe-interval contract, not a regex engine.
     safe=lambda c:48<=c<=57 or 65<=c<=90 or 97<=c<=122
     if len(body)!=6 or body[0]!=91 or body[2]!=45 or body[4:]!=[93,43]or not safe(body[1])or not safe(body[3])or body[1]>body[3]:
      raise ValueError('Unsupported cold regexp body; retain as native-only frontier')
     if truthy(next_value)and(next_value['kind']!='string'or next_value['units'][0]not in [58,42]):
      raise ValueError('Reached lookahead; no fake supported result')
     if fixture.get('constructorKind')=='number':observations.append({'ok':False});break
     route_matcher=ref('r'+str(sum(g['kind']=='array'for g in graph))+'.regex')
    # The RHS exists before Set, but failure exposes no partial-state claim.
    if current is not None and not current['writable']or cache_key not in own and not extensible:
     observations.append({'ok':False});break
    identity='r'+str(sum(g['kind']=='array'for g in graph));value=ref(identity)
    graph.append(dict(id=identity,kind='array',values=[string(label),string(name),route_matcher]))
    if body is not None:
     graph.append(dict(id=identity+'.regex',kind='regexp',source=[94]+body+[36],flags=[],lastIndex=desc({'kind':'number','value':0},True,False,False)))
    if cache_key in own:own[cache_key]['value']=value
    else:own[cache_key]=desc(value)
  cache=dict(own=[dict(key=list(k),**own[k])for k in sorted(own)],prototype='parent'if parent else'Object.prototype',extensible=extensible)
  observations.append(dict(ok=True,value=copy.deepcopy(value),cache=copy.deepcopy(cache),visibleGraph=copy.deepcopy(graph),oldFrames=True))
 return observations
