"""Independent argument/metadata/live-binding/cache contract, no source evaluator."""
import copy
import importlib.util
from pathlib import Path

spec=importlib.util.spec_from_file_location('cache_contract',Path(__file__).resolve().parents[1]/'getpattern-cache/oracle.py')
cache=importlib.util.module_from_spec(spec);spec.loader.exec_module(cache)
U,string,units,key=cache.U,cache.string,cache.units,cache.key
METADATA=dict(name=dict(value='getPattern',writable=False,enumerable=False,configurable=True),
              length=dict(value=2,writable=False,enumerable=False,configurable=True),ownPrototype=False,functionPrototype=True)

def history(fixture):
    own=cache.fields(fixture.get('seed',[]));parent=cache.fields(fixture.get('inherited',[]))
    extensible=fixture.get('extensible',True);graph=[];observations=[];constructor='builtin'
    for step in fixture['steps']:
        constructor=step.get('constructorKind',constructor)
        arguments=step.get('arguments',[string(step.get('label',[])),step.get('next',U)])
        label_value=arguments[0]if arguments else U
        next_value=arguments[1]if len(arguments)>1 else U
        if label_value['kind']!='string':observations.append(dict(ok=False));break
        label=label_value['units'];matched=cache.decompose(label)
        if label==[42]:value=string([42])
        elif matched is None:value=dict(kind='null')
        else:
            cache_key=tuple(key(label,next_value));current=own.get(cache_key,parent.get(cache_key))
            current_value=U if current is None else current['value']
            if cache.truthy(current_value):value=current_value
            else:
                name,body=matched;route_matcher=dict(kind='bool',value=True)
                if body is not None:
                    safe=lambda c:48<=c<=57 or 65<=c<=90 or 97<=c<=122
                    if len(body)!=6 or body[0]!=91 or body[2]!=45 or body[4:]!=[93,43]or not safe(body[1])or not safe(body[3])or body[1]>body[3]:
                        raise ValueError('Unsupported cold body; no fabricated regex result')
                    if cache.truthy(next_value)and(next_value['kind']!='string'or next_value['units'][0]not in [58,42]):
                        raise ValueError('Reached lookahead remains a separate frontier')
                    if constructor=='number':observations.append(dict(ok=False));break
                    route_matcher=cache.ref('r'+str(sum(g['kind']=='array'for g in graph))+'.regex')
                if current is not None and not current['writable']or cache_key not in own and not extensible:
                    observations.append(dict(ok=False));break
                identity='r'+str(sum(g['kind']=='array'for g in graph));value=cache.ref(identity)
                graph.append(dict(id=identity,kind='array',values=[string(label),string(name),route_matcher]))
                if body is not None:graph.append(dict(id=identity+'.regex',kind='regexp',source=[94]+body+[36],flags=[],
                    lastIndex=cache.desc(dict(kind='number',value=0),True,False,False)))
                if cache_key in own:own[cache_key]['value']=value
                else:own[cache_key]=cache.desc(value)
        view=dict(own=[dict(key=list(k),**own[k])for k in sorted(own)],
                  prototype='parent'if parent else'Object.prototype',extensible=extensible)
        observations.append(dict(ok=True,value=copy.deepcopy(value),cache=copy.deepcopy(view),visibleGraph=copy.deepcopy(graph),oldFrames=True))
    return dict(metadata=copy.deepcopy(METADATA),nonConstructible=True,sameExport=True,sameCache=True,observations=observations)
