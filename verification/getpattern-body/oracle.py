"""Independent wildcard/no-effect rule composed with the frozen cache contract."""
import copy
import importlib.util
from pathlib import Path

spec=importlib.util.spec_from_file_location('cache_reference',Path(__file__).resolve().parents[1]/'getpattern-cache/oracle.py')
cache=importlib.util.module_from_spec(spec);spec.loader.exec_module(cache)
U,string,units,key=cache.U,cache.string,cache.units,cache.key

def history(fixture):
    # A wildcard step has no cache/graph effect. Compute the independent cache
    # history once for all other steps, then insert the skipped observations.
    reduced=copy.deepcopy(fixture)
    reduced['steps']=[step for step in fixture['steps']if step['label']!=[42]]
    normal=iter(cache.history(reduced))
    own=cache.fields(fixture.get('seed',[]))
    current=dict(own=[dict(key=list(k),**own[k])for k in sorted(own)],
                 prototype='parent'if fixture.get('inherited')else'Object.prototype',extensible=fixture.get('extensible',True))
    graph=[];result=[]
    for step in fixture['steps']:
        if step['label']==[42]:
            result.append(dict(ok=True,value=string([42]),cache=copy.deepcopy(current),visibleGraph=copy.deepcopy(graph),oldFrames=True))
        else:
            value=next(normal);result.append(value)
            if not value['ok']:break
            current=value['cache'];graph=value['visibleGraph']
    return result
