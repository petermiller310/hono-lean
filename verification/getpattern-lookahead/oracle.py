"""Independent interval/prefix/assertion contract; never calls either executable."""
def units(text):
    encoded=text.encode('utf-16-le','surrogatepass')
    return [encoded[i]+256*encoded[i+1]for i in range(0,len(encoded),2)]
def source(lower,upper,next_value,display=False):
    return [94,91,lower,45,upper,93,43,40,63,61]+([92]if display else[])+[47]+next_value+[41]
def label(name,lower,upper):return [58]+name+[123,91,lower,45,upper,93,43,125]
def key(input_label,next_value,separator=35):return input_label+[separator]+next_value
def match(lower,upper,next_value,input_value):
    # Independent decomposition at '/', which cannot belong to an admitted
    # range. This does not reproduce the VM's greedy range-scan algorithm.
    try:slash=input_value.index(47)
    except ValueError:return None
    taken=input_value[:slash];remainder=input_value[slash+1:]
    if not taken or not all(lower<=unit<=upper for unit in taken):return None
    if remainder[:len(next_value)]!=next_value:return None
    return dict(values=[taken],index=0,input=input_value,groupsUndefined=True)
def expected(fixture,*,tuple_label=False,tuple_whole_match=False,key_separator=35,assertion_prefix=None):
    lo,hi=fixture['lower'],fixture['upper'];name=fixture['name'];next_value=fixture['next']
    assertion_next=(assertion_prefix or[])+next_value
    last=dict(value=fixture.get('lastIndex',0),writable=fixture.get('writable',True),enumerable=False,configurable=False)
    return dict(ok=True,tuple=[fixture['label']if tuple_label else key(fixture['label'],next_value,key_separator),
                              fixture['label']if tuple_whole_match else name],source=source(lo,hi,assertion_next,True),flags=[],
                ownSource=False,ownFlags=False,prototypeStandard=True,extensible=True,lastIndex=last,
                queries=[dict(value=match(lo,hi,assertion_next,value),lastIndex=last)for value in fixture['queries']],oldFrames=True)
