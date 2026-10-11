from common import *
import ast
sys.path.insert(0,str(ROOT))
from tools.abrl_lifecycle import lean_declaration_header,statement_hash
public=ROOT/'Tests/OnlineAdaptiveOSDCanary.lean'
assert public.read_bytes()==(RUN/'algorithm-canary-performance_canary-body-attempt-v2.lean.txt').read_bytes()
assert load(RUN/'algorithm-canary-performance_canary-focused-build-v2.json')['actual_exit']==0
headers=load(CONTRACT/'algorithm-canary-stabilized-v1.json')['exact_headers']
tree=ast.parse((RUN/'prove-algorithm-canary-v1.py').read_text(encoding='utf8'))
bodies=next(ast.literal_eval(n.value) for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='bodies' for t in n.targets))
for name in ['prefix_canary','zero_energy_canary','zero_diameter_canary']:
    event('algorithm-canary-'+name+'-proving-event-v1','proving',dict(current_leaf=name,allowed_file=public.as_posix(),boundary='Frozen approved remaining BODY; independent review pending'))
    prefix=public.read_bytes().rsplit(b'end AdaptiveProbe\n',1)[0]
    public.write_bytes(prefix+b'\n'+Path(headers[name]['path']).read_bytes()+bodies[name].encode()+b'end AdaptiveProbe\n')
    assert statement_hash(lean_declaration_header(public,name))==headers[name]['normalized_statement_hash']
    write(RUN/('algorithm-canary-'+name+'-body-attempt-v1.lean.txt'),public.read_bytes())
    code,out=capture('algorithm-canary-'+name+'-focused-build-v1','lake','build','Tests.OnlineAdaptiveOSDCanary',required=False)
    print(out[-3500:] if code else '\n'.join(out.splitlines()[-7:]),flush=True)
    if code: sys.exit(code)
    write(RUN/('algorithm-canary-'+name+'-compiled-local-v1.json'),dict(production_sha256=sha(public),header=headers[name],boundary='focused only'))
