from common import *
import ast
sys.path.insert(0,str(ROOT))
from tools.abrl_lifecycle import lean_declaration_header,statement_hash
public=ROOT/'Tests/OnlineAdaptiveOSDCanary.lean'
assert public.read_bytes()==(RUN/'algorithm-canary-zero_energy_canary-body-attempt-v1.lean.txt').read_bytes()
headers=load(CONTRACT/'algorithm-canary-stabilized-v1.json')['exact_headers']
s=public.read_text(encoding='utf8')
s=s.replace('  have hf : ∀ t : ℕ, BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (zeroLoss t) := by','  have hz (t : ℕ) : loss 0 = zeroLoss t := by\n    funext z\n    norm_num [loss, feedback, zeroLoss]\n  have hf : ∀ t : ℕ, BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (zeroLoss t) := by')
s=s.replace('simpa [loss, feedback, zeroLoss] using (loss_regular V 0).2.1','simpa only [hz t] using (loss_regular V 0).2.1')
s=s.replace('simpa [feedback, loss, zeroLoss] using (loss_regular V 0).2.2','simpa only [hz t, feedback, show (0 : ℕ) ≠ 1 by norm_num, show (0 : ℕ) ≠ 3 by norm_num, if_false] using (loss_regular V 0).2.2')
s=s.replace('  · simpa [he] using hp','  · rw [he] at hp\n    simpa using hp')
write(RUN/'algorithm-canary-zero-energy-repair-route-v2.json',dict(classification='Function-valued loss requires explicit extensional equality; rewrite energy before half normalization',frozen_headers_unchanged=True,failure_receipt=rows([RUN/'algorithm-canary-zero_energy_canary-focused-build-v1.json'])))
public.write_bytes(s.encode())
assert statement_hash(lean_declaration_header(public,'zero_energy_canary'))==headers['zero_energy_canary']['normalized_statement_hash']
write(RUN/'algorithm-canary-zero_energy_canary-body-attempt-v2.lean.txt',public.read_bytes())
code,out=capture('algorithm-canary-zero_energy_canary-focused-build-v2','lake','build','Tests.OnlineAdaptiveOSDCanary',required=False)
print(out[-3200:] if code else out.splitlines()[-1],flush=True)
if code: sys.exit(code)
write(RUN/'algorithm-canary-zero_energy_canary-compiled-local-v2.json',dict(production_sha256=sha(public),boundary='focused only'))
tree=ast.parse((RUN/'prove-algorithm-canary-v1.py').read_text(encoding='utf8'))
bodies=next(ast.literal_eval(n.value) for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='bodies' for t in n.targets))
name='zero_diameter_canary'
event('algorithm-canary-'+name+'-proving-event-v1','proving',dict(current_leaf=name,allowed_file=public.as_posix()))
public.write_bytes(public.read_bytes().rsplit(b'end AdaptiveProbe\n',1)[0]+b'\n'+Path(headers[name]['path']).read_bytes()+bodies[name].encode()+b'end AdaptiveProbe\n')
assert statement_hash(lean_declaration_header(public,name))==headers[name]['normalized_statement_hash']
write(RUN/('algorithm-canary-'+name+'-body-attempt-v1.lean.txt'),public.read_bytes())
code,out=capture('algorithm-canary-'+name+'-focused-build-v1','lake','build','Tests.OnlineAdaptiveOSDCanary',required=False)
print(out[-3200:] if code else out.splitlines()[-1],flush=True)
if code: sys.exit(code)
write(RUN/('algorithm-canary-'+name+'-compiled-local-v1.json'),dict(production_sha256=sha(public),boundary='focused only'))
