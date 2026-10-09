from common import *
fixed()
cs=load(CONTRACT/'canary-stabilized-v1.json')
test=ROOT/cs['targets'][0]['file']
assert load(RUN/'four-numeric-branches-command-v1.json')['actual_exit']==1
assert sha(test)==load(RUN/'decreasing-canary-focused-inspected-v2.json')['canary_sha256']
diag='''import Tests.OnlinePrescientBregmanRegretCanary
import Lean
open Lean Elab Command
partial def peel (e : Expr) : Expr :=
  match e with
  | .letE _ _ v b _ => peel (b.instantiate1 v)
  | .mdata _ b => peel b
  | _ => if e.getAppFn.isConstOf ``id && e.getAppArgs.size == 2 then peel e.getAppArgs[1]! else e
run_cmd do
  let env ← getEnv
  for name in #[`BanditRL.OnlinePrescientBregmanRegretCanary.fixed_signed_run,
      `BanditRL.OnlinePrescientBregmanRegretCanary.decreasing_signed_run] do
    let some (.thmInfo info) := env.find? name | throwError "missing actual theorem value"
    let p := peel info.value
    match p.getAppFn with
    | .const n _ => logInfo m!"{name}: actual peeled root {n}, arguments {p.getAppArgs.size}"
    | _ => throwError "unexpected nonconstant root"
'''
write(RUN/'numeric-spine-diagnostic-v1.lean',diag)
_,out=capture('numeric-spine-diagnostic-command-v1','lake','env','lean',RUN/'numeric-spine-diagnostic-v1.lean')
assert out.count('actual peeled root And.casesOn')==2,out
write(RUN/'pre-numeric-projection-native-exact-v3.json',dict(rows=[dict(path=p.as_posix(),sha256=sha(p),raw_base64=base64.b64encode(p.read_bytes()).decode('ascii')) for p in [RUN/'lifecycle-sessions.jsonl',RUN/'lifecycle-state.json',RUN/'trials.jsonl',RUN/'own-artifact-journal.md'] if p.exists()]))
old=test.read_bytes()
write(RUN/'pre-numeric-projections-v3.lean',old)
s=old.decode('utf8')
changes=[]
for before,base,indices in [
    ('  obtain ⟨hf0, hf1, hs0, hs1, hstrict, _, _, _, h0, h1, h2, _, hD10, hD01, _, _⟩ :=\n    BanditRL.OnlinePrescientBregmanCanary.two_distinct_current_losses\n',
     'BanditRL.OnlinePrescientBregmanCanary.two_distinct_current_losses',
     [('hf0',0),('hf1',1),('hs0',2),('hs1',3),('hstrict',4),('h0',8),('h1',9),('h2',10),('hD10',12),('hD01',13)]),
    ('  obtain ⟨hf0, _, hs0, _, hclosed, hstrict, hdiffAll, hseqOld, _, _, _, _, _, _, _, _⟩ :=\n    fixed_signed_run\n',
     'fixed_signed_run',[('hf0',0),('hs0',2),('hclosed',4),('hstrict',5),('hdiffAll',6),('hseqOld',7)])]:
    assert s.count(before)==1
    after=''.join('  have '+var+' := '+base+'.2'*i+'.1\n' for var,i in indices)
    s=s.replace(before,after)
    changes.append(dict(before=before,after=after))
assert all(t['exact_header'] in s for t in cs['targets'])
test.write_bytes(s.encode('utf8'))
write(RUN/'numeric-projections-source-attempt-v3.lean',test.read_bytes())
write(RUN/'numeric-VALUE-audit-failure-repair-v3.json',dict(prior_actual_exit=1,prior_receipt_sha256=sha(RUN/'four-numeric-branches-command-v1.json'),actual_diagnostic_sha256=sha(RUN/'numeric-spine-diagnostic-command-v1.json'),failure='Both actual compiled proof roots are And.casesOn from destructuring old conjunctions; the deliberately non-normalizing numeric selector cannot reach And.intro without unfolding/eliminating that outer recursor.',repair='Replace only the two old-fact obtain destructurings by exact component projections in local have bindings. Same old facts, actual algorithm and numeric proof transports; no theorem unfolding/proof-irrelevance normalization in audit, no header or production mutation.',exact_replacements=changes,production_sha256=sha(PUBLIC)))
code,out=capture('two-canaries-projection-focused-build-v3','lake','build','Tests.OnlinePrescientBregmanRegretCanary',required=False)
passed=code==0 and 'Built Tests.OnlinePrescientBregmanRegretCanary' in out and 'Build completed successfully' in out
write(RUN/'two-canaries-projection-focused-inspected-v3.json',dict(actual_exit=code,compiled=passed,canary_sha256=sha(test),production_sha256=sha(PUBLIC),full_conjunctions=2,frozen_headers_unchanged=True,numeric_VALUE_audit='pending v2 rerun',source_container_closed=False,whole_Goal_status='ACTIVE'))
if not passed:
    print(out[-6000:])
    event('native-canary-projection-repair-v3','repair',dict(actual_exit=code,frozen_headers_unchanged=True,evidence='two-canaries-projection-focused-build-v3.json'))
fixed()
assert passed
audit=(RUN/'canary-public-VALUE-audit-v1.py').read_text(encoding='utf8').replace('-v1','-v2')
for key in ['stabilized','canary-stabilized','fixed-canary-fence','decreasing-canary-fence']:
    audit=audit.replace(key+'-v2.json',key+'-v1.json')
audit=audit.replace("parent = ROOT/'runs/online-ch2-prescient-causal-20261009/export-selected-dependencies-v2.lean'","parent = ROOT/'runs/online-ch2-prescient-causal-20261009/export-selected-dependencies-v1.lean'")
audit=audit.replace('decreasing-canary-focused-inspected-v2.json','two-canaries-projection-focused-inspected-v3.json')
write(RUN/'canary-public-VALUE-audit-v2.py',audit)
print('Both frozen canary bodies compiled with equivalent exact projections; v2 public/numeric audit prepared, not yet run.')
