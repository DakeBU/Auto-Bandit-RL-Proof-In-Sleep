"""Preserve actual first focused failure; make the canary's subset type explicit."""
from common_v1 import *
fixed(False,True);assert load(RUN/'public-canary-focused-v1-01-exit.json')['exit_code']==1
for p in [PUBLIC,CANARY]:write(RUN/'leaves'/('focused-failed-v1-'+p.name),p.read_bytes())
text=CANARY.read_text(encoding='utf-8')
old='''  exact Set.Countable.mono
    (fun x hx => ⟨hx, convex_nondifferentiable_segment.2 x hx⟩) hc'''
new='''  have hsub : segment ℝ (0 : Plane) (PiLp.single 2 1 1) ⊆
      segment ℝ (0 : Plane) (PiLp.single 2 1 1) ∩
        {x : Plane | ¬ DifferentiableAt ℝ coordinateAbsolute x} := by
    intro x hx
    exact ⟨hx, convex_nondifferentiable_segment.2 x hx⟩
  exact Set.Countable.mono hsub hc'''
assert old in text;CANARY.write_bytes(text.replace(old,new).encode())
text=PUBLIC.read_text(encoding='utf-8');assert 'simp [PiLp.single_apply]' in text
PUBLIC.write_bytes(text.replace('simp [PiLp.single_apply]','simp').encode());fixed(False,True)
write(RUN/'focused-repair-v2.json',dict(failed_attempt='public-canary-focused-v1-01',actual_public_job_compiled=True,whole_focused_command_failed=True,error_signature='Canary subset-pair expected type could not be determined',repair='Annotate actual source-segment-to-intersection subset before invoking existing Countable.mono; remove an unused public simp argument.',source_headers_unchanged=True,canary_statements_unchanged=True,source_contract_unchanged=True,proof_route_unchanged=True,original_failed_bodies_preserved=True,mathematical_target_repairs=[]))
native('failed-focused-trial-v1','trial-log','--task',TASK,'--role','lower','--kind','attempt','--status','failed','--run-id',RUN.name,'--attempt-id','UNCOUNTABLE-BODY-V1','--statement-hash',load(CONTRACT/'native-statement-fingerprints-v1.json')['convex_uncountable_nondifferentiability'],'--verifier-evidence',RUN/'public-canary-focused-v1-01.log','--harness','hierarchical','--progress-class','no-progress','--error-signature','Canary subset-pair expected type could not be determined','--notes','Actual public module job compiled, combined focused gate failed on canary elaboration; explicit same-subset annotation repair, all source/header/test statements fixed. No accepted proof progress claimed from failed command.')
event('repair',dict(failed_attempt='UNCOUNTABLE-BODY-V1',repair=(RUN/'focused-repair-v2.json').as_posix(),targets_unchanged=True),attempt='body-v2')
print('Actual first focused failure preserved; same-target canary annotation repair only.')
