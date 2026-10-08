from common_v1 import *
fixed()
for extension in ['txt','png']:
    src=Path('runs/online-ftl-sharp-20261007')/f'source-pdf17-v1.{extension}'
    write(RUN/src.name,src.read_bytes())
public=(CONTRACT/'public-context-v1.lean').read_text(encoding='utf8')
neutral=(CONTRACT/'neutral-context-v1.lean').read_text(encoding='utf8')
draft=(RUN/'draft-types-v1.lean').read_text(encoding='utf8')
imports=[line for line in public.splitlines() if line.startswith('import ')]
context='\n'.join(line for line in public.splitlines() if not line.startswith('import '))
neutral='\n'.join(line for line in neutral.splitlines() if not line.startswith('import '))
start=draft.index('namespace DraftMinimum')
end=draft.index('end DraftMinimum')+len('end DraftMinimum')
types=draft[start:end]
identities=['example : NeutralMinimum.Q'+str(n).zfill(3)+' = DraftMinimum.Q'+str(n).zfill(3)+' := by rfl' for n in range(1,7)]
definitions=['example : NeutralMinimum.C0 = empiricalMean := by rfl',
 'example : NeutralMinimum.C1 = meanPredict := by rfl',
 'example : NeutralMinimum.C2 = comparatorRegret (X := ℝ) := by rfl',
 'example : NeutralMinimum.C3 = squaredBestRegret := by rfl']
write(RUN/'draft-neutral-identities-v1.lean','import Mathlib\n'+'\n'.join(imports)+'\n'+context+'\n'+neutral+'\nopen BanditRL.OnlineLearning\n'+types+'\n'+'\n'.join(identities+definitions))
gate('actual-draft-neutral-identities-v1','lake','env','lean',RUN/'draft-neutral-identities-v1.lean')
write(RUN/'draft-type-verification-v1.json',dict(status='actual type/definition identity compilation passed',
    public_six_closed_Prop_types_compiled=True,neutral_six_closed_Prop_types_compiled=True,
    six_actual_neutral_Prop_equalities_compiled=True,four_whole_definition_equalities_compiled=True,
    target_theorem_bodies_not_present=True,target_Lean_gate_not_claimed=True,
    exact_targets_sha256=sha(CONTRACT/'targets-v1.json'),exact_public_context_sha256=sha(CONTRACT/'public-context-v1.lean'),
    exact_neutral_context_sha256=sha(CONTRACT/'neutral-context-v1.lean'),source_package_accepted=False,chapter_complete=False,goal_complete=False))
fixed();print('Six actual closed Prop identities and four whole definitions compile; no target body exists yet.')
