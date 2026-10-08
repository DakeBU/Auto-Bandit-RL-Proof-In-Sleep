from common_reviewed_v2 import *
import re

headers_fixed(7)
targets=load(CONTRACT/'targets-v2.json')['rows']
neutral=(CONTRACT/'neutral-context-v2.lean').read_text(encoding='utf8')
draft=(RUN/'draft-types-and-API-v2.lean').read_text(encoding='utf8')
draft_types=draft.split('namespace DraftSeed\n',1)[1].split('end DraftSeed',1)[0]
text='import BanditRLProof.OnlineGuessingRandomizedIID\n'+neutral
text+='\nopen BanditRL.OnlineLearning\nnamespace ActualDraftTypes\n'+draft_types+'\nend ActualDraftTypes\n'
for i,row in enumerate(targets,1):
    universes='u, v, w, z' if i==1 else 'u, v'
    q='Q'+str(i).zfill(3)+'.{'+universes+'}'
    text+='\nexample : ActualDraftTypes.'+q+' = NeutralSeed.'+q+' := rfl\n'
    text+='example : ActualDraftTypes.'+q+' := by exact @'+row['name']+'\n'
for public,neutral_name,universes in [('expectedFixedMinimum','C0','u'),('expectedFixedRegret','C1','u'),
        ('privateSeedPastInformation','C2','u, v')]:
    text+='\nexample : @'+public+'.{'+universes+'} = @NeutralSeed.'+neutral_name+'.{'+universes+'} := rfl\n'
names=[r['name'] for r in targets]+[PRE+'privateSeedPastInformation',PRE+'expectedFixedMinimum',PRE+'expectedFixedRegret',
    PRE+'expectedFixedMinimum_eq_variance',PRE+'iid_cumulative_prediction_decomposition',PRE+'independent_prediction_square',
    'ProbabilityTheory.iIndepFun.indepFun_finset','ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map',
    'MeasureTheory.Measure.prodAssoc_prod','ProbabilityTheory.indep_of_indep_of_le_left']
for name in names:
    text+='\n#check '+name+'\n#print axioms '+name+'\n'
write(RUN/'leaves'/'actual-public-types-kernel-v2.lean',text)
gate('actual-public-types-kernel-v2','lake','env','lean',RUN/'leaves'/'actual-public-types-kernel-v2.lean')
log=(RUN/'actual-public-types-kernel-v2.log').read_text(encoding='utf8')
assert 'sorryAx' not in log
axioms=set()
for value in re.findall(r'depends on axioms: \[([^\]]*)\]',log):
    axioms.update(x.strip() for x in value.split(',') if x.strip())
assert axioms<=set(['propext','Classical.choice','Quot.sound']),axioms
write(RUN/'actual-public-type-kernel-audit-v2.json',dict(actual_lean_exit=0,
    frozen_public_proof_type_instantiations=7, arbitrary_universe_draft_neutral_identities=7,
    whole_definition_identities=3,named_checks_and_axioms=len(names),actual_axioms=sorted(axioms),sorryAx=False,
    public_sha256=sha(PUBLIC),target_headers_sha256=sha(CONTRACT/'targets-v2.json'),
    combined_root_Tests_harness_pending=True,semantic_BODY_pending=True,
    chapter_complete=False,goal_complete=False))
headers_fixed(7)
print('Actual 7 universal public proof types /7 identities /3 whole definitions /17 named kernel checks passed.')
