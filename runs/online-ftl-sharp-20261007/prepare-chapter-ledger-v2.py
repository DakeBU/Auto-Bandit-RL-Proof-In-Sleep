from common_v1 import *
fixed()
old=Path('docs/contracts/online-foundations-public-v1/chapter-one-source-ledger-draft-v1.json');d=load(old)
assert len(d['maintext_items'])==14
d['prior_ledger']=dict(path=old.as_posix(),sha256=sha(old),original_unchanged=True)
d['enumeration_status']='Candidate15 maintext items; new explicit refined regret bound split from stability. Chapter-wide enumeration review requested separately; no mathematical or chapter acceptance.'
for x in d['maintext_items']:
 if x['source_id']=='C1-STABILITY':
  x['lean_names'].append(PRE+'meanPredict_initial_stability')
  x['current_status']='Exact two source stability obligations: existing later4/t API; frozen sharp initial1/4 target pending current CONTRACT/proof/BODY/FINAL gates'
d['maintext_items'].insert(next(i for i,x in enumerate(d['maintext_items']) if x['source_id']=='C1-HARMONIC'),dict(source_id='C1-REFINED-REGRET',printed_page=5,pdf_page=17,kind='unnumbered main performance bound',required_maintext=True,target_intent='Actual causal FTL best-fixed interval regret <=0.25+4 sum(source t=2..T)1/t, with positive horizon, targets in[0,1] and empiricalMean as produced feasible minimizer',lean_names=[PRE+'meanPredict_regret_refined'],current_status='Exact frozen new public target pending CONTRACT/proof/BODY/FINAL/integration gates',evidence_permission='No completion from closed Prop type, interface presence or historical source coverage'))
d.update(candidate_maintext_item_count=15,chapter_mandatory_proof_total=None,source_package_accepted=False,chapter_complete=False,goal_complete=False)
write(CONTRACT/'chapter-one-source-ledger-draft-v2.json',d)
program=dict(goal='Orabona v10 Chapters1-16 ACTIVE/unbudgeted',current_chapter=1,source_sha256=PDF_SHA,chapters=[dict(chapter=n,status='candidate15 maintext items; wholechapter source enumeration review requested; proof/interface gates outstanding' if n==1 else 'partial, mandatorytotal null/incomplete' if n==2 else 'unenumerated mandatory',mandatory_total=None,complete=False) for n in range(1,17)],appendices='Required by maintext dependencies, not yet fully enumerated',history_and_standalone_exercises='Separate optional/planned; formal maintext results cannot be excluded even if proof left as exercise',past_fixed_OGD='Historical bounded delivery only, not chapter completion',chapter_complete=False,goal_complete=False)
write(RUN/'whole-program-obligations-draft-v2.json',program)
write(RUN/'chapter-ledger-version-v2.json',dict(status='Explicit refined unnumbered maintext obligation added; old ledger immutable',old_item_count=14,new_candidate_item_count=15,new_source_ID='C1-REFINED-REGRET',chapter_wide_enumeration_verdict='pending distinct source reviewer',no_chapter_acceptance=True,no_excluded_required_result=True))
fixed();print('Candidate15 Chapter1 maintext items; independent enumeration review pending, proof totals still unknown.')
