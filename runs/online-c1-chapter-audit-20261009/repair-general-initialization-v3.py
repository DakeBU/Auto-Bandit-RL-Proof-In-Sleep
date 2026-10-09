from common_v1 import *
sys.path.insert(0,str(ROOT))
from tools.abrl_lifecycle import statement_hash
import re
fixed()
r=load(RUN/'source-contract-receipt-v1.json');assert r['verdict']=='rejected' and r['inputs_unchanged'] and r['fixed_input_count']==103
assert sha(RUN/'source-contract-review-v1.md')=='429637779fe9985fbf9bb31cae7081f6826c4b20fc20705cf10c39183a29d9bd'
assert sha(RUN/'source-contract-receipt-v1.json')=='a737201379785365661e8f57d69fb4f752366e3125982f1f5f8b40cefef61ade'
for row in load(RUN/'source-contract-review-inputs-v1.json')['rows']:assert sha(row['path'])==row['sha256']
old=load(CONTRACT/'general-initialization-targets-draft-v2.json');new=[]
for t in old['new_targets']:
    v=dict(t)
    if t['id']=='G002':
        v['name']='BanditRL.OnlineLearning.ftlPredict_bestRegret_refined'
        v['conclusion']='''squaredBestRegret y (ftlPredict initial y) T ≤
      (1 : ℝ) + ∑ t ∈ Finset.range (T - 1), 4 / ((t : ℝ) + 2)'''
        v['header']='theorem ftlPredict_bestRegret_refined '+v['binders']+' :\n    '+v['conclusion']
        v['statement_hash']=statement_hash(v['header'])
        v['previous_draft_hash']=t['statement_hash']
        v['change_reason']='Explicit source-review-required exact finite1+tail terminal; prior loose5+log draft retained, never stabilized/proved.'
    v['phase']='draft v3 source-required repair; stabilization pending'
    new.append(v)
assert [t['statement_hash'] for t in new if t['id']!='G002']==[t['statement_hash'] for t in old['new_targets'] if t['id']!='G002']
write(CONTRACT/'general-initialization-targets-draft-v3.json',dict(version=3,phase='draft',new_targets=new,owning_public_path='BanditRLProof/OnlineFTLInitializationRegret.lean',old_fifty_statement_hashes_unchanged=True,
    source_review_required_finite_and_upper_terminal_preserved=True,new_source_object_count=1,new_production_proof_targets=4,required_fullchapter_source_audit_objects=17,unknown_proof_total=None,chapter_complete=False,goal_complete=False))
write(CONTRACT/'general-initialization-targets-draft-v3.lean.txt','\n\n'.join(x['header'] for x in new))
write(CONTRACT/'general-initialization-neutral-targets-v3.lean.txt','\n\n'.join(re.sub(r'^theorem\s+\w+','theorem '+x['id'],x['header']) for x in new))
write(CONTRACT/'general-initialization-intent-draft-v4.md','''Version3 mathematical target repair follows actual rejected chapter contractv1 G1/G2. Preserve the original source/50 headers and all earlier draft/review/failed evidence. G001 exact positive-prefix first-round true-best regret correction remains unchanged (all real initial/observations; same ftlPredict as public state). G002 now freezes reviewer-required exact general-unit-initial finite terminal1+sum_{t in range(T-1)}4/(t+2), replacing the unstabilized loose5+4lnT draft; old drafttype/decode remain as old evidence, not a scope waiver. This uses the existing actual half refined1/4+tail plus exact correction and produces1/4+first-loss-difference<=1 from two legal unit points; or uses actual Lemma1.2/empirical-minimum/laterstability with direct initial<=1. Source positiveT/indexdenominators and initial1 retained; universal1/4 is false. G003 unchanged: same actual predictor and every fixed interval comparator have upper-epsilon NoRegret, no ordinary-limit oracle. Its analytic vanishing upper may use a derived loose5+4lnT from exact finite first-round correction plus half finite bound; this proof estimate is separate from G002 terminal and no printedconstant claim. G004 unchanged: ordinary zero normalized TRUE-best regret comes from the actual G001 fixed finite correction/T and existing half best-average0. It supplies no finite ordinary fixed-comparator limit. Fixed initial chosen before same whole run, not selected by T/comparator/future; no expectation/IID assumptions or supplied regret/stability. Existing any-init state/prefix/feasibility proofs are actual algorithm dependencies. Four derived targets close one additional required source object, not four printed results; original16 untouched, currentaudit17/prooftotalnull/fullgatespending. One new module in the same BanditRLProof library, not a perBook project or changed old proof/predicate. Distinct statement/source review and proving required before any body is written; v1 source rejection preserved.''')
m=load(CONTRACT/'chapter-one-source-map-draft-v1.json')
addition=dict(source_id='C1-FTL-ANY-INITIAL-GUARANTEE',printed_page=3,pdf_page=15,kind='required unnumbered algorithm performance guarantee',required_maintext=True,
    source_intent='Any unit initial FTL family followed by promise the same strategy wins; specialize printed Theorem1.3 half separately.',
    source_review_required_terminals=['same ftlPredict, initialunit, positiveT and bounded scoredprefix: truebestR<=1+sum(range(T-1),4/(t+2))','same all-time unitstream/initial: upper-epsilon NoRegret for every fixed unitcomparator'],
    lean_names=[t['name'] for t in new],state='draft-required-unproved',evidence=str(RUN/'source-contract-receipt-v1.json'),source_result_count=1,new_target_count=4)
write(CONTRACT/'chapter-one-source-map-draft-v3.json',dict(version=3,phase='draft repair',original16_source_objects_preserved_verbatim=m['original16_source_objects_preserved_verbatim'],prior_current_mapping_preserved=m['current_mapping'],additional_required_source_objects=[addition],required_source_audit_object_count=17,unknown_required_proof_total=None,no_maintext_result_excluded=True,
    review_of_old_fifty=r['source_decisions'],all_previous_v1_input_hashes_unchanged=True,source_reconciliation_is_not_proof_of_false_ordinary_limit=True,chapter_complete=False,goal_complete=False))
write(CONTRACT/'general-initialization-DAG-v3.json',dict(kind='semantic prerequisite overlay; compiled VALUE graph later separate',single_lower_route=True,
    edges=[['existing exact ftlPredict/ftlState/strictpast representation','G001'],['G001','G002'],['meanPredict_bestRegret_refined','G002'],['G001','G003'],['meanPredict_bestRegret_bound','G003'],['comparatorRegret_le_squaredBestRegret','G003'],['noRegret_of_vanishing_bound','G003'],['G001','G004'],['meanPredict_bestRegret_average_tendsto_zero','G004'],['G002','C1-FTL-ANY-INITIAL-GUARANTEE'],['G003','C1-FTL-ANY-INITIAL-GUARANTEE']],
    first_dependency_ready_leaf='G001',exact_positive_prefix_first_round_identity=True,terminal_edit_allowed=False))
write(RUN/'general-initialization-neutral-inputs-v3.json',dict(rows=rows([CONTRACT/'general-initialization-neutral-targets-v3.lean.txt',CONTRACT/'general-initialization-neutral-context-v2.lean.txt']),target_count=4,context_definitions=6,source_identity_or_proof_or_prior_verdict_included=False,prior_report_hash=sha(RUN/'general-initialization-blind-reconstruction-v2.md'),prior_receipt_hash=sha(RUN/'general-initialization-blind-receipt-v2.json')))
write(RUN/'general-initialization-neutral-packet-v3.md','''Read ONLY thispacket, general-initialization-neutral-inputs-v3.json/twoinputs and your own previous4target v2 report/receipt. G001/G003/G004 unchanged; G002 now has the exact positiveT1+sum(range(T-1),4/(t+2)) conclusion. New finite type, not a proof or silent correction of previous input. Give COMPLETE4 natural prose/LaTeX/seven slots, especially changed finite constant/index/initial range and unchanged absence of causal/performance premises vs actual definitions. No source/identity/intent/old source-review/proof consultation. Output ONLY general-initialization-blind-reconstruction-v3.md/receipt-v3.json with all2 RAWinputs/packet/index beforeafter and oldv2output binding. Four complete reconstructions, remainingambiguities, reusedhistory/requestedAstramedium/no runtime/human/external/absolute-blind attestation. Oldall50+old4/v2 files remain untouched; no source/proof/chapter verdict.''')
write(RUN/'general-initialization-draft-typecheck-v3.lean','import BanditRLProof\n\nopen Filter BanditRL.OnlineLearning\n\n'+'\n\n'.join('#check (∀ '+t['binders']+',\n    '+t['conclusion']+')' for t in new))
gate('general-initialization-draft-typecheck-v3','lake','env','lean',RUN/'general-initialization-draft-typecheck-v3.lean')
fixed();print('Source-required exact1+tail v3 types drafted and checked; original16/50 untouched, currentsourceaudit17/prooftotalnull; no bodies.',flush=True)
