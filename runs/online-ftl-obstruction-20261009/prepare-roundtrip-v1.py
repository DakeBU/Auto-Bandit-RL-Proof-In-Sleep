from common_v1 import *
import re
old=load(RUN/'baseline-v1.json')
baseline=old['rows'][:]
for i,rel in enumerate(['runs/active_frontier.json','docs/contracts/online-book-v1/coverage.json','research-wiki/mathlib/theorem-cards.md']):
    p=ROOT/rel;q=RUN/'baseline'/('additional-input-'+str(i)+'-v2.raw')
    write(q,p.read_bytes());baseline.append(dict(path=rel,sha256=sha(p),snapshot=q.as_posix()))
write(RUN/'baseline-v2.json',dict(old,rows=baseline,repair='Correct active-frontier location and add existing book coverage/theorem-card baseline before contract freeze; v1 retained.'))
fixed()
definitions=[]
for rel,names in [('BanditRLProof/OnlineLearningMean.lean',['empiricalMean']),
    ('BanditRLProof/OnlineLearningFTL.lean',['meanPredict']),
    ('BanditRLProof/OnlineLearningRegret.lean',['comparatorRegret','NoRegret']),
    ('BanditRLProof/OnlineSquareMinimum.lean',['squaredBestRegret']),
    ('BanditRLProof/OnlineNoRegretSemantics.lean',['LimitNoRegret'])]:
    text=(ROOT/rel).read_text(encoding='utf8')
    for name in names:
        match=re.search(r'(?m)^(?:noncomputable )?def '+name+r'\b',text);assert match,name
        after=text[match.start():];end=re.search(r'\n\s*\n',after);assert end
        definitions.append(after[:end.start()].strip())
context=(CONTRACT/'context-v1.lean.txt').read_text(encoding='utf8')
newdef=context.split('/-- Explicit binary')[1].split('end BanditRL.OnlineLearning')[0]
newdef='noncomputable def dyadicObservation'+newdef.split('noncomputable def dyadicObservation')[1].strip('\n')
neutral='import Mathlib\n\nopen Filter\nnamespace BanditRL.OnlineLearning\n\n'+'\n\n'.join(definitions)+'\n\n'+newdef+'\n\n'
write(RUN/'neutral-context-and-statements-v1.lean.txt',neutral+(CONTRACT/'targets-v1.lean.txt').read_text(encoding='utf8')+'\n\nend BanditRL.OnlineLearning\n')
write(RUN/'blind-packet-v1.md','Read ONLY neutral-context-and-statements-v1.lean.txt. Reconstruct all four propositions in ordinary mathematics and LaTeX, precise quantifiers, assumptions, strict-past process/initialization, signed metrics, ordinary versus upper condition, total division and dyadic subsequence indices. No source identity lookup or other repository/prior-verdict access, no proof edits. Actor has reused staged history, not absolute blindness. Write only blind-reconstruction-v1.md and blind-receipt-v1.json in thisRUN; hash BOTH inputs before/after, reportSHA, actor requestedAstra/medium/runtime_attestedfalse, inputs_unchanged/input_checks. No inference of compilation or source equivalence.')
write(RUN/'blind-inputs-v1.json',dict(rows=rows([RUN/'neutral-context-and-statements-v1.lean.txt',RUN/'blind-packet-v1.md'])))
targets=load(CONTRACT/'targets-v1.json')['targets']
probe=context.replace('end BanditRL.OnlineLearning','')
# Elaborate the four exact propositions as local Prop-valued definitions; no theorem evidence.
for t in targets:
    header=t['header'];left,right=header.split(' :\n',1)
    probe+=left.replace('theorem ','def draft_',1)+' : Prop :=\n'+right+'\n\n'
probe+='''#check meanPredict_fixedRegret_limit_iff
#check meanPredict_limitNoRegret_of_mean_converges
#check empiricalMean_mem
#check tendsto_pow_atTop_atTop_of_one_lt
#check Finset.sum_range_succ
#check le_of_tendsto
#check ge_of_tendsto
#check Nat.one_le_pow
#check Filter.tendsto_add_atTop_nat
end BanditRL.OnlineLearning
'''
write(RUN/'api-signature-probe-v1.lean',probe)
write(CONTRACT/'reader-requirements-v1.json',dict(
    R1='Pinned source ordinary-lim display, existing upper NoRegret and proposed correction remain separate; four DERIVED terminals, not four printed results.',
    R2='Same actual initial-half strict-past meanPredict; one fixed all-time observation stream, no horizon/future/mean algorithm oracle.',
    R3='D1 exact iff for all unit comparators versus existence of one convergent empirical mean inunit; necessity uses actual comparator0/1 limits, not a convergence premise.',
    R4='D2 explicit binary well-founded dyadic recursion and D3 two empirical-mean subsequences with distinct2/3 and1/3 limits; exact prefix counts and subsequence divergence produced, not assumed.',
    R5='D4 same bounded source-FTL pathwise upper NoRegret and best/T0 together with nonexistence of any ordinary real limit at the fixed comparator0 and failure of literal all-comparator LimitNoRegret. Signed negative subsequence limits allowed; no stochastic/minimax claim.',
    R6='All four public endpoints instantiated by nondegenerate exact finite-prefix public canaries; focused/rootTests/harness/axioms/fences/nonempty committed-HEAD contributor/site/registry/pixels/semantic gates separately recorded.',
    R7='Only four derived obligations may close; original16/null/historical overlays and other required C1C2/C3-16/appendices remain. Full Chapter1 reconciliation/gate still required; GoalACTIVE, PR201stackedunmerged, main/live unchanged.'))
write(RUN/'contract-mutable-scope-v1.json',dict(immutable_headers=sha(CONTRACT/'targets-v1.lean.txt'),immutable_context=sha(CONTRACT/'context-v1.lean.txt'),
    proving_scope=[PUBLIC.relative_to(ROOT).as_posix(),CANARY.relative_to(ROOT).as_posix()],body_only_with_frozen_headers=True,
    canary_contract_review_before_proof=True,own_task_append_only=[d+'/'+TASK+'.md' for d in ['tasks','proof-obligations','conversion-windows']],
    own_run_new_evidence=True,own_contract_new_versions_reviewed=True,own_native_journals_only=True,
    global_frontier_memory_indexes_immutable=True,root_reader_registry_contribution_require_separate_BODY_review=True,
    terminal_edit_requires_new_contract_review=True,source_chapter_whole_goal_complete=False))
write(RUN/'source-contract-review-packet-v1.md','ANTI-ANCHORED contract + separately proposed source-correction review. Read exact v10 PDF14/16/18 text and originalpixels; inspect four frozen headers/scopedcontext and blind reconstruction. Per-target seven slots; mathematical plausibility and source relationship separately. D1 exactiff unitcomparators/one meanlimit, D3 actualdyadic stream and correct horizons/2/3vs1/3, D4 bounded sameactualFTL fixedzero ordinary nonexistence coexisting with upperNoRegret and best/T0. No already-assumed limits/regret or source rewriting. Proposed correction is separate, no pinnedsource edit. No source-facing body compiled yet; probeProp definitions are elaboration only. All RAW current inputs before/after; exactreaderrequirements and proofscope. Original16/null/otherC1C2/C3-16/appendices/GoalACTIVE unchanged. Actor reuseddistinctAstra/medium, no human/external/runtime/absoluteblind claim. Outputs only source-contract-review-v1.md and source-contract-receipt-v1.json: verdict/fixed_input_count/raw_input_checks(path,before_sha256,after_sha256,unchanged)/inputs_unchanged/report_sha256/required_blocking_repairs/required_reader_corrections EXACTreaderrequirements/permitted_future_proof_scope EXACTmutablescope/per_target_seven_slot_audits/separate_source_correction_verdict/pixelreview. No body/git/site edits.')
print('Neutral four-target packet and signature probe ready; no theorem body.',flush=True)
