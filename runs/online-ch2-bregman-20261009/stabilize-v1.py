from common import *
fixed()
review = RUN/'contract-review-v1.json'
assert sha(review) == '8c393baa4505e54d46b745b51e717d32420eb13afc6f9f361d9afa2513b5a911'
r = load(review)
assert r['verdict'] == 'accepted-with-explicit-delta' and not r['required_repairs']
for row in load(RUN/'contract-review-inputs-v1.json')['rows']:
    assert sha(row['path']) == row['sha256'], row['path']
d = load(CONTRACT/'targets-draft-v1.json')
mutable = [RUN/x for x in ['lifecycle-sessions.jsonl','lifecycle-state.json','own-artifact-journal.md']]
mutable += [ROOT/x/(TASK+'.md') for x in ['tasks','proof-obligations','conversion-windows']]
write(RUN/'pre-stabilization-exact-own-metadata-v1.json',dict(rows=[dict(path=p.as_posix(),sha256=sha(p),raw_base64=base64.b64encode(p.read_bytes()).decode('ascii')) for p in mutable]))
write(CONTRACT/'stabilized-v1.json',dict(stage='stabilized',targets=d['targets'],definition=d['definition'],semantic_slots=d['semantic_slots'],source_to_Lean_delta=d['source_to_Lean_delta'],source_card_sha256=sha(CONTRACT/'source-card-v1.json'),draft_sha256=sha(CONTRACT/'targets-draft-v1.json'),context_sha256=sha(RUN/'neutral-types-v1.txt'),review_sha256=sha(review),initial_lower_leaves=d['targets'][:2],dependency_DAG=d['dag'],dependency_evidence='Pinned typed API retrieval v2 actual exit0; accepted PR208 minimum comparison. No Bregman production body compiled yet.',allowed_production_file=PUBLIC.as_posix(),edit_boundary='Only exact five frozen theorem bodies, full canonical definition and required imports in new production file; no extra named helpers, roots/Tests/readers/old baseline/global frontier. Changed target or context needs versioned review.',local_proof_obligations=5,definition_not_a_proof_obligation=True,source_container_closed=False,chapter_complete=False,whole_Goal_status='ACTIVE'))
contents = {
 'tasks': '# Bregman proximal comparison\n\nTask '+TASK+'; proving. Five headers and the complete canonical definition frozen in docs/contracts/online-ch2-bregman-v1/stabilized-v1.json after distinct staged automated CONTRACT accepted-with-explicit-delta. Initial finite ready leaves: self and three-point algebraic identities. Remaining three frozen bodies pending. No source/chapter/Goal closure.\n',
 'proof-obligations': '# Bregman obligations\n\n'+'\n'.join('- '+t['declaration']+': proving; frozen '+t['statement_hash']+'.' for t in d['targets'])+'\n\nFive local proofs; definition separate; chapter denominator unknown. Source finitePart/subgradient/minimum bridge, domain/interior extension, attained causal current-loss recursion and same-run sharp fixed/variable telescopes remain REQUIRED/OPEN; all eight Chapter2 forwards OPEN; whole Goal ACTIVE. Public Test contracts require separate neutral review before bodies.\n',
 'conversion-windows': '# Bregman conversion v1\n\nChapter2 post-Theorem2.13 -> Section15.5.1 one-step proof -> necessary Definition6.4/Lemma6.7 machinery only. Normed dual core and separate complete-Hilbert gradient bridge; total fderiv defaults explicitly disclosed; positivity only under its frozen hypotheses. Actual supplied proximal minimum is not an existence/recursive-algorithm theorem. Both negative residuals and both base differentiability hypotheses preserved. All source-to-Lean deltas and required-open source bridges in stabilized-v1.json. Only new production file bodies/imports allowed; old roots/Tests/readers/global frontier unchanged.\n'
}
for dirname, text in contents.items():
    (ROOT/dirname/(TASK+'.md')).write_bytes(text.encode('utf8'))
pins = [dict(declaration=t['declaration'],statement_hash=t['statement_hash']) for t in d['targets']]
event('stabilized-native-v1','stabilized',dict(contract_sha256=sha(CONTRACT/'stabilized-v1.json'),review_sha256=sha(review),targets=pins,definition_sha256=d['definition']['definition_term_sha256'],source_container_closed=False,chapter_complete=False,goal_complete=False))
event('proving-native-v1','proving',dict(selected_leaves=pins[:2],allowed_file=PUBLIC.as_posix(),local_obligations=5,source_container_closed=False,chapter_complete=False,goal_complete=False))
capture('leaf-attempt-running-v1',sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','trial-log','--task',TASK,'--role','lower','--kind','attempt','--status','running','--attempt-id','BG001-algebra-v1','--run-id',RUN.name,'--lean',PUBLIC.relative_to(ROOT).as_posix(),'--statement-hash',d['targets'][1]['statement_hash'],'--obligations-before','2','--obligations-after','2','--notes','Two finite algebraic leaves from five frozen package proofs; canonical actual fderiv. Local count only; other three and general source mandatory-open.')
write(RUN/'30_lower-plan-v1.md','Initial lower leaves: canonical definition, divergence_self, source-oriented three_point_identity using actual continuous-linear-map algebra. No differentiability/convexity inferred. Then finite nonnegative scalar-segment support, Hilbert gradient conversion, and actual proximal minimum plus differentiated penalty. Preserve all five exact headers and definition term. No holes for unimplemented declarations; no extra named public helpers. Focused builds and exact type checks precede candidate. Full source/Chapter2/whole Goal remain open.')
fixed()
print('Five exact headers and canonical definition stabilized; two algebraic leaves selected.')
