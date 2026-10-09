from common import *
import copy
fixed()
br=load(RUN/'five-BODY-review-v1.json')
assert br['BODY_verdict']=='accepted-with-explicit-delta' and not br['required_repairs']
pr=load(RUN/'publication-plan-review-v1.json')
assert pr['required_repairs'] and pr['materialization_verdict'] not in ['accepted','accepted-with-explicit-delta']
for name in ['five-BODY-review-inputs-v1.json','publication-plan-review-inputs-v1.json']:
    for row in load(RUN/name)['rows']: assert sha(row['path'])==row['sha256'],row['path']
proposal=load(RUN/'reader-proposal-v1.json'); new=copy.deepcopy(proposal)
note=next(n for n in new['notes'] if n['full_name'].endswith('.iterate_variable_sharp'))
before=note['math']
note['math']=r'\begin{gathered}T>0,\quad B(u;x_t)\le M\ (0\le t<T),\\ \eta_t>0\ (0\le t<T),\quad \eta_{t+1}\le\eta_t\ (t+1<T),\\ L_T(u)\le\frac{M}{\eta_{T-1}}-\frac{B(u;x_T)}{\eta_{T-1}}-\sum_{t=0}^{T-1}\frac{B(x_{t+1};x_t)}{\eta_t}.\end{gathered}'
after=note['math']
write(RUN/'reader-proposal-v2.json',new)
high=load(RUN/'publication-after-highlights.json')
matching=next(n for n in high['highlights'] if n['full_name']==note['full_name'])
assert matching['math']==before
matching['math']=after
write(RUN/'publication-after-highlights-v2.json',high)
plan=load(CONTRACT/'exact-publication-plan-v1.json')
row=next(r for r in plan['rows'] if r['path']==(ROOT/'website/content/highlights.json').as_posix())
row['after_snapshot']=(RUN/'publication-after-highlights-v2.json').as_posix()
row['after_sha256']=sha(RUN/'publication-after-highlights-v2.json')
plan['reader_proposal_sha256']=sha(RUN/'reader-proposal-v2.json')
plan['prospective_repair']='Only variable-sharp displayed formula now bounds positivity by t<T and monotonicity by t+1<T, including T=1 correctly. Four other exact path transitions and all other highlight fields unchanged; Lean/context/headers/BODY unchanged. Delayed native conversion-window materialization required before baseline writes, never retroactive stabilization evidence.'
write(CONTRACT/'exact-publication-plan-v2.json',plan)
guard=(RUN/'publication_guard_v1.py').read_text(encoding='utf8').replace('publication-plan-review-v1.json','publication-plan-review-v2.json').replace('exact-publication-plan-v1.json','exact-publication-plan-v2.json')
old="assert statement_hash(lean_declaration_header(p,t['declaration']))==t['statement_sha256']"
newcode="""assert hashlib.sha256(t['exact_header'].encode('utf8')).hexdigest()==t['statement_sha256']
            fence=next(load(f) for f in CONTRACT.glob('*fence-v1.json') if load(f).get('declaration')==t['declaration'])
            assert statement_hash(lean_declaration_header(p,t['declaration']))==fence['statement_hash']"""
assert guard.count(old)==1
guard=guard.replace(old,newcode)
write(RUN/'publication_guard_v2.py',guard)
integration=(RUN/'integrate-publication-v1.py').read_text(encoding='utf8').replace('publication-plan-review-v1.json','publication-plan-review-v2.json').replace('exact-publication-plan-v1.json','exact-publication-plan-v2.json').replace('publication_guard_v1','publication_guard_v2').replace('reader-proposal-v1.json','reader-proposal-v2.json')
needle="for row in p['rows']: Path(row['path']).write_bytes(Path(row['after_snapshot']).read_bytes())"
insert="""conversion=ROOT/'conversion-windows'/(TASK+'.md')
assert not conversion.exists()
write(RUN/'pre-conversion-native-exact-v1.json',dict(rows=[dict(path=q.as_posix(),sha256=sha(q),raw_base64=base64.b64encode(q.read_bytes()).decode('ascii')) for q in [RUN/'lifecycle-sessions.jsonl',RUN/'lifecycle-state.json',RUN/'trials.jsonl',RUN/'own-artifact-journal.md'] if q.exists()]))
capture('conversion-window-help-v1',sys.executable,'-B','-X','utf8','tools/bandit.py','conversion-window','--help')
capture('conversion-window-native-materialization-v1',sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','conversion-window',TASK,'--title','Same-run prescient cumulative bounds: frozen five-terminal conversion')
write(RUN/'conversion-window-native-template-v1.raw',conversion.read_bytes())
conversion.write_bytes(conversion.read_bytes()+('\\nDelayed native artifact materialization after BODY review. The draft conversion intent below existed in director-architect-draft-v1.md at its indexed draft SHA; this native template did NOT exist at stabilization and is not backdated. No new target or premise.\\n\\n'+(RUN/'director-architect-draft-v1.md').read_text(encoding='utf8')+'\\nFrozen source/headers/context/DAG: '+CONTRACT.relative_to(ROOT).as_posix()+'/stabilized-v1.json. All five exact theorem bodies are now reviewed and focused-compiled; combined/publication/FINAL gates remain separately pending.\\n').encode('utf8'))
write(RUN/'conversion-window-delay-inspected-v1.json',dict(actual_native_receipt_sha256=sha(RUN/'conversion-window-native-materialization-v1.json'),native_template_sha256=sha(RUN/'conversion-window-native-template-v1.raw'),filled_artifact_sha256=sha(conversion),draft_intent_sha256=sha(RUN/'director-architect-draft-v1.md'),not_contemporaneous_stabilization=True,publication_repair_review_sha256=sha(pr),whole_Goal_status='ACTIVE'))
"""+needle
assert integration.count(needle)==1
integration=integration.replace(needle,insert)
write(RUN/'integrate-publication-v2.py',integration)
write(RUN/'publication-repair-v2.json',dict(prior_repair_review_sha256=sha(RUN/'publication-plan-review-v1.json'),BODY_review_sha256=sha(RUN/'five-BODY-review-v1.json'),changed_field='iterate_variable_sharp reader math only',before_math=before,after_math=after,raw_UTF8_header_hashes_distinct_from_native_normalized_statement_hashes=True,guard_draft_v1_unexecuted_hash_comparison_corrected_in_v2=True,production_sha256=sha(PUBLIC),canary_sha256=sha(ROOT/'Tests/OnlinePrescientBregmanRegretCanary.lean'),four_other_transitions_unchanged=True,whole_Goal_status='ACTIVE'))
write(RUN/'publication-plan-review-packet-v2.md','''# Separate v2 bounded-index publication repair and delayed conversion artifact

Read exact v1 repair decision, all five BODY accepted decision (unchanged bodies), v2 reader/afterhighlights/plan/repair. Only one variable-sharp displayed formula changes: positivity eta_t>0 for 0<=t<T; monotonicity eta_(t+1)<=eta_t for t+1<T. T=1 has positivity eta0 and no unplayed comparison. Every other field/four other prospective path transitions unchanged. Baseline five paths remain BEFORE. No canonical edit yet.

Before baseline mutation integrate-publication-v2.py must validate BOTH distinct review inputs, capture exact native beforebytes, run actual --help and native-scoped conversion-window command, preserve actual unfilled template, append already frozen draft conversion intent and explicitly disclose delayed materialization; record hashes. It does not claim native conversion-window existed at stabilization. Native journal changes are post-review authorized output with contemporaneous beforebytes. No target weakening. Guard-v1 was only an unexecuted draft and wrongly compared raw headerSHA to native normalized statementSHA; guard-v2 checks exact frozen raw header and native fence hash independently, no changed mathematics. REVIEW THESE exact helpers too, but do not execute or mutate native/Git/roots.

Create-only publication-plan-review-v2.md/json with verdict/materialization_verdict/required_repairs/approved_five_rows/approved_plan_sha256, before/after all indexed inputs and32928baseline/PDF, reporthash and actor limitations. Scope prospective exact five-path materialization plus OWN delayed conversion/contribution/evidence only. Verify old fields/links/otherBooks/sharedregistry preserved, all source/conditional boundaries. Complete combined Lean/harness/contributor/shadow/site/registry/DOM/pixels/FINAL/native/delivery still pending; wholeGoal ACTIVE. Preserve v1 failure and review; BODY acceptance not source/chapter acceptance.
''')
paths=[p for d in [RUN,CONTRACT] for p in d.rglob('*') if p.is_file() and '__pycache__' not in p.parts]
paths += [PUBLIC,ROOT/'Tests/OnlinePrescientBregmanRegretCanary.lean']+[Path(r['path']) for r in plan['rows']]
write(RUN/'publication-plan-review-inputs-v2.json',dict(rows=rows(paths),exact_plan_sha256=sha(CONTRACT/'exact-publication-plan-v2.json'),baseline_count=32928,allowed_new_outputs=['publication-plan-review-v2.md','publication-plan-review-v2.json'],no_canonical_mutation_yet=True,whole_Goal_status='ACTIVE'))
fixed()
print('Exact single-mathfield v2 repair/helpers pinned; delayed native artifact remains pending actual execution.')
