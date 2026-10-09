from publication_guard_v3 import *
fixed()
full=load(RUN/'full-harness-inspected-v1.json')
assert full['actual_check_passed']
combined=load(RUN/'combined-root-Tests-inspected-v1.json')
own=[ROOT/d/(TASK+'.md') for d in ['tasks','proof-obligations','research-wiki/retrieval-index']]
mutables=[CONTRIBUTION,*own,RUN/'lifecycle-sessions.jsonl',RUN/'lifecycle-state.json',RUN/'trials.jsonl',RUN/'own-artifact-journal.md']
write(RUN/'pre-candidate-own-metadata-v1.json',dict(rows=[dict(path=p.as_posix(),sha256=sha(p),raw_base64=base64.b64encode(p.read_bytes()).decode('ascii')) for p in mutables if p.exists()]))
summary=('Five frozen conditional same-run cumulative production proofs and two complete16/22conjunct canaries have actual focused/public VALUE/standard-only axiom/fence evidence and distinct staged BODY acceptance. '
    'Selected7public/7total nodes,1885coalesced direct TYPE_VALUE presences;8production and5canary required VALUE parents;4individually selected numeric proof branches have Eq.mpr heads and their specific new theorem constants. '
    'Actual combined root/Tests/full tools/bandit.py check passed with observed counts and exact hashes in combined-root-Tests-inspected-v1.json/full-harness-inspected-v1.json. '
    'Exact five-path publication plan-v2 materialized after distinct plan review-v3; reader played-index repair and operative-input binding repair preserved. '
    'Native conversion-window artifact was explicitly materialized LATE from frozen draft intent, before baseline writes; never backdated. All failed attempts and equivalent body/API/audit repairs retained. '
    'The conditional sharp telescopes/printed forms are now closed at the frozen interfaces, while full source-domain/generator/loss hypothesis transport and source valid-run wrapper remain REQUIREDOPEN. '
    'All8Chapter2forward source containers OPEN, Chapter2partial/null, Ch3-16unenumerated/null, whole16GoalACTIVE. Shared registry/site/DOM/pixels/FINAL/native/delivery pending. No main/live/merge/deploy/CI claim.')
for p in own: p.write_bytes(p.read_bytes()+('\nIntegrated candidate: '+summary+'\n').encode('utf8'))
c=load(CONTRIBUTION)
c['verification']['bandit_check']='Actual root/Tests/full tools/bandit.py check passed with compiler/unittest/exporter/check markers inspected; exact observed counts/source/receipt hashes in RUN combined-root-Tests-inspected-v1.json/full-harness-inspected-v1.json. No rule/toolchain/source weakening.'
CONTRIBUTION.write_bytes((json.dumps(c,ensure_ascii=False,indent=2)+'\n').encode('utf8'))
write(RUN/'memory-digest-v2.md','# '+TASK+'\n\n'+summary+'\n')
write(RUN/'proof-obligations-candidate-v1.json',dict(stage='integrated-candidate',production=[dict(declaration=t['declaration'],raw_UTF8_header_sha256=t['statement_sha256'],status='focused-and-combined-compiled; complete public VALUE/standard-only axioms/frozen; BODY-accepted; FINAL-pending') for t in load(CONTRACT/'stabilized-v1.json')['targets']],canaries=[dict(declaration=t['declaration'],raw_UTF8_header_sha256=t['statement_sha256'],status='full-conjunction actual public VALUE/standard-only axioms/frozen; BODY-accepted; FINAL-pending') for t in load(CONTRACT/'canary-stabilized-v1.json')['targets']],observed_combined=combined,observed_full_harness=full,remaining_required=['Source X/interior generator representation and source closedness packaging','Source finite-on-V/no-bottom to proper and global-support premise transport','Full source actual valid-run wrapper/interior conditions','All eight Chapter2 forward source containers'],source_container_closed=False,chapter_proof_total=None,chapter_complete=False,whole_Goal_status='ACTIVE'))
capture('candidate-list-lean-help-v1',sys.executable,'-B','-X','utf8','tools/bandit.py','list-lean-decls','--help')
_,out=capture('candidate-public-production-lookup-v1',sys.executable,'-B','-X','utf8','tools/bandit.py','list-lean-decls','OnlinePrescientBregmanRegret','--statement')
for t in load(CONTRACT/'stabilized-v1.json')['targets']: assert t['declaration'] in out,t['declaration']
_,out=capture('candidate-public-Test-lookup-v1',sys.executable,'-B','-X','utf8','tools/bandit.py','list-lean-decls','OnlinePrescientBregmanRegretCanary','--include-tests','--statement')
for t in load(CONTRACT/'canary-stabilized-v1.json')['targets']: assert t['declaration'] in out,t['declaration']
write(RUN/'pre-reference-index-native-exact-v1.json',dict(rows=[dict(path=p.as_posix(),sha256=sha(p),raw_base64=base64.b64encode(p.read_bytes()).decode('ascii')) for p in mutables if p.exists()]))
capture('candidate-scoped-reference-index-v1',sys.executable,'-B','-X','utf8',RUN/'reference-index-scoped-v1.py','reference-index')
idx=load(RUN/'reference-index-v1/local_lean_declarations.json')
indexed={r['full_name'] for r in idx['declarations']}
assert all(t['declaration'] in indexed for t in load(CONTRACT/'stabilized-v1.json')['targets'])
assert all(t['declaration'] not in indexed for t in load(CONTRACT/'canary-stabilized-v1.json')['targets'])
assert len(list((RUN/'reference-index-v1').glob('*.json')))==8
write(RUN/'candidate-scoped-reference-index-inspected-v1.json',dict(actual_cli_receipt_sha256=sha(RUN/'candidate-scoped-reference-index-v1.json'),actual_output_rows=rows((RUN/'reference-index-v1').glob('*.json')),default_production_index_contains_five=True,Tests_deliberately_separate=True,global_retrieval_indexes_and_SGB_unchanged=True,whole_Goal_status='ACTIVE'))
capture('candidate-frontier-help-v1',sys.executable,'-B','-X','utf8','tools/bandit.py','frontier-refresh','--help')
capture('candidate-frontier-refresh-v1',sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','frontier-refresh','--root-objective','Persistent Orabona Chapters1-16; conditional same-run cumulative Bregman interfaces only','--leaf',TASK,'--kind','review','--statement','Five frozen conditional cumulative proofs/two complete canaries BODY-accepted and combined compiled; full source Chapter2 incomplete. Registry/site/pixels FINAL/native/delivery pending.','--file',RUN/'five-BODY-review-v1.md','--source-status','source-reviewed','--leaf-status','gate-pending','--dependency','review:five-production-BODY:accepted','--dependency','review:two-canary-BODY:accepted','--dependency','lean:BanditRL.OnlinePrescientBregman.iterate_variable_regret:compiled','--trials',RUN/'trials.jsonl','--output',RUN/'current-frontier-v1.json','--shadow-status','pending')
_,out=capture('candidate-frontier-shadow-v1',sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','frontier-shadow','--trials',RUN/'trials.jsonl','--memory-digest',RUN/'memory-digest-v2.md','--frontier',RUN/'current-frontier-v1.json')
s=json.loads(out)
assert s['mismatches']==[] and not s['would_mutate']
write(RUN/'shadow-inspected-v1.json',dict(actual_report=s,scope='OWN bounded five conditional proofs/two complete canaries and retained failure history, not a source/chapter denominator.',global_SGB_unchanged=True,chapter_proof_total=None,chapter_complete=False,whole_Goal_status='ACTIVE'))
fixed()
print('Actual OWN lookup/reference-index and frontier-shadow gates passed; global SGB unchanged, source/chapter/Goal still open.')
