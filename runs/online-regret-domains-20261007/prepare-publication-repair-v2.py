from common_v1 import *
fixed(integrated=True)
assert load(RUN/'push-creation-v1-exit.json')['exit_code']==1
assert 'Internal Server Error' in (RUN/'push-creation-v1.log').read_text(encoding='utf-8')
repo='repos/DakeBU/Auto-Bandit-RL-Proof-In-Sleep'
remote=subprocess.check_output(['git','ls-remote','origin','refs/heads/'+BRANCH],encoding='utf-8')
duplicates=json.loads(subprocess.check_output(['gh','api',repo+'/pulls?state=all&head=DakeBU%3Acodex%2Fresearch-online-regret-domains']))
assert not remote.strip() and not duplicates
write(RUN/'publication-command-repair-v2.json',dict(status='Transient remote publication failure; same authorized push/draft scope',failed_gate='push-creation-v1',failed_log_sha256=sha(RUN/'push-creation-v1.log'),original_source_and_FINAL_unchanged=True,remote_branch_absent=True,existing_PRs=[],mathematical_acceptance='accepted; no target or proof repair',change='Versioned retry push-creation-v2 and derivative create/delivery helpers accept the actual new successful gate; preserve failed v1',new_production_math=0,chapter_complete=False,goal_complete=False))
old=(RUN/'create-pr-v1.py').read_text(encoding='utf-8');assert old.count("'push-creation-v1-exit.json'")==1
write(RUN/'create-pr-v2.py',old.replace("'push-creation-v1-exit.json'","'push-creation-v2-exit.json'"))
old=(RUN/'prepare-delivery-v1.py').read_text(encoding='utf-8')
write(RUN/'prepare-delivery-v2.py',old.replace("'create-pr-v1'","'create-pr-v2'").replace("'push-creation-v1'","'push-creation-v2'"))
native('publication-repair-event-v2','lifecycle-event','--session',TASK,'--event','repair','--payload-json',json.dumps(dict(scope='Publication command only; mathematical package accepted',record=(RUN/'publication-command-repair-v2.json').as_posix(),failed_gate='push-creation-v1',same_branch=True,source_contract_unchanged=True,chapter_complete=False,goal_complete=False)))
write(RUN/'publication-repair-packet-v2.md','''# Required source reviewer: publication-only retry

Reuse /root/source_reviewer GPT-6 Astra/medium, history disclosed, no escalation/external/human/runtime attestation. Actual push-creation-v1 failed GitHub Internal Server Error after all FINAL/native/fullharness/contributor/diff/scope/raw committed gates passed. Remote branch absent and no existing PR checked. No source/tests/reader/contract or any earlier receipt/tool rewritten. Only derivative create-pr-v2 (one literal gate name v1→v2) and prepare-delivery-v2 (two applicable label replacements) plus resume-publication-v2 retry the same authorized ownbranch and same exactOPENPR189 draft scope. Originalfailed logs retained. Never treat exit1 as success; successfulnewgate actualneeded. No duplicatePR/merge/deploy/main/live/retirement/Goalcompletion.

Validate fixed repair rows, prior FINAL401/receipt/report unchanged and current public/canary/readers exact; inspect new helpers complete bounded changes and current Git status/scope. Native lifecycle publication repair is separate from accepted mathematical package. Repairedpublication event accepted without extra newmath/trial; existing0productionmath/1modelsubobligation/8tests retained. Write only publication-repair-review-v2.md and publication-repair-receipt-v2.json: actor.task, verdictaccepted|accepted-with-explicit-delta|rejected, report/report_sha256, allfixedrows+inputmanifest/report reviewed_files/fixed_input_count, required_repairs/required_mathematical_repairs/required_metadata_repairs arrays, chapter_complete=false/goal_complete=false. Return actualhashes. Review does not assert retry will succeed.
''')
paths=[RUN/p for p in ['publication-command-repair-v2.json','prepare-publication-repair-v2.py','create-pr-v1.py','create-pr-v2.py','prepare-delivery-v1.py','prepare-delivery-v2.py','resume-publication-v2.py','publication-repair-packet-v2.md','push-creation-v1.log','push-creation-v1-exit.json','final-reader-inputs-v1.json','final-reader-receipt-v1.json','final-reader-review-v1.md','accepted-decision-v1.json','native-acceptance-overlay-v1.json','committed-raw-audit-v1.json']]
write(RUN/'publication-repair-inputs-v2.json',dict(stage='publication-only-repair',rows=[dict(path=p.as_posix(),sha256=sha(p)) for p in paths],fixed_input_count=len(paths),source_target_unchanged=True,goal_complete=False))
fixed(integrated=True)
