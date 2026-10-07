"""Repair only the actual required progress-field prefix schema; retain failed gate."""
from common_v2 import *
fixed(True);assert load(RUN/'contributor-exact-v1-01-exit.json')['exit_code']!=0
p=Path('research-wiki/contribution-contracts/online-osd-public-20261007.json');write(RUN/'snapshots/before-contributor-schema-repair-v2.txt',p.read_bytes());d=load(p)
d['progress_updates']['teaching_route']='updated: current source/public evidence for existing canonical chain; zero new proofs and no chapter completion'
d['progress_updates']['results_ledger']='no-change-with-reason: additive own acceptance overlay only after all remaining gates; existing chapter ledger unchanged'
d['progress_updates']['roadmap']='no-change-with-reason: total Goal ACTIVE, global SGB unchanged; generic policy/Example2.32/linearization/unitanalysis/remaining chapter obligations REQUIRED'
p.write_bytes((json.dumps(d,ensure_ascii=False,indent=2)+'\n').encode())
write(RUN/'contributor-schema-repair-v2.json',dict(actual_failure='Exact-base contributor checker rejected only three progress_updates prefixes. Actual schema requires updated: or no-change-with-reason:.',changes=['teaching_route prefix/content','results_ledger explicit no-change-with-reason','roadmap explicit no-change-with-reason'],original_manifest_snapshot='snapshots/before-contributor-schema-repair-v2.txt',original_failed_gate_and_committed_script_preserved=True,public_canary_headers_reader_math_and_root_Tests_unchanged=True,current_full_harness_rerun_pending=True,source_FINAL_separate_repair_review_pending=True))
text=(RUN/'source-site-gates-v1.py').read_text(encoding='utf-8').replace("passed('prepare-site-adapters-v1-01')","passed('prepare-site-adapters-v1-01');passed('full-harness-v2-01')")
for s in ['contributor-exact-v1-01','scoped-diff-v1-01','source-scope-v1-01']:text=text.replace(s,s.replace('v1','v2'))
text=text.replace("RUN/'check-scoped-diff-v1.py','v1'","RUN/'check-scoped-diff-v1.py','v2'");write(RUN/'source-site-gates-v2.py',text)
text=(RUN/'prepare-final-evidence-v3.py').read_text(encoding='utf-8')
for s in ['contributor-exact-v1-01','scoped-diff-v1-01','source-scope-v1-01','source-site-gates-v1-01','full-harness-v1-01']:text=text.replace(s,s.replace('v1','v2'))
text=text.replace("'candidate-frontier-refresh-v1']","'candidate-frontier-refresh-v1','source-site-gates-v1-01','contributor-exact-v1-01']")
text=text.replace("'Task shadow CLI rejected", "'Exact-base contributor schema rejected three progress prefixes; only existing required prefixes repaired in own manifest, full harness2/current contributor2 required; no math/reader change.','Task shadow CLI rejected")
write(RUN/'prepare-final-evidence-v4.py',text)
text=(RUN/'prepare-pr-payload-v3.py').read_text(encoding='utf-8').replace('All R1-R8 discharged','Original exact-base contributor prefix-schema failure and its three-field metadata repair are retained; current full harness2 and contributor2 pass. All R1-R8 discharged');write(RUN/'prepare-pr-payload-v4.py',text)
text=(RUN/'complete-delivery-gates-v4.py').read_text(encoding='utf-8').replace("passed('prepare-pr-payload-v3-01')","passed('prepare-pr-payload-v4-01')");write(RUN/'complete-delivery-gates-v5.py',text)
event('repair',dict(kind='own contributor manifest progress prefix schema',repair=(RUN/'contributor-schema-repair-v2.json').as_posix(),public_and_canary_unchanged=True),attempt='contributor-v2')
print('Actual contributor schema repaired only in own metadata; original exact-base failure preserved, current gates must run.')
