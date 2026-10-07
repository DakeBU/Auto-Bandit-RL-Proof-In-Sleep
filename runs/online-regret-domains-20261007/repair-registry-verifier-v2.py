from common_v1 import *
fixed(integrated=True)
original=(RUN/'verify-registry-v1.py').read_text(encoding='utf-8')
old="for phrase in ['Finset.sum_sub_distrib','(hb : ∀ u ∈ V','(hl : ∀ u ∈ V','bound u T < ε']:\n assert phrase in mt,phrase"
new="""for phrase in ['(hb : ∀ u ∈ V','(hl : ∀ u ∈ V']:
 assert phrase in mt,phrase
# Catalogue exposes exact statement plus source link; teaching disclosure
# exposes the complete exact proof. Check the complete bodies on that page.
source=PUBLIC.read_text(encoding='utf-8')
for n in load(CONTRACT/'existing-public-headers-v1.json'):
 start=source.index('theorem '+n+' ')
 ends=[j for marker in ['\\n/--','\\nend BanditRL.OnlineLearning'] for j in [source.find(marker,start)] if j>=0]
 segment=source[start:min(ends)].strip()
 assert ' := by' in segment and ' '.join(segment.split()) in ' '.join(text.split()),n
for phrase in ['Finset.sum_sub_distrib','bound u T < ε','tendsto_order']:
 assert phrase in text,phrase"""
assert old in original
updated=original.replace(old,new).replace("RUN/'registry-v1.json'","RUN/'registry-v2.json'").replace('full_actual_module_types_and_proofs_present=True','module_catalogue_exact_types_present=True,reader_disclosure_full_exact_proofs_present=True')
write(RUN/'verify-registry-v2.py',updated)
write(RUN/'registry-verifier-repair-v2.json',dict(original_failure_log_sha256=sha(RUN/'registry-check-v1.log'),original_reason='v1 mistakenly required proof正文 on module catalogue, which exposes exact types/source links; exact proof bodies belong to the teaching-page disclosure',site_source_and_scanner_unchanged=True,mathematical_target_unchanged=True,original_registry_v1_pass_record_not_written=True,repair='v2 checks full exact existing proof bodies against actual public source in teaching-page text; still checks full catalogue types and all10835identity/URL/hash pairs',applicable_site='tmp/online-regret-domains-site-v1',source_commit=load('tmp/online-regret-domains-site-v1/site-manifest.json')['source_commit']))
native('registry-verifier-repair-event-v2','lifecycle-event','--session',TASK,'--event','repair','--payload-json',json.dumps(dict(run_id=RUN.name,repair_record=(RUN/'registry-verifier-repair-v2.json').as_posix(),mathematical_target_changed=False,chapter_complete=False,goal_complete=False)))
gate('registry-check-v2',sys.executable,'-B','-X','utf8',RUN/'verify-registry-v2.py')
# Capture helper v1 was not executed; update the applicable registry binding
# in a separate helper version instead of altering its prepared artifact.
capture=(RUN/'capture-reader-v1.py').read_text(encoding='utf-8').replace("RUN/'registry-v1.json'","RUN/'registry-v2.json'")
write(RUN/'capture-reader-v2.py',capture)
gate('current-reader-capture-v2',sys.executable,'-B','-X','utf8',RUN/'capture-reader-v2.py')
native('registry-verifier-candidate-event-v2','lifecycle-event','--session',TASK,'--event','candidate','--payload-json',json.dumps(dict(run_id=RUN.name,registry=(RUN/'registry-v2.json').as_posix(),mathematical_target_changed=False,chapter_complete=False,goal_complete=False)))
fixed(integrated=True)
