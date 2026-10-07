from common_v1 import *
fixed(integrated=True)
original=(RUN/'verify-registry-v1.py').read_text(encoding='utf-8')
old="for phrase in ['Finset.sum_sub_distrib','(hb : ∀ u ∈ V','(hl : ∀ u ∈ V','bound u T < ε']:\n assert phrase in mt,phrase"
new="""for phrase in ['(hb : ∀ u ∈ V','(hl : ∀ u ∈ V']:
 assert phrase in mt,phrase
# Both generated surfaces expose exact statements and source links, not
# exact proof-code disclosures. Verify their full statements and separately
# bind complete local compiled source bodies; do not invent a UI feature.
sys.path.insert(0,str(ROOT))
from tools.abrl_lifecycle import normalize_statement
for n,h in load(CONTRACT/'existing-public-headers-v1.json').items():
 statement=normalize_statement(h)
 assert statement in ' '.join(mt.split()) and statement in ' '.join(text.split()),n
 source_url='https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/blob/'+m['source_commit']+'/BanditRLProof/OnlineLearningRegret.lean'
 assert any(href.startswith(source_url+'#L') for href in parsed.hrefs),n
assert sha(PUBLIC)==load(RUN/'reader-integrated-bindings-v1.json')['public_doc_insertion_sha256']
assert Path('docs/contracts/online-regret-domains-v1/complete-existing-module-v1.lean.txt').read_bytes()==(RUN/'snapshots/BanditRLProof--OnlineLearningRegret.lean.raw').read_bytes()
for phrase in ['Finset.sum_sub_distrib','tendsto_order','Finset.sum_nonpos']:
 assert phrase in text,phrase"""
assert old in original
updated=original.replace(old,new).replace("RUN/'registry-v1.json'","RUN/'registry-v3.json'").replace('full_actual_module_types_and_proofs_present=True','module_and_reader_full_exact_statements_present=True,compiled_complete_proof_source_bound=True,generated_exact_proof_code_disclosure=False')
write(RUN/'verify-registry-v3.py',updated)
write(RUN/'registry-verifier-repair-v3.json',dict(failed_verifier_logs=[dict(path=(RUN/f).as_posix(),sha256=sha(RUN/f)) for f in ['registry-check-v1.log','registry-check-v2.log']],reason='Both actual generated catalogue and teaching exact-Lean disclosures contain statements and source links. v1 and v2 wrongly required a nonexistent exact proof-code UI feature.',actual_surface_audit='Exact statements/fullsource links plus readable natural-language formula proofs; complete mathematical theorem bodies separately preserved/compiled in public source and BODY receipt',publication_protocol='Exact proof-code disclosure required when site exposes proof text; this site does not. No renderer/parser/source change is needed.',full_statement_check_not_weakened=True,source_and_all_math_unchanged=True,registry_identity_checks_unchanged=True,partial_PASS_records_not_created=True,applicable_site='tmp/online-regret-domains-site-v1',source_commit=load('tmp/online-regret-domains-site-v1/site-manifest.json')['source_commit']))
gate('registry-check-v3',sys.executable,'-B','-X','utf8',RUN/'verify-registry-v3.py')
capture=(RUN/'capture-reader-v1.py').read_text(encoding='utf-8').replace("RUN/'registry-v1.json'","RUN/'registry-v3.json'")
write(RUN/'capture-reader-v3.py',capture)
gate('current-reader-capture-v3',sys.executable,'-B','-X','utf8',RUN/'capture-reader-v3.py')
native('registry-verifier-candidate-event-v3','lifecycle-event','--session',TASK,'--event','candidate','--payload-json',json.dumps(dict(run_id=RUN.name,registry=(RUN/'registry-v3.json').as_posix(),mathematical_target_changed=False,chapter_complete=False,goal_complete=False)))
fixed(integrated=True)
