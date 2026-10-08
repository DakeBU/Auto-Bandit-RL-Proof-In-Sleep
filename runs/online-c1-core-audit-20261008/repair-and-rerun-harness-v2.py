from common_integrated_v1 import *
import importlib.util
fixed_integrated()
failed=load(RUN/'combined-full-harness-v1-exit.json')
assert failed['exit_code']==1
log=(RUN/'combined-full-harness-v1.log').read_text(encoding='utf8')
assert 'test_archive_is_reproducible' in log and 'FAILED (failures=1, skipped=7)' in log
write(RUN/'full-harness-archive-repair-analysis-v1.json',dict(
    actual_first_full_gate_exit=1,actual_tests=472,actual_failures=1,actual_skips=7,
    failed_test='test_build_anonymous_iclr_supplement.AnonymousSupplementTests.test_archive_is_reproducible',
    failure='Two generated test ZIP raw bytes differ. Both source/Tests Lean builds passed.',
    probable_cause='Own official reference-index refresh ran concurrently during the full harness; the archive builder explicitly reads local_lean_declarations.json. Its current source snapshot changed by12 own locator shifts and4 restored old PR196 entries.',
    causal_limit='Temporary failing archives were cleaned by unittest teardown; this record does not claim a retained per-entry ZIP diff or conclusive attribution.',
    remedy='No archive builder/test/anonymous snapshot edits. Record all actual raw payload input bindings, run the exact reproducibility assertion and complete harness with source inputs stable; compare bindings afterwards.',
    source_statement_or_proof_or_fixture_change=False,production_gate_waiver=False,
    anonymous_material_modified=False,chapter_complete=False,goal_complete=False))
native('harness-repair-event-v1','lifecycle-event','--session',TASK,'--event','repair',
    '--payload-json',json.dumps(dict(contract_version=2,failed_gate='fullharness/archive-reproducibility',
    source_statement_changed=False,proof_body_changed=False,analysis=(RUN/'full-harness-archive-repair-analysis-v1.json').as_posix())))
spec=importlib.util.spec_from_file_location('core_audit_readonly_payload_inventory',ROOT/'tools/build_anonymous_iclr_supplement.py')
builder=importlib.util.module_from_spec(spec);spec.loader.exec_module(builder)
inputs={};original=builder.read_regular
def recorded(rel):
    data=original(rel);h=hashlib.sha256(data).hexdigest()
    assert rel not in inputs or inputs[rel]==h,rel
    inputs[rel]=h
    return data
builder.read_regular=recorded
payload=builder.build_payload(allow_missing_graph=True)
assert 'research-wiki/retrieval-index/local_lean_declarations.json' in inputs
assert not any(rel.startswith('runs/online-c1-core-audit-20261008/') for rel in inputs)
index_names=subprocess.check_output(['git','ls-files','-z'])
head=subprocess.check_output(['git','rev-parse','HEAD'])
write(RUN/'harness-stable-raw-source-inputs-v2.json',dict(actual_read_regular_files=inputs,
    actual_payload_files=len(payload),archive_written=False,anonymous_release_refreshed=False,
    input_count=len(inputs),git_index_names_sha256=hashlib.sha256(index_names).hexdigest(),
    head=head.decode('utf8').strip(),new_package_source_scope_frozen=True,
    note='Read-only diagnostic build_payload records exact existing raw inputs; no generated archive or anonymous output written.'))
def stable():
    fixed_integrated()
    for p,h in inputs.items(): assert sha(p)==h,p
    assert subprocess.check_output(['git','ls-files','-z'])==index_names
    assert subprocess.check_output(['git','rev-parse','HEAD'])==head
stable()
gate('archive-reproducibility-focused-v2',sys.executable,'-B','-X','utf8','-m','unittest',
    'tools.test_build_anonymous_iclr_supplement.AnonymousSupplementTests.test_archive_is_reproducible')
stable()
gate('combined-full-harness-v2',sys.executable,'-B','-X','utf8','tools/bandit.py','check')
stable()
assert load(RUN/'combined-root-build-v1-exit.json')['exit_code']==0
assert load(RUN/'combined-Tests-build-v1-exit.json')['exit_code']==0
write(RUN/'combined-gates-v1.json',dict(public_files_sha256={p.as_posix():sha(p) for p in MODULES},
    canary_sha256=sha(CANARY),source_pins={p:sha(p) for p in ['lean-toolchain','lakefile.lean','lake-manifest.json']},
    actual_commands=['lake build BanditRLProof','lake build Tests','python tools/bandit.py check (stable v2)'],
    actual_exit_codes=[0,0,0],actual_failed_harness_v1_preserved=True,
    exact_focused_archive_reproducibility_passed=True,raw_source_snapshot_stable_before_after=True,
    own_canary_tracked_before_harness=True,contributor_and_site_and_FINAL_pending=True,
    five_source_audits_still_pending_FINAL_native=True,new_production_proofs=0,chapter_complete=False,goal_complete=False))
print('Focused reproducibility and full harness actualpass on unchanged raw source snapshot; original failure retained, no test/builder/anonymous source edits.')
