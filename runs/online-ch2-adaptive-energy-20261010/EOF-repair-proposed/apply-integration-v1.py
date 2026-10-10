from integration_guard_v1 import *

fixed_integration(after=False,review_inputs=True)
plan=load(PLAN)
for row in plan['rows']:
    Path(row['path']).write_bytes(Path(row['after_snapshot']).read_bytes())
write(CONTRIBUTION,(RUN/plan['prospective_manifest']).read_bytes())
fixed_integration(full_old_baseline=True)
write(RUN/'integration-applied-inspected-v1.json',dict(
    exact_old_file_deltas=6,new_manifest=rows([CONTRIBUTION]),
    production_sha256=sha(PUBLIC),Test_sha256=sha(TEST),
    all_other_35386_old_baseline_RAW_unchanged=True,
    source_families=1,production_proofs=3,complete_canaries=2,
    combined_gates='pending',site='pending',native_acceptance='pending',
    chapter_complete=False,whole_Goal='active'))
print('Applied exactly six approved AFTER snapshots and one new manifest.',flush=True)
