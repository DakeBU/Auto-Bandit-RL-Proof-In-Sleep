from integration_guard_v1 import *
fixed(after=False)
plan=load(CONTRACT/'exact-integration-plan-v1.json')
for row in plan['rows']:
    Path(row['path']).write_bytes(Path(row['after_snapshot']).read_bytes())
write(CONTRIBUTION,(RUN/'prospective-contribution-v1.json').read_bytes())
fixed()
write(RUN/'integration-applied-inspected-v1.json',dict(exact_old_file_deltas=6,new_manifest=rows([CONTRIBUTION]),production_unchanged=sha(MODULE),Test_unchanged=sha(TEST),all_other_34991_old_baseline_RAW_unchanged=True,combined_gates='pending',site='pending',FINAL='pending',native_acceptance='pending',delivery='pending',chapter_complete=False,whole_Goal='active'))
print('Applied exactly approved six snapshots and one new manifest.',flush=True)
