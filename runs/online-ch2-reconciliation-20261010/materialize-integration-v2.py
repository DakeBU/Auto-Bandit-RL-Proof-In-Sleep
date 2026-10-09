from integration_guard_v2 import *
fixed(after=False)
assert not CONTRIBUTION.exists()
plan=load(CONTRACT/'exact-integration-plan-v1.json')
assert all(Path(r['path']).is_file() for r in plan['rows'])
# All six before states, reviewed helpers, definitions, headers and input bindings
# pass before the first write. No other existing source path is permitted.
for row in plan['rows']:
    Path(row['path']).write_bytes(Path(row['after_snapshot']).read_bytes())
write(CONTRIBUTION,(RUN/'prospective-contribution-v2.json').read_bytes())
fixed(after=True)
write(RUN/'integration-materialized-v2.json',dict(exact_six_old_rows=plan['rows'],
    production=rows([MODULE]),Test=rows([TEST]),contribution=rows([CONTRIBUTION]),
    reader_proposal=rows([RUN/'reader-proposal-v1.json']),
    source_join=rows([CONTRACT/'qualified-source-reconciliation-draft-v4.json']),
    prior_review_conversion='Only approved six paths use exact preserved BEFORE snapshots and exact reviewed AFTER bytes; all other indexed RAW inputs remain immutable.',
    full_combined_gates='pending',site='pending',native_acceptance='pending',FINAL='pending',
    source_container_closed=False,chapter_complete=False,whole_Goal='active'))
print('Six exact reviewed transitions plus OWN scoped contribution materialized; combined gates pending.',flush=True)
