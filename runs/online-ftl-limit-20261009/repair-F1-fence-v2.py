from common_proving_v1 import *
s=proving_fixed()
failure=load(RUN/'F1-safe-v1-exit.json')
assert failure['actual_exit']==1
f=load(RUN/'fences/F1-v1.json')
assert f['statement_hash']==s['targets'][0]['statement_hash']
write(RUN/'F1-fence-repair-v2.json',dict(failed_gate='F1-safe-v1',actual_exit=1,
    cause='source-assumption CLI expects literal source text retained in declaration/file; prose description absent there',
    repair='New fencev2 binds actual quantifier strings (y : ℕ → ℝ), (T : ℕ). Originalv1/log retained.',
    statement_hash_unchanged=True,theorem_body_unchanged_sha256=sha(PUBLIC),source_assumptions_weakened=False,
    mathematical_contract_version=1,semantic_reviewer_final_audit_required=True))
native('F1-repair-lifecycle-v2','lifecycle-event','--session',TASK,'--event','repair','--payload-json',
    json.dumps(dict(run_id=RUN.name,leaf='F1',failure='literal source-assumption fence configuration',
        theorem_compiled=True,statement_hash_unchanged=True,mathematical_target_changed=False)))
native('F1-fence-v2','statement-fence','--declaration',s['targets'][0]['name'],'--file',PUBLIC.relative_to(ROOT).as_posix(),
    '--source-assumption','(y : ℕ → ℝ)','--source-assumption','(T : ℕ)',
    '--output',(RUN/'fences/F1-v2.json').relative_to(ROOT).as_posix())
native('F1-safe-v2','safe-verify','--fence',(RUN/'fences/F1-v2.json').relative_to(ROOT).as_posix())
native('F1-proving-resume-v2','lifecycle-event','--session',TASK,'--event','proving','--payload-json',
    json.dumps(dict(run_id=RUN.name,leaf='F1',exact_contract_version=1,focused_compiled=True,
        literal_assumption_fence_ok=True,remaining_body_targets=4,package_accepted=False)))
print('F1 same body/hash build0 and corrected literal fence0; old failure retained.',flush=True)
