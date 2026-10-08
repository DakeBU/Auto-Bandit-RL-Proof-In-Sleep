from common_v1 import *

fixed()
assert load(RUN / 'actual-draft-neutral-identities-v1-exit.json')['exit_code'] == 1
old = (RUN / 'draft-neutral-identities-v1.lean').read_text(encoding='utf8')
new = old
for i in range(1,9):
    q = 'Q' + str(i).zfill(3)
    before = 'example : DraftExpected.' + q + ' = NeutralExpected.' + q + ' := rfl'
    after = 'example : DraftExpected.' + q + '.{u} = NeutralExpected.' + q + '.{u} := rfl'
    assert new.count(before) == 1
    new = new.replace(before, after)
new = new.replace('example : DraftExpected.Q001.{u}', 'universe u\nexample : DraftExpected.Q001.{u}', 1)
write(RUN / 'draft-neutral-identities-universe-v2.lean', new)
write(RUN / 'draft-universe-repair-v2.json', dict(actual_original_exit=1,
    original_compiler_log_sha256=sha(RUN / 'actual-draft-neutral-identities-v1.log'),
    original_scratch_sha256=sha(RUN / 'draft-neutral-identities-v1.lean'),
    correction='Instantiate both closed polymorphic Props at the same explicit ARBITRARY universe u; retain all quantified objects and hypotheses.',
    not_restricting_to_Type_zero=True, eight_scoped_identity_checks_only=True,
    original_contract_headers_context_source_unchanged=True, public_theorem_body_failure=False,
    new_scratch_sha256=sha(RUN / 'draft-neutral-identities-universe-v2.lean')))
gate('actual-draft-neutral-identities-universe-v2', 'lake', 'env', 'lean', RUN / 'draft-neutral-identities-universe-v2.lean')
source = (RUN / 'audit-draft-context-v1.py').read_text(encoding='utf8')
start = "write(RUN / 'draft-type-verification-v1.json',"
assert source.count(start) == 1
tail = start + source.split(start, 1)[1]
tail = tail.replace('eight_closed_Prop_type_identities=True,',
    "eight_closed_Prop_type_identities=True, arbitrary_shared_universe='u', actual_identity_gate='actual-draft-neutral-identities-universe-v2',")
exec(compile(tail, str(RUN / 'audit-draft-context-v1.py') + ':universe-audit-resume-v2', 'exec'))
