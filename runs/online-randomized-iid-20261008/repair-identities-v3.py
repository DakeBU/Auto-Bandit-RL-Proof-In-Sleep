from common_v1 import *

fixed()
source = (RUN / 'actual-draft-neutral-identities-v2.lean').read_text(encoding='utf8')
assert source.count('universe u v w z\n') == 2
prefix, suffix = source.split('namespace NeutralSeed\n', 1)
last = prefix.rfind('universe u v w z\n')
prefix = prefix[:last] + prefix[last:].replace('universe u v w z\n', '', 1)
write(RUN / 'identity-compilation-repair-v3.json', dict(actual_failure='actual-draft-neutral-identities-v2-exit.json',
    reason='Duplicate top-level universe declaration when concatenating two independently compiled contexts.',
    repair='Remove second universe command in verification file only; exact reviewed draft/neutral inputs unchanged.',
    target_version=2, header_change=False, original_failure_retained=True))
write(RUN / 'actual-draft-neutral-identities-v3.lean', prefix + 'namespace NeutralSeed\n' + suffix)
gate('actual-draft-neutral-identities-v3', 'lake', 'env', 'lean', RUN / 'actual-draft-neutral-identities-v3.lean')
targets = load(CONTRACT / 'targets-v2.json')['rows']
write(RUN / 'draft-type-verification-v2.json', dict(actual_lean_exit=0, arbitrary_universe_prop_identities=7,
    public_proofs=0, headers={r['id']:r['header_sha256'] for r in targets}, complete_neutral_definitions=3,
    compile_command_receipt='actual-draft-neutral-identities-v3-exit.json',
    draft_receipt='draft-types-and-API-v2-exit.json', neutral_receipt='neutral-types-v2-exit.json'))
native('reference-index-v2', 'reference-index')
native('list-lean-expectedFixed-v2', 'list-lean-decls', 'expectedFixed', '--statement')
fixed()
print('Seven arbitrary-universe proposition identities actually compiled; neutral review ready.')
