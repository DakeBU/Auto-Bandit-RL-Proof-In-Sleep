from common_v1 import *

fixed()
assert load(RUN / 'draft-types-and-API-v2-exit.json')['exit_code'] == 0
assert load(RUN / 'neutral-types-v2-exit.json')['exit_code'] == 0
targets = load(CONTRACT / 'targets-v2.json')['rows']
write(CONTRACT / 'source-statement-fingerprint-v2.json', load(RUN / 'active-source-statement-fingerprint-v2.json'))
obligations = load(CONTRACT / 'proof-obligations-draft-v2.json')
for row in obligations['obligations']:
    row['header_sha256'] = next(r['header_sha256'] for r in targets if r['id'] == row['id'])
write(CONTRACT / 'proof-obligations-current-draft-v2.json', obligations)
write(RUN / 'draft-metadata-correction-v2.json', dict(
    reason='Automated draft cloning preserved old per-header hashes in preliminary fingerprint/obligation copies.',
    operative_fingerprint=(CONTRACT / 'source-statement-fingerprint-v2.json').as_posix(),
    operative_obligations=(CONTRACT / 'proof-obligations-current-draft-v2.json').as_posix(),
    preliminary_not_operative=['source-fingerprint-v2.json', 'proof-obligations-draft-v2.json'],
    exact_targets_unchanged=True, before_blind_or_source_review=True))
draft = (RUN / 'draft-types-and-API-v2.lean').read_text(encoding='utf8')
neutral = (CONTRACT / 'neutral-context-v2.lean').read_text(encoding='utf8')
identities = []
for i in range(1,8):
    universes = 'u, v, w, z' if i == 1 else 'u, v'
    name = 'Q' + str(i).zfill(3)
    identities.append('example : DraftSeed.' + name + '.{' + universes + '} = NeutralSeed.' + name + '.{' + universes + '} := rfl')
write(RUN / 'actual-draft-neutral-identities-v2.lean', 'import Mathlib\n' + draft + '\n' +
    neutral.replace('import Mathlib\n', '', 1) + '\n' + '\n'.join(identities))
gate('actual-draft-neutral-identities-v2', 'lake', 'env', 'lean', RUN / 'actual-draft-neutral-identities-v2.lean')
write(RUN / 'draft-type-verification-v2.json', dict(actual_lean_exit=0, arbitrary_universe_prop_identities=7,
    public_proofs=0, headers={r['id']:r['header_sha256'] for r in targets},
    complete_neutral_definitions=3, compile_command_receipt='actual-draft-neutral-identities-v2-exit.json'))
native('reference-index-v2', 'reference-index')
native('list-lean-expectedFixed-v2', 'list-lean-decls', 'expectedFixed', '--statement')
fixed()
print('Actual seven arbitrary-universe draft-neutral identities compiled; ready for source-blind decoder.')
