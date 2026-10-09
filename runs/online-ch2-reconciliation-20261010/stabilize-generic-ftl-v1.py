from common import *
fixed()
leaf = CONTRACT / 'generic-ftl-v1'
review = RUN / 'generic-ftl-contract-review-v1.json'
assert sha(review) == '6a44aeae5531c470370f79e6812fdd161fbde8bcef5979b73f88ea52fd14526e'
decision = load(review)
assert decision['required_repairs'] == []
assert decision['verdict'] == 'accepted-with-explicit-delta'
assert sha(decision['report']) == decision['report_sha256']
assert sha(decision['input_manifest']) == decision['input_manifest_sha256']
inputs = load(decision['input_manifest'])['rows']
assert len(inputs) == 25
for row in inputs:
    assert sha(row['path']) == row['sha256'], row['path']
headers = load(leaf / 'frozen-headers-draft-v1.json')['rows']
targets = {row['declaration']: row for row in decision['target_verdicts']}
assert len(headers) == len(targets) == 9
for row in headers:
    normalized = ' '.join(row['exact_header'].split()).encode('utf8')
    assert hashlib.sha256(normalized).hexdigest() == row['normalized_header_sha256']
    assert targets[row['declaration']]['normalized_header_sha256'] == row['normalized_header_sha256']
assert sha(leaf / 'definition-context-v1.lean.txt') == '112847a69636cd98ea1413861fa77dd5d315493f8c591893b4166080674c6db2'
write(leaf / 'stabilized-v1.json', dict(
    state='stabilized', source_review=rows([review, decision['report'], decision['input_manifest']]),
    frozen_inputs=inputs, public_headers=headers,
    definition_context_sha256=sha(leaf / 'definition-context-v1.lean.txt'),
    first_leaf='BanditRL.OnlineFTLSelector.select_some_spec',
    allowed_production='NEW BanditRLProof/OnlineFTLSelector.lean; frozen definitions/imports/headers, actual BODY and necessary private helpers only',
    Tests='separate exact contract review required',
    BODY_accepted=False, chapter_complete=False, whole_Goal='ACTIVE'))
event('generic-ftl-stabilized-event-v1', 'stabilized', dict(
    leaf='generic-ftl-v1', evidence=(leaf / 'stabilized-v1.json').as_posix(),
    evidence_sha256=sha(leaf / 'stabilized-v1.json'),
    boundary='scoped journal records this reviewed freeze; runtime does not enforce the entire paper workflow'))
event('generic-ftl-proving-event-v1', 'proving', dict(
    current_leaf='BanditRL.OnlineFTLSelector.select_some_spec',
    dependencies=['four frozen definitions', 'Classical.choose_spec', 'Option.some.inj'],
    allowed_edits=['NEW production module frozen context and actual theorem BODY', 'OWN create-only evidence'],
    production_BODY='not yet authored at event time', chapter_complete=False))
fixed()
