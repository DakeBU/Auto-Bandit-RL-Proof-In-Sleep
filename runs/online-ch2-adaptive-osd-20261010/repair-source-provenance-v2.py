from common import *

review = RUN/'potential-CONTRACT-review-v1.json'
r = load(review)
assert sha(review) == 'd28d039513dd8daf1a8d43dcf0a311fd80fe3fcbfc994ae7b6d6289c552fb88c'
assert sha(r['report']) == '85522c1794bf0f060b148e30ca5f794f3e2213a48e4d7cb5a5f9e7f7d7640038'
assert r['verdict'] == 'rejected' and not PUBLIC.exists()
for row in load(r['input_manifest'])['rows']:
    assert sha(row['path']) == row['sha256'], row['path']
original = (CONTRACT/'source-card-v1.md').read_text(encoding='utf8')
parts = original.split('\n\n')
assert parts[3].startswith('Proof-display issue for independent review:')
parts[3] = ('Operative proof-display reading, superseding the rejected v1 interpretation: '
    'printed14/PDF26 already multiplies (1/eta_(t+1)-1/eta_t) by '
    'norm(x_(t+1)-u)^2/2. The factor1/2 is outside the parentheses in the distance fraction. '
    'Thus moving it into w=1/(2eta) is equivalent algebra, not a correction to the source. '
    'The proposed missing-half allegation and its claimed counterexample are withdrawn. '
    'The original printed equality, Theorem2.13 terminal, header and pinned PDF remain unchanged. '
    'Retain source-proof-display-correction-proposed-v1 and the independent rejected review as historical failure evidence; '
    'source-proof-display-retraction-v1 records the corrected attribution.')
write(CONTRACT/'source-card-v2.md', '\n\n'.join(parts).replace(
    '# Pinned source and current preparatory leaf', '# Pinned source and current preparatory leaf: operative v2', 1))
write(CONTRACT/'source-proof-display-retraction-v1.md', '# Retraction of a mistaken source correction\n\n'
    'The source-review actor personally viewed PDF25/26 originals and rejected the v1 missing-half proposal. '
    'Root then reread the same ORIGINAL PDF26 image and confirmed norm(x_(t+1)-u)^2/2 is already printed '
    'outside the reciprocal-difference parentheses. The source is correct at this step. '
    'The v1 allegation and purported counterexample are withdrawn, not treated as an Orabona erratum.\n\n'
    'For distances[0,1,1],steps[1,1/2], the ACTUAL printed expansion is '
    '0-1+(2-1)*(1/2)=-1/2, exactly the original potential sum. The value0 in v1 evaluates '
    'a mistranscription without the printed /2. The example does not refute the PDF. '
    'The original incorrect proposal, original source-card-v1, exact source images and rejecting '
    'potential-CONTRACT-review-v1 remain unedited.\n\n'
    'Only source attribution/narrative is repaired. The exact potential header/context and Theorem2.13 '
    'terminal are unchanged. Zero weights remain an explicit algebraic generalization requiring the '
    'later actual adaptive-OSD consumer. Future minimum-versus-infimum concerns remain separately required; '
    'this retraction neither proves nor dismisses those. WholeGoalACTIVE.\n')
write(CONTRACT/'potential-contract-draft-v2.md',
    (CONTRACT/'potential-contract-draft-v1.md').read_text(encoding='utf8')+
    '\n## Operative source version and retained rejection\n\n'
    'Operative source-card-v2 plus source-proof-display-retraction-v1 supersede only the rejected source '
    'reading in v1. No source erratum is claimed for printed14. Header/context/fingerprint v1 remain '
    'identical and mathematical terminal accepted separately in the rejected combined v1 review. '
    'The v2 source binding needs favorable review before stabilization or proving.\n')
capture('potential-contract-rejected-trial-v1', sys.executable, '-B', '-X', 'utf8', RUN/'native-scoped.py',
    'trial-log', '--task', TASK, '--role', 'reviewer', '--kind', 'review', '--status', 'rejected',
    '--run-id', RUN.name, '--attempt-id', 'potential-contract-v1', '--progress-class', 'diagnostic',
    '--reviewer-validated', '--obligations-before', '1', '--obligations-after', '1',
    '--notes', 'Source-proof display was misread: original distance fraction already has /2. Mathematical header unchanged; no BODY permitted until versioned provenance repair reviewed.',
    '--verifier-evidence', review.as_posix())
event('potential-source-repair-event-v2', 'repair', dict(current_leaf='weighted_potential_sum',
    rejected_review_sha256=sha(review), operative_source_card_sha256=sha(CONTRACT/'source-card-v2.md'),
    source_reading='Original printed equality already includes half in distance fraction; no source erratum.',
    frozen_header_unchanged=True, mathematical_BODY_started=False, whole_Goal='active'))
write(RUN/'potential-CONTRACT-packet-v2.md', '# Versioned source-provenance repair review\n\n'
    'Resolve v1 required repairS1 using operative source-card-v2, source-proof-display-retraction-v1 and '
    'potential-contract-draft-v2. Original source/proposal/card/rejected-review remain unchanged. '
    'Rebind exact SAME mathematical header/context/fingerprint and existing complete neutral reconstruction; '
    'no new decode is needed for an attribution-only repair. Confirm source PDF26 has /2 and no author erratum '
    'or terminal weakening is claimed. Native rejected review1->1 and repair event transport actual earlier '
    'judgment; no mathematical BODY exists.\n\n'
    'OutputONLY potential-CONTRACT-review-v2.md/json: verdict/required_repairs/report+sha/input_manifest+sha, '
    'all RAW before/after, S1resolution and header/context unchanged. If favorable authorize only NEW '
    'BanditRLProof/OnlineAdaptivePotential.lean exact context/header/BODY; no algorithm/roots/Test/readers/pins. '
    'Keep rejected source proposal and bootstrap operational failure. WholeGoalACTIVE; causal parent required draft. '
    'UTF8write_bytes singleLF. No proving or mutation by reviewer.\n')
paths = [Path(x['path']) for x in load(RUN/'potential-CONTRACT-inputs-v1.json')['rows']]
paths += list(RUN.rglob('*'))+list(CONTRACT.rglob('*'))
write(RUN/'potential-CONTRACT-inputs-v2.json', dict(rows=rows(paths),
    mathematical_header_changed=False, operative_source_card=sha(CONTRACT/'source-card-v2.md'),
    rejection_retained=sha(review), scope='Versioned source attribution repair; original false proposal retained.'))
print('Source-provenance v2 prepared; no proof BODY.', flush=True)
