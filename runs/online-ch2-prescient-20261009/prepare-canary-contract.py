from common import *
fixed()
assert sha(RUN/'canary-blind-receipt-v1.json')=='1cf2084a048c2b6bf2087b58e70e58c3d4d36d3de3d0b092a39cf83cb0c9ade2'
index=load(RUN/'neutral-canary-index-v1.json')
assert sha(RUN/'neutral-canary-types-v1.txt')==index['context_sha256']
assert sha(RUN/'neutral-types-v1.txt')==index['imported_definitions_sha256']
write(CONTRACT/'canary-targets-draft-v1.json',dict(stage='draft type-only before distinct source/CONTRACT review',targets=index['targets'],
    full_context_path=(RUN/'neutral-canary-types-v1.txt').as_posix(),full_context_sha256=sha(RUN/'neutral-canary-types-v1.txt'),
    imported_four_definitions_path=(RUN/'neutral-types-v1.txt').as_posix(),imported_four_definitions_sha256=sha(RUN/'neutral-types-v1.txt'),
    source_card_sha256=sha(CONTRACT/'source-card-v1.json'),production_contract_sha256=sha(CONTRACT/'stabilized-v1.json'),
    distinct_blind_receipt_sha256=sha(RUN/'canary-blind-receipt-v1.json'),
    objects='Five derived public Tests probes, not five printed results. Scalar actual Domain[-1,1] and unbounded Domain=R; fixed source-affine losses with vector6 at round0 and-1 thereafter; actual gradient identity from existing gradient_linear. Four production definitions reused exactly.',
    quantifiers='Closed concrete two-round numerical tests plus all-round/all-point actual affine-gradient identity, forall arbitrary future h with fixed current h0, and forall feasible comparator at horizon0. No supplied projection/regret certificates.',
    assumptions='Eta1/2 or1 positive. Comparator0 feasible. Initialcenter1 for two-round tests, explicitcenter3 outsideV for initialization/empty-horizon test. Unbounded wholeR is nonempty closed convex. Actual rangeT includes played prediction state(t+1), not priorstate.',
    conclusion='Active projection values/strict movement bound; formal counterexample to naive constrained negative ordinary-gradient-square substitution; unconstrained exact identity; current dependence with future exclusion; outsideinitial feasible projection plus T0 sharp API.',
    normalization='Constrained states1,-1,-1/2; regret-11/2; movement17/4; terminal1/4; correctsharpRHS-7/2; falsegradientRHS-17/2. Unconstrained states1,-2,-3/2; regret/energy identity-21/2. Emptyhorizon has no paid first prediction or movement despite independentfirstprediction being1.',
    information='Prediction0 receives currentg0; changing currentvector changes it, all later vectors arbitrary. Core forall-time inclusive prefix separately frozen. This is not ordinary strict-past online algorithm.',
    boundary='Derived operational probes for reviewed affine/Euclidean foundation. General full prescient source container/convex/Bregman/variable eta remains required/open. Naive gradient sign counterexample is NOT an author-endorsed correction or claim that the qualitative source remark is false. Initialcenter outsideV matches X=E source requirement. No package/chapter/wholeGoal completion.',
    owning_test_file=(ROOT/'Tests/OnlinePrescientLinearCanary.lean').as_posix(),
    allowed_future_scope='After separate review/version freeze only this new test file with exact interval/whole/signals definitions and5frozen headers/necessary explicit local projection arithmetic helpers. Roots/readers/other Tests/globalstate remain forbidden pending exact publication plans.',
    proof_status='No canary theorem body written/compiled. Production remaining6 proofs under lower work, not BODY/package accepted.',chapter_complete=False,whole_Goal_status='ACTIVE'))
paths=[CONTRACT/'canary-targets-draft-v1.json',CONTRACT/'source-card-v1.json',CONTRACT/'stabilized-v1.json',RUN/'neutral-canary-types-v1.txt',RUN/'neutral-canary-index-v1.json',RUN/'neutral-types-v1.txt',
    RUN/'canary-blind-reconstruction-v1.md',RUN/'canary-blind-receipt-v1.json',RUN/'contract-review-v1.json',RUN/'contract-review-v1.md',RUN/'first-leaf-BODY-review-v1.json',RUN/'first-leaf-candidate-body-v2.raw',
    ROOT/'BanditRLProof/OnlineGradientDescentSource.lean',PDF]
paths += [RUN/f'source-pdf{n}.{ext}' for n in [26,277,278] for ext in ['txt','png']]
write(RUN/'canary-CONTRACT-review-inputs-v1.json',dict(rows=rows(paths),stage='ONLY canary types/source semantics; production current proof file not frozen input because sequential lower continues under exactprefix permission',
    fixed_import_context='Exact4definitions in neutral-types + first BODY accepted immutable snapshot; actual production prefix maintained separately',compilation_claim=False,chapter_complete=False,whole_Goal_status='ACTIVE'))
fixed();print('Five canary contracts/roundtrip source packet ready; no Test/root edits or compilation claim.')
