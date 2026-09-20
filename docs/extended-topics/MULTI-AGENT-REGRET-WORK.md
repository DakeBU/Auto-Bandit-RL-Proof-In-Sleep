# Actual coordination regret proof work

Source: Rosenski--Shamir--Szlak ICML2016, static Algorithm2 and supplement
A.1 Lemma4; pinned source and reviewed repair in MULTI-AGENT-CONTRACT.md.
Target: construct the actual collision-free reward sum from action s draw,
prove its deficit against any common n-arm set with means in [0,1] is at most
2*unfixedCount s, and integrate the actual state/draw laws to <=8*n^2.
DistinctFixed and FixedWithin are produced by the existing stateLaw support
invariants, not new stochastic assumptions. No independence of player waiting
times, no supplied regret charge, and no full unknown-N exploration claim.

Reuse search: bandit.py search-memory/list-lean-decls collision finds only the
existing MusicalChairs coordination definitions. Reuse action, CollisionFree,
DistinctFixed, FixedWithin, stateLaw_distinct/stateLaw_within, and finite
expected_unfixed_occupation_le. Mathlib finite sets: card_le_card_of_injOn,
card_image_iff, sum_image, sum_sdiff, sum_le_sum_of_subset_of_nonneg.
Decision: adapt existing common coordination kernel; scratch prototype first.

Proof route: a colliding fixed player's collision partner must be unfixed;
choose one partner per fixed collision. Distinct fixed actions make that map
injective, so colliding fixed count <= unfixed count. Successful fixed actions
inject into the common set. Missing comparator arms number at most twice the
unfixed count; each contributes <=1. Other successful players contribute
nonnegative means. Integrate this actual charge using finite PMF sums and the
previous occupation endpoint. Preserve real comparator subtraction; any
ENNReal ofReal adapter must establish nonnegative regret on supported draws.

Owner: scratch runs/extended-topics-20260920/MusicalChairsRegretPrototype.lean;
planned production Algorithms/MusicalChairsCoordinationRegret.lean after
independent blind/source review. Full learner and ICLR obligations remain open.

Promotion checkpoint: exact core moved into
BanditRLProof/Algorithms/MusicalChairsCoordinationRegret.lean with four
public-root Tests canaries and exact folded reader. Independent blind decoder
and source reviewer accepted the component with explicit scope delta and
verified exact-body promotion. Code commit:
0b853ce17188070a8b720ab24ce911b18941dca7. The oneFixed diagnostic is not reachable
from the two-player all-unfixed common-{0,1} law; the expected canary separately
uses the actual initial law. Fresh integration gates are recorded separately
in runs/extended-topics-20260920/multi-agent-regret-validation.json.
