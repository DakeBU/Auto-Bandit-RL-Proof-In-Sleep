# CH13-MOSS-UPPER — source-faithful MOSS upper dependency

Problem id: `CH13-MOSS-UPPER`

Parent task: `TEXTBOOK-PART-IV-CHAPTER-13-BASIC-LOWER-BOUND-SPINE`

Status: mathematical dependency compiled and accepted through PR #105,
main run 33953476610, Pages job 101275173069 and live b38630c checks.
Not an open mathematical conjecture. Final status-record publication is
tracked separately from the accepted mathematical dependency.

## Source and frozen target

Lattimore–Szepesvári, *Bandit Algorithms*, Algorithm 7 and Theorem 9.1,
author-online pp. 123–127 / physical PDF pp. 132–136, referenced by the
Chapter 13 main-prose near-minimax claim. Source:
<https://tor-lattimore.com/downloads/book/book.pdf>.

For finite k-armed 1-subgaussian reward laws, Algorithm 7 initializes by
pulling every arm once and then maximizes
`empiricalMean_i + sqrt (4 / s * log (max 1 (n / (k*s))))`, where s is
that arm's previous pull count. The source upper target is
`expectedPseudoRegret n <= 39 * sqrt (k*n) + sum_i gap_i`.
Use k>0 and n>=k for the full initialization contract. Any n<k extension
must explicitly define the truncated initialization rather than silently
claiming the source policy is already specified there.

The final Chapter 13 consumer must use a single admissible policy and the
same finite-arm history/reward-law model as its minimax regret functional.
On gaps in [0,1], the additive gap sum is at most k, and n>=k absorbs
this into sqrt(k*n). A Gaussian-subclass lower transfer alone is insufficient.

## Current Lean status and retrieval boundary

The initial 2026-09-05 search found no MOSS algorithm or upper endpoint.
That historical gap is now discharged by the complete fixed-horizon route:
`MOSS.canonicalGapExpectedRegret_le` proves the exact constant 39 on the
same canonical history law as the lower bound, and
`LowerBounds.moss_nearMinimax` proves the broad-class factor 2160 via a
regret-preserving Gaussian subclass embedding. Both typed canaries compile
with baseline axioms only. The full pre-merge check at cdc3a51 passed;
merged-tree and PR/publication checks remain separate.

Initialization uses T<=1+kappa. A sharp expected-count bound removes the
source estimate's loose additive one, preserving exactly one gap sum in
Theorem 9.1. The class restricts gaps, not absolute means. This does not
close an anytime MOSS theorem.
In particular, `ConcentrationQuadraticMaximal.lean` explicitly uses a finite
union bound and is not the no-extra-log Doob bound needed by Theorem 9.2.
The exact Gaussian Eq. (13.1) is separately compiled at commit `1203c63`
and does not discharge this dependency.

Theorem cards involved: `TXT-LATTIMORE-SZEPESVARI-2020`,
`SCN-STOCHASTIC-FINITE`; any Mathlib retrieval must record exact declarations
and distinguish probability prerequisites from algorithm/history integration.

## Historical dependency route (now compiled)

1. Define the exact real-valued MOSS radius and score, including initialization
   and a measurable finite argmax policy. Do not use the old rational UCB
   placeholder score as the algorithm.
2. Prove the deterministic selection implication: if the optimal arm's index
   is at least `muStar - deficit` and the selected arm has gap greater than
   `2*deficit`, its index exceeds its own mean plus half its gap. This is now
   compiled as `selected_index_gt_mean_add_half_gap`; it is not an
   expected-regret theorem.
3. Theorem 9.2: derive the finite-time maximal subgaussian partial-sum tail
   via an exponential submartingale/Doob argument, without a union-bound
   cardinality factor. Explicitly include positive variance and threshold.
   This route now compiles in `ConcentrationMartingaleMaximal.lean`, including
   an independent centered coordinate producer on the natural filtration.
   It has no assumed tail-probability premise. Instantiate it on the actual
   centered reward stream via the compiled MOSSCanonicalReward module.
4. Lemma 9.3: dyadic peeling and its summation/integration estimate give
   `P(exists s>=1, mean_s + sqrt(4/s*logPlus(1/(s*delta))) + gap <= 0)
   <= 15*delta/gap^2`, for 0<delta<1 and gap>0. Finite-prefix versions may
   suffice for the horizon-n consumer, but retain the required constants.
5. Integrate the clipped tail to bound expected optimal-arm index deficit;
   prove the large-gap occupancy estimate using the source Lemma 8.2 route.
   Account separately for each initialization pull (the additive gap sum).
6. Assemble Theorem 9.1 in the concrete policy model, then transport its
   upper bound to the Chapter 13 broader-class minimax consumer.

## Acceptance gate

Concentration retrieval used by the now-compiled maximal bound: pinned Mathlib
`Probability/Martingale/OptionalStopping.lean:157` provides
`MeasureTheory.maximal_ineq` for a nonnegative submartingale, with NNReal
threshold times the finite-sup event probability bounded by its terminal
restricted integral. Conditional Jensen now produces the exponential
submartingale, and the natural-filtration independence bridge produces the
centered partial-sum martingale. The compiled Lemma 9.3 peeling theorem
consumes this result and preserves its constants; the maximal bound alone
would not suffice for the MOSS optimism-deficit tail theorem.

Next smallest work item: publish the final synchronized completion records.
Merged-tree verification, structured self-review and PR/main/Pages/live
checks pass. No mathematical leaf is missing from this packet's frozen target.

Typed external canaries for the concrete algorithm, maximal tail, peeling,
and source-constant regret endpoint; root and Tests build; axiom scan;
full harness check; source/assumption review; synchronized proof export,
retrieval/blueprint memory and website. Conditional deterministic or
tail-assumed wrappers must remain labeled as such and cannot close this gate.
Keep Chapter 13 `partial` until the connected consumer and chapter completion
contract pass. Notes/exercises are optional and are not a substitute blocker.
