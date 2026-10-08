# Ambient completed-information real versions and original IID excess

Task id: `ONLINE-COMPLETED-CAUSAL-20261008`
Kind: `completed-causal-producer`
Status: `planned`
Harness: `hierarchical`

## Goal

State the bandit/RL theorem, definition, or literature-port target.

## Source

- Paper or repository:
- Theorem/lemma/section:
- Existing Lean declaration:
- Textbook/source card:
- Scenario card:

## Lean Target

```lean
-- target declaration names here
```

Target file: `BanditRLProof/OnlineGuessingCompletedCausal.lean`

## Proof Obligations

- [ ] Natural-language statement is mapped to Lean symbols.
- [ ] Required model assumptions are explicit.
- [ ] Probability, measurability, concentration, and stopping-time contracts are recorded.
- [ ] Reusable theorem cards are identified before proof search.
- [ ] Each active leaf has local APIs, intended proof route, and regularity contracts.
- [ ] General leaves are classified as `mathlib-candidate`, `project-local`, or `theorem-card-only`.
- [ ] `lake build && lake build Tests` passes.

## Mathlib-Ready Leaf Contract

| Leaf | Local APIs/imports | Intended proof route | Regularity contracts | Mathlib status |
| --- | --- | --- | --- | --- |
| root | TBD | TBD | TBD | project-local |

## Retrieval Cards

- LML cards:
- Mathlib cards:
- Textbook cards:
- Scenario cards:

## Trial Logging

```bash
python3 tools/bandit.py trial-log --task ONLINE-COMPLETED-CAUSAL-20261008 --role lower --kind attempt --status running --notes "..."
python3 tools/bandit.py trial-summary
```


## Draft4 derived completion targets

# Ambient completed-information bridge: draft contract v1

Pinned source: Orabona arXiv:1912.13213v10, 2026-06-21; SHA256 cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17. Printed1/PDF13 states the IID squared-loss variance benchmark, Eqs1.1/1.2, and nonnegative excess. Printed3/PDF15 distinguishes strict-past information from inaccessible hindsight. Four proposed declarations are derived formalization infrastructure and specializations, not four printed book theorems. Source round1 corresponds to Lean time0.

For an arbitrary ambient measure mu and arbitrary sigma field F on Omega, define its ambient null augmentation exactly by the pinned mathlib eventuallyMeasurableSpace F (ae mu): each member differs modulo ambient-mu AE from an F-measurable set. This includes subsets of ambient null sets. It is not automatically the completion of mu.trim F; no equivalence with that different construction is claimed. The core target produces an actual F-measurable real version of any real P measurable for this augmented sigma field, with equality for ambient mu. No probability, finiteness, F below the ambient sigma field, or countability/standard-Borel assumption on Omega is needed. Real output regularity is essential to the countable coding/measurable inverse route; no arbitrary-codomain claim is made.

The three terminal adapters assume F_t below private seed plus strict past, and measurability of the original P_t for this ambient augmentation. They may not assume the AE-version conclusion or supplied current-target independence. The actual core version supplies AEStronglyMeasurable[F_t] under the same ambient measure, then reuses the three immutable accepted AE causal producers from PR198. The bounded-policy terminal preserves original predictions AE in[0,1] at every natural time, globally feasible chosen policies on every input, and one same-process AE event for all natural times, before all horizons. Original off-null values may be noncausal and outside the interval. This is a classical law-relative representation, not an executable unknown-law learner.

Current-target independence uses joint independent measurable targets and a measurable private seed independent of the entire infinite target stream; no IID/support/boundedness or prediction-integrability assumption is added to that terminal. The IID endpoint additionally uses identical laws, AE unit targets/predictions and probability measure; it compares the original infinite process with the minimum of expected fixed unit-comparator losses outside expectation. The population mean is analysis-only. The exact cumulative identity and nonnegativity hold for every natural horizon including T0; there is no division by zero, rate, convergence, pathwise or high-probability upgrade.

Default single lower route: code P using the pinned measurable embedding of real into countably many Bool coordinates; obtain one F-measurable representative set for each coordinate from the actual augmented-field hypothesis; intersect the countably many AE equalities, and decode with the measurable left inverse. This must be an actual producer proof, not a version existence premise. All four exact Lean headers must survive proof repair unchanged.

Canary: reuse the positive-variance, random-private-seed IID model whose badPrediction accesses the current target only on a nonempty null event. Establish actual augmented-field measurability directly from its ordinary causal version and AE equality, retain proofs of not ordinary pointwise predictable and not everywhere unit, and instantiate all four new targets on the original bad process. Preserve nonzero two-round excess1/2 and T0; no scalar-normalization/convergence claim.

Only four derived completion obligations may close after actual gates. This package can close the precisely defined ambient-null-augmentation-to-real-version gap, not every other notion of completed information or a general causal stochastic-kernel realization. The kernel realization remains REQUIRED. Original16 Chapter1 source objects and null unknown proof total, all other Chapter1/2 targets, unenumerated Chapters3-16 and required appendices remain required. Whole Goal ACTIVE; PR198 remains OPEN draft and unmerged. Main/live unchanged. Pinned Lean/mathlib, old theorem bodies, old Book IDs/URLs and source snapshots remain intact.

Exact targets/DAG in docs/contracts/online-completed-causal-v1. L1 dependency-ready; L2/L3/L4 await L1. Type syntax checked; no theorem body or terminal compiled. Contract source/semantic review REQUIRED.
