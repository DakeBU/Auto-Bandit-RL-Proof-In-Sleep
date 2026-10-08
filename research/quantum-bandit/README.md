# Quantum Bandit A+B: executable research checkpoint

Date: 2026-10-09. Status: **kernel-checked prototype increment, publication draft**.
Neither project A nor project B is proved complete. No regret advantage, optimality,
mixed-fidelity optimality, finite-bit implementation, or global novelty is claimed.

## Frozen inputs and safe ownership

| Repository | Frozen upstream source | Toolchain | Ownership |
|---|---|---|---|
| BanditRLlib | `6847b678a73db68dee5101d6f05c2453c1405afc` | Lean 4.29.1 | `research/qb261009`, isolated worktree |
| QuantumComputinglib | `305952f4291d7be530c76f51f7e98d77faf1cf45` | Lean 4.29.1 | `research/qb261009`, isolated worktree |
| Mathlib | `5e932f97dd25535344f80f9dd8da3aab83df0fe6` | pinned by both manifests | same compatible dependency |
| Samplinglib | fetched remote `c05de12e6a8ca7af8ce2df8608836f8d4e90f617` | Lean 4.33.0 | inspected only; not a compiled dependency |

The original Bandit/Sampling/Quantum checkouts were not reset, rebased, checked out,
or edited. The original quantum collaborator branch advanced during this task;
that work is outside this freeze. No main merge or website deployment occurred.
Local paths are `C:/qb261009/bandit`, `C:/qb261009/quantum`. This small Lake project
uses relative path dependencies: Bandit repository two levels above and its quantum
sibling. Clone the two frozen branches with that layout to reproduce it. Shared local
Git objects and package junctions are cache conveniences, not theorem premises.

## Literal access and cost contract

The proposed final model is **FC-WO-reset-v1**. Arms are chosen classically at block
boundaries using classical history. A block starts with a fresh normalized register,
uses one fixed arm's unknown unitary or its matching dagger a total of at most D times,
intersperses specified known unitaries, measures once at its end, and discards every
quantum register. Classical history persists; quantum memory does not. Adaptation
inside the block and coherent queries across arm indices are outside this model.

Every forward **and inverse** oracle use consumes one unit of T and charges that arm's
gap. Shots are blocks. Physical primitive gates, known-gate synthesis, physical depth,
state loading, classical processing and wall-clock cost remain separate. No reflection
about an unknown state, controlled unknown oracle, or unknown mean angle is free.
The present code proves single-block circuit semantics and deterministic accounting;
the actual reset/measurement stochastic history producer remains open.

B fixes each implemented circuit and matching inverse at a fidelity. Its target mean
bias is systematic. Noise that changes between oracle invocations requires a separate
model and is not covered by these perturbation proofs. Quantum-estimate confidence
events do not imply independent, unbiased or sub-Gaussian estimation errors.

## What the checked mathematics says

Write p(U)=Re⟨Uψ,P Uψ⟩ with ‖ψ‖=1, complex finite Euclidean matrices, Loewner
0≤P≤I, and the induced L2 operator norm. Both U and V are actual unitaries.
The effect contraction ‖P‖≤1 and output normalization are proved internally.
Split the quadratic-form difference into
⟨(U−V)ψ,P Uψ⟩+⟨Vψ,P(U−V)ψ⟩. Cauchy–Schwarz and the operator bound yield
|p(U)−p(V)|≤2η when ‖U−V‖≤η. The same semantics proves 0≤p(U)≤1.
Mathlib's scoped matrix instances are assembled into a proof-local CStarAlgebra;
this does not add a mathematical assumption to the public theorem.

For positionally aligned primitive lists, the existing Ry perturbation theorem gives
operator error at most mδ/2. The new Born consumer therefore derives reward bias≤mδ.
The alignment certificate is an explicit input: wire identity, gate ordering and
angle matching are not synthesized. m counts all primitive instructions, so the bound
can be conservative. Exact-real angles remain distinct from finite-bit compilation.

A chronological query word is evaluated by later instructions multiplying on the left.
Known instructions are identical in both environments. Telescoping with unitary
prefix/suffix factors gives error≤qη; dagger perturbation uses star isometry. Here
q=forwardCount+inverseCount is an exact proved equality. The Born error is≤2qη.
Concrete primitive-list expansion executes this word and has exactly
`knownGates + q * oracle.length` primitive gates, including the reversed dagger.
The joint adapter uses the same word's counts to construct the charged arm block.
The list expansion of those blocks is proved equal to the existing real-mean regret
and gap-weighted pull-count formulas at the consumed query horizon. Arbitrary padding
beyond that horizon has no role in those equalities. Horizon clipping is still open.

For final computational-basis measurements, probabilities are the squared coordinate
norms and normalization is derived from unitary output norms. With the **unhalved**
Hellinger convention, reverse triangle plus the Euclidean norm identity proves
H²≤‖x−y‖²≤q²η²≤Dqη². This is a genuine single-block information ingredient;
it is not an adaptive lower bound, and it does not yet treat arbitrary POVMs.

On a supplied good confidence event, interval elimination retains tied optima and
removes an arm once its gap exceeds four times the common radius. Fixed circuit bias
b and statistical radius s compose as b+s. A fixed-enumeration exact-real argmax
returns an ε-optimal arm when b+s≤ε/2 for every arm. Finite bad-event unions require
no independence. The joint failure-bound theorem derives the circuit bias and invokes
that actual argmax; its per-arm statistical tail bounds remain explicit premises of
a **conditional transport leaf**, never an unconditional quantum algorithm theorem.
The measure in that transport is arbitrary: probability normalization and measurable
algorithm histories must be established by the eventual producer.

## Declaration and verification map

| Claim | Actual Lean declaration | Source/dependencies | Status |
|---|---|---|---|
| Born probability range/stability | `QuantumBlockEncoding.BornStability.probability_mem_Icc`, `probability_difference_le` | P0 finite-dimensional refinement; Mathlib effect order/inner products/unitary maps | compiled |
| aligned circuit reward bias | `QuantumBlockEncoding.CircuitRewardBias.aligned_reward_bias_le` | existing `aligned_eval_distance_le`, actual circuit unitarity, Born stability | compiled conditional on alignment |
| forward/inverse query telescoping | `QuantumBlockEncoding.QuantumQueryWord.eval_distance_le`, `queryCount_eq`, `probability_difference_le` | chronological instruction semantics/unitary products/star norm | compiled |
| actual gate count and evaluator link | `QuantumBlockEncoding.QueryCircuitCost.expanded_length`, `expanded_semantics` | primitive list expansion and existing dagger/append semantics | compiled prototype; seal chronology gap |
| genuine basis information bound | `QuantumBlockEncoding.BasisHellinger.bounded_word_hellingerSq_le` | actual basis normalization, reverse triangle, query telescoping | compiled; basis-only |
| confidence/elimination/recommendation | `BanditRLProof.QuantumConfidence.optimal_survives`, `large_gap_removed`, `recommend_fixed_fidelity_failure_bound` | existing finite argmax/union bounds; supplied estimation tails | compiled conditional transport |
| real regret/pull-count compatibility | `BanditRLProof.QuantumQueryAccounting.chargedRegret_eq_realMeanRegret`, `chargedRegret_eq_gap_pullCount` | actual query-list expansion and existing RealMeanRegretPullCount | compiled deterministic accounting |
| actual cross-library chain | `BanditRLProof.QuantumBanditAdapter.aligned_circuit_confidence_transport`, `circuit_certified_recommendation_failure_bound`, `chargedBlock_queries` | imported compatible quantum theorems plus Bandit confidence/accounting | compiled conditional transport |

Focused commands run on the real sources:

```text
# C:/qb261009/quantum
lake build QuantumBlockEncoding.BornStability QuantumBlockEncoding.CircuitRewardBias ABEISTests.QuantumBanditBornCanary
lake build QuantumBlockEncoding.QuantumQueryWord ABEISTests.QuantumQueryWordCanary
lake build QuantumBlockEncoding.BasisHellinger ABEISTests.BasisHellingerCanary
# C:/qb261009/bandit
lake build BanditRLProof.QuantumQueryAccounting Tests.QuantumConfidenceCanary
# this directory
lake build Canary
lake exe dependency_export evidence/proof-term-graph.json
```

The joint executable canary reports five actual primitive gates for a two-query word
with a specified known gate; the inverse is charged. The noncommuting Ry–CX–Ry canary
consumes an existing alignment proof to derive bias plus statistical radius.
Reported root axioms are `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`
or new source axiom is admitted. Aggregate gates and exact failures are recorded in
`evidence/validation.json`, with raw logs retained in `C:/qb261009/evidence`.

`evidence/proof-term-graph.json` is extracted from compiled declaration type/value
constants. It distinguishes type edges from proof-only value edges and records the
external boundary. Module imports are a separate array, not asserted implications.
Paper proof/construction routes and unproved estimator/lower-bound leaves stay separate
from this actual Lean dependency slice. Source/source-hash inventories and independent
seven-slot reports are in `evidence/`.

## Nearest prior work and the remaining research claims

The pinned audit is [literature-audit.md](evidence/literature-audit.md). The depth
tradeoff is already supported by [Erle–Koczor, Theorem 1](https://arxiv.org/html/2608.24434v1#Thmtheorem1).
Uniform horizon-independent O(K) regret is incompatible with
[Liu–Li–Lui, Theorem 8](https://arxiv.org/html/2608.14319v1#Thmtheorem8); soft-O notation
must retain the essential horizon logarithms. The fresh inaccessible-randomness
[quantum-channel oracle](https://arxiv.org/html/2301.08544v4) differs from a fixed reversible
oracle within reset blocks. Bias-radius composition and cost allocation already have
[classical multi-fidelity BAI prior art](https://arxiv.org/html/2406.03033v2).

The NeurIPS 2026 [memory-decoherence](https://neurips.cc/virtual/2026/poster/154155) and
[limited-adaptivity](https://neurips.cc/virtual/2026/poster/148383) official abstracts were
checked. Their full theorem PDFs were unavailable in this audit. Consequently exact
formal model separation and any final novelty verdict remain unresolved.

External Lean resources are pinned in [inventory-external.md](evidence/inventory-external.md).
QuAIR/Lean-QIT-Bench, Timeroot/Lean-QuantumInfo, Hayata-Yamasaki-Group/lean-quantum and
openai/math have different toolchains/licenses/placeholders as recorded. **All remain
candidate nodes**: none is assumed as a local theorem. Existing HOO reward-process MGF
proofs cannot be applied to arbitrary quantum estimation outputs.

The next ordered leaves are:

1. Freeze exact signatures before proof search for a projector-based estimator with
   implemented known reflections, real forward/inverse counts, D=1 handling, fresh shots,
   integer cap and conditional confidence for every classical history. General effects
   require a costed dilation; the present effect stability theorem does not supply it.
2. Construct the finite-horizon A policy with dyadic stages, summable confidence budgets,
   interruption at T, ties, K>T and failed-estimation expected regret. Then close the
   gap-dependent upper bound and its gap-free split. Current soft bounds are speculative.
3. Construct B's feasible finite fidelity selector and ε-BAI policy. Include integer
   rounding, infeasible/empty levels, known gates and actual statistical producers before
   claiming ΣΦ complexity. Evaluate genuine precision/coherence/cost optimization beyond
   the known bias-radius lemma; mixed-fidelity optimality is unproved.
4. Extend the basis bound to arbitrary allowed measurements; produce concrete hard
   two-environment oracles with controlled unitary distance; prove adaptive reset-history
   information accumulation, stopping and bandit-to-testing reduction. No matching
   Ω(√(KT/D)) theorem is presently local.
5. Resolve strict publication/seal coverage debt and complete current-source content-bound
   reviews and all repository integration gates before any publication proposal.

## Independent review and publication boundary

The author, source-blind decoder and source reviewer are distinct agents. The decoder
uses only formal statements/definitions/proof terms with comments removed. The reviewer
compares the source seals and original task against that reconstruction. Both reports
preserve packet hashes and historical differences; current-source checks are separate.

The reviewer records a real protocol gap: concrete primitive gate-cost expansion was
introduced during implementation beyond the original abstract query-word seal. It is
not retrospectively sealed or represented as publication-admitted. Other prose seals
also do not bind every final module by exact pre-proof signature digest. These useful
verified increments are retained as prototypes. Strict contributor/publication admission
therefore remains draft; no fabricated accepted identity or green registry is created.

Canonical taxonomy/technique families remain unchanged because this increment introduces
no new accepted quantum regret/BAI theorem. The existing horizon-independence Frontier
resolution remains an external preprint result, not a newly ported proof. The joint
actual dependency slice is updated; candidate algorithm and source edges stay dashed.
No bound/source atlas or compressed spine is promoted. This is a recorded
`no-change-with-reason`, not a claim that the open research roots were discharged.
