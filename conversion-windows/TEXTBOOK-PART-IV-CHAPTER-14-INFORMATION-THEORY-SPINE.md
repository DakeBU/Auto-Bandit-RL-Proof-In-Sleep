# Conversion Window: Textbook Part IV Chapter 14 information-theory spine

Task id: `TEXTBOOK-PART-IV-CHAPTER-14-INFORMATION-THEORY-SPINE`

Source card: `TXT-LATTIMORE-SZEPESVARI-2020`

Scenario card: `SCN-STOCHASTIC-FINITE`

## Source placement and status fence

The canonical source is Lattimore--Szepesvári, *Bandit Algorithms*, CUP 2020,
Part IV, Chapter 14, author-version pp. 186--197 / physical PDF pp. 195--206
(CUP edition pp. 160--169).  The whole-chapter body window is §14.1--§14.2,
author-version pp. 186--191 / physical PDF pp. 195--200. Equation (14.4)
defines discrete relative entropy, Eq. (14.5) gives the finite-discretisation
definition on arbitrary measurable spaces, Theorem 14.1 gives the RN/log-
likelihood representation, Eq. (14.6) gives the common-density formula, and
Theorem 14.2/Eq. (14.7) is Bretagnolle--Huber.

The previously accepted lower-bound spine formally targeted §14.2 only.  That
scoped gate remains valid, but it is insufficient for whole-chapter completion.
Section 14.1 coding definitions and Eqs. (14.1)--(14.3) are now required body
rows.  Notes and exercises remain optional.  Exercise 14.10 is now compiled in
its full arbitrary-sub-sigma-algebra form; the local event version remains a
separate dependency leaf.

## Whole-chapter status fence

- Required body: opening motivation, §14.1, §14.2, and the displayed proof and
  application claims through Eq. (14.9).
- Optional: §14.3 Notes, §14.4 Bibliographic Remarks, §14.5 Exercises.
- Promotion rule: every required mathematical definition and claim must map to
  a compiled local declaration and typed canary.  A theorem card, imported API,
  conditional lemma, or prose mapping alone cannot promote the chapter.
- Current decision: `partial`. Main Huffman, common-density, overlap and
  Gaussian terminals are compiled and fully gated. The constructed arithmetic
  code rate theorem passed its full gate at 2a31a01. Supporting non-metric,
  cross-entropy and fixed-length adapters passed the d325147 gate.
  Additional body assertions and current export/site closure are audited in
  `reviews/2026-09-05-chapter-14-body-closure-audit.md`; historical site/review
  rows below do not certify this expanded scope.

## Precise restatement

For a finite source alphabet, a binary prefix code assigns distinct nonempty
bit strings with no distinct codeword prefixing another.  Its expected length
is the probability-weighted codeword length.  Natural entropy is
`∑ₓ pₓ log(pₓ⁻¹)` and base-two entropy divides this by `log 2`.  The local
surface proves the induced codebook uniquely decodable and hence its Kraft
inequality. The recursive Huffman constructor is globally optimal. A named
arithmetic interval-address block-code family with a zero-mass escape tag
has expected rate tending to entropy; its full gate passed at 2a31a01.

For probability measures `P,Q` on `(Ω,F)`, relative entropy is infinite when
`P` is not absolutely continuous with respect to `Q`. In the finite regular
branch it is the `P`-integral of the log likelihood ratio. For Bernoulli laws,
this reduces to `p log(p/q) + (1-p) log((1-p)/(1-q))`, with zero-mass terms
equal to zero and support mismatch equal to infinity.

For every measurable event `A`, Theorem 14.2 lower-bounds the sum of the two
hypothesis-testing errors, `P(A)+Q(Aᶜ)`, by one half times the exponential of
negative `D(P,Q)`. If `D(P,Q)=∞`, the right-hand side is zero. The statement
is direction-sensitive even though the source notes that a second application
with `D(Q,P)` is also valid.

## Lean mapping

| Source symbol | Meaning | Lean declaration | Type / role | Status |
| --- | --- | --- | --- | --- |
| finite binary prefix code | injective nonempty codewords with prefix freedom | `LowerBounds.BinaryPrefixCode` | typed source model | compiled |
| Kraft inequality | codeword lengths satisfy the binary Kraft bound | `BinaryPrefixCode.kraft_inequality` | Mathlib uniquely-decodable adapter | compiled |
| `H(P),H₂(P)` | finite natural/base-two entropy and unit conversion | `discreteEntropy`, `discreteEntropyBaseTwo`, `discreteEntropyBaseTwo_eq_div_log_two` | exact finite-sum definitions | compiled |
| `E[ℓ(c(X))]` | expected codeword length objective | `expectedCodeLength` | exact finite-sum definition | compiled |
| `D(P,Q)` | extended-real relative entropy | `LowerBounds.relativeEntropy P Q` | `ENNReal`, alias of `InformationTheory.klDiv` | compiled |
| `log(dP/dQ)` | log likelihood ratio | `MeasureTheory.llr P Q` | measurable real function | imported |
| Theorem 14.1 finite branch | RN/LLR integral formula | `relativeEntropy_of_absolutelyContinuous_of_integrable` | equality in `ENNReal` | compiled |
| Theorem 14.1 singular branch | non-AC gives infinity | `relativeEntropy_eq_top_of_not_absolutelyContinuous` | endpoint equality | compiled |
| finite KL contract | AC and LLR integrability | `relativeEntropy_ne_top_iff` | exact iff | compiled |
| `D(P,Q)=0 ↔ P=Q` | separation for finite measures | `relativeEntropy_eq_zero_iff` | exact iff | compiled |
| Exercise 14.10 | KL after restriction to arbitrary `m ≤ m₀` | `relativeEntropy_trim_le` | finite-measure data processing | compiled |
| `d(p,q)` | Bernoulli relative entropy | `LowerBounds.bernoulliRelativeEntropy` reusing `KLUCB.bernoulliKL` | `ENNReal` with exact endpoints | compiled |
| Exercise 14.10 at event sigma-algebra | binary KL cannot exceed measure KL | `bernoulliRelativeEntropy_event_le` | dependency theorem | compiled |
| binary testing inequality | two-atom Bretagnolle--Huber | `binaryBretagnolleHuber` | real inequality | compiled |
| `exp(-D)/2` including `D=∞` | source RHS | `bretagnolleHuberScale` | real nonnegative scale | compiled |
| Theorem 14.2 / Eq. (14.7) | `P(A)+Q(Aᶜ)` lower bound | `bretagnolleHuber` | exact measure/event terminal | compiled |
| history relative entropy | adaptive bandit history law | `banditHistoryRelativeEntropy_eq_expectedPulls_sum` | compiled Chapter 15 consumer | compiled outside Chapter 14 gate |

## Assumption ledger

| Assumption | Lean status | Purpose | Blocking? |
| --- | --- | --- | --- |
| one measurable space for `P,Q` | typed | source comparison domain | no |
| nonempty codewords | field of `BinaryPrefixCode` | makes arbitrary repeated-message concatenations uniquely decodable | no; explicit model contract |
| `IsProbabilityMeasure P,Q` | typeclass premise on event/data-processing/testing terminals | total masses are one and event probabilities lie in `[0,1]` | no |
| `MeasurableSet A` | explicit | complements and restricted measures are valid events | no |
| direction `P ≪ Q` | derived from finite KL or explicit on Theorem 14.1 branch | legitimizes RN derivative | no |
| `Integrable (llr P Q) P` | explicit only on finite integral branch; equivalent to finite KL jointly with AC | Mathlib's real integral convention | no |
| `D(P,Q)=∞` | explicit branch of `bretagnolleHuberScale` | implements `exp(-∞)=0` | no |
| mutual AC | absent | not required by source | must remain absent |
| finite KL premise on Theorem 14.2 | absent | source theorem is unconditional | must remain absent |
| reversed `D(Q,P)` | absent from main terminal | a separate application, never a silent replacement | no |
| policy consistency/history adaptation | absent | belongs to Chapter 15 | no |
| concentration/stopping time | absent | Chapter 14 uses neither | no |

## Local API and proof route

| Leaf | Existing APIs/imports | Retrieval evidence | Intended route | Pivot rule |
| --- | --- | --- | --- | --- |
| KL definition/branches | `Mathlib.InformationTheory.KullbackLeibler.Basic` | installed Mathlib source | exact wrappers around `klDiv` branch lemmas | do not invent a second measure KL |
| prefix coding | `InformationTheory.UniquelyDecodable`, `kraft_mcmillan_inequality` | installed Mathlib source | prove the finite range uniquely decodable from prefix freedom, then adapt Kraft | do not label Kraft as the missing Huffman/source-coding terminal |
| arbitrary DPI | `Measure.trim`, `toReal_rnDeriv_trim`, `map_condExp_le`, `integral_condExp`, `integral_trim` | installed Mathlib source | finite/top split; conditional Jensen for the trimmed RN density | keep `m ≤ m₀` and finite-measure instances explicit |
| Bernoulli KL | `KLUCB.bernoulliKL`, `bernoulliKLCore_eq_klFun`, endpoint lemmas | compiled local declarations | reuse the exact support convention | do not use totalized `Real.log 0` as a finite singular value |
| event processing | f-divergence integral, restriction/RN uniqueness, convex `klFun` lower bound | installed Mathlib source; no ready-made map theorem found | decompose over `A,Aᶜ`, lower-bound each mass pair and add | if RN restriction identity blocks, extract it as a public/general helper rather than assume data processing |
| binary BH | log concavity or weighted AM--GM, square-root overlap algebra | source proof, Mathlib real analysis | affinity is at least `exp(-d/2)`; overlap is at least affinity squared over two | separate `p=0,1` and `q=0,1`; never assume interior silently |
| measure BH | event processing plus binary BH | local compiled leaves | split infinite/finite KL; convert ENNReal inequality to `toReal` only with not-top witnesses | do not weaken terminal to a premise carrying the desired inequality |
| history chain rule | `klDiv_compProd_eq_add` | imported route evidence | Chapter 15 iterative kernel model | never label imported kernel rule as an adaptive-policy history theorem |

## Proof DAG

| Node | Interface | Dependencies | Lean declaration | Mathlib status | Gate | Status |
| --- | --- | --- | --- | --- | --- | --- |
| `CH14-SOURCE-FENCE` | exact Theorems 14.1/14.2, equations and pages | official author PDF/CUP metadata | repository evidence | source evidence | source review | mapped |
| `CH14-CODE-ENTROPY` | typed prefix code, expected length, entropy units, Kraft bound | Mathlib coding API and finite real sums | `BinaryPrefixCode`, `discreteEntropy`, `expectedCodeLength` and helpers | project definitions plus imported theorem adapter | focused Lean | compiled |
| `CH14-KL-SURFACE` | extended-real KL and finite/singular branch adapters | Mathlib KL/LLR | `relativeEntropy` and branch lemmas | imported plus project wrappers | focused Lean | compiled |
| `CH14-FULL-DPI` | arbitrary sub-sigma-algebra monotonicity | conditional RN identity and Jensen | `relativeEntropy_trim_le` | Mathlib-candidate project leaf | focused Lean | compiled |
| `CH14-BERNOULLI-SURFACE` | exact two-atom endpoint convention | existing KLUCB module | `bernoulliRelativeEntropy` plus adapter lemmas | compiled dependency/project adapters | focused Lean | compiled |
| `CH14-EVENT-DPI` | binary/event KL is at most measure KL | RN restriction and f-divergence convexity | `bernoulliRelativeEntropy_event_le` | Mathlib-candidate project leaf | focused Lean | compiled |
| `CH14-BINARY-BH` | two-atom error lower bound | affinity and overlap algebra | `binaryBretagnolleHuber` | project-local | focused Lean | compiled |
| `CH14-THEOREM-14-2` | exact unconditional event testing inequality | event DPI, binary BH, top/finite split | `bretagnolleHuberScale`, `bretagnolleHuber` | source terminal | focused Lean | compiled |
| `CH14-HISTORY-KL` | same-policy adaptive history decomposition | kernel chain rule plus policy/history model | `banditHistoryRelativeEntropy_eq_expectedPulls_sum` | compiled Chapter 15 | Chapter 15 | compiled outside Chapter 14 gate |
| `CH14-TYPED-CANARY` | full conclusions including finite and singular examples | all compiled declarations | `Tests/TextbookPartIVChapter14Canary.lean` | project-local | Tests | verified |
| `CH14-LOCAL-FULL-GATE` | focused/root/Tests/placeholder/full harness gates | all compiled local nodes | Lake and `tools/bandit.py` | repository | full check | verified locally |
| `CH14-EVIDENCE-SITE` | task/DAG/export/index/site agreement | compiled chapter surface | repository artifacts | repository | lean-verified/site/browser | historical §14.2 verified; expanded-body local site check passed in 8578e2a, browser/current publication not yet verified |
| `CH14-REVIEW` | independent source/Lean/evidence audit | all local artifacts | review record | repository | independent review | historical §14.2 only; expanded-body completion audit remains open |
| `CH14-REMOTE` | PR, main Actions, Pages and live page | accepted local chapter | PR #11; run `31949303227`; Pages job `95172626370`; live desktop/mobile | repository | deployment | verified for the historical §14.2 milestone; the 2026-09-04 extension awaits its own PR |

## Gaps

- [x] Project-local RN restriction identity needed by event data processing.
- [x] Binary affinity/Jensen proof with all endpoints.
- [x] Exact unconditional measure-level Bretagnolle--Huber terminal.
- [x] Exact finite code/entropy definitions and a prefix-code Kraft adapter.
- [x] Full arbitrary-sub-sigma-algebra data processing (Exercise 14.10).
- [x] Chapter 15 same-policy history-law construction and divergence decomposition (compiled in its own gate).
- [x] Huffman optimality and the one-bit entropy sandwich; full gate dff13cb.
- [x] Arithmetic source-coding aggregate validation at 2a31a01 (named rate and converse compiled); final whole-body source audit is tracked separately below.
- [x] Eq. (14.4) for an arbitrary finite alphabet, with exact support dichotomy and zero-mass terms.
- [x] Eq. (14.5) finite-discretisation supremum equivalence to RN KL, including singular and nonintegrable branches.
- [x] Eq. (14.6) general common-density formula; full harness passed at `78846b8`.
- [x] Measure-overlap and source affinity/Jensen; full gate b8325c2.
- [x] General Gaussian-variance/application; full gate 1e8af14.
- [ ] Additional mathematical body assertions and evidence closure in the body audit.

The boxed unique-decoding equivalence is now mapped to
`exists_prefixCode_of_uniquelyDecodable`, preserving every length on a finite
injective encoder with uniquely decodable range. Its nonempty words are
derived, not assumed; the non-strict Kraft converse includes equality.
Module/direct canaries pass at 3d7c9a1; root/full gate and current export/site
verification remain pending. See the boxed-code and arithmetic-identity audits
for the two source-fidelity repairs after the a47106a gate.
