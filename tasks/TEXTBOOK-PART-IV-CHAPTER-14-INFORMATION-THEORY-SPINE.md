# Textbook Part IV Chapter 14 information-theory spine

Task id: `TEXTBOOK-PART-IV-CHAPTER-14-INFORMATION-THEORY-SPINE`

Kind: `theoremFormalization`

Status: `accepted`

Whole-chapter coverage: `partial`

Harness: `hierarchical`

## Goal

Formalize the source-faithful information-theoretic foundation of Chapter 14,
*Foundations of Information Theory*.  The original accepted milestone covered
the lower-bound-facing Section 14.2 slice.  Whole-chapter completion additionally
requires the Section 14.1 coding/entropy body and every mathematical claim in the
Section 14.2 exposition and proof to be either connected to a compiled local
declaration or recorded as an explicit blocker.  It must not claim the adaptive-
bandit history decomposition from Chapter 15.

## Source

- Authors: Tor Lattimore and Csaba Szepesvári.
- Book: *Bandit Algorithms*, Cambridge University Press, 2020.
- DOI: <https://doi.org/10.1017/9781108571401>.
- Formal author version: <https://tor-lattimore.com/downloads/book/book.pdf>.
- Placement: Part IV, Chapter 14, author-version pp. 186--197, physical PDF
  pp. 195--206 (CUP edition pagination pp. 160--169).
- Whole-chapter body window: §14.1--§14.2, author-version pp. 186--191 /
  physical PDF pp. 195--200.  Notes, bibliographic remarks, and exercises are
  optional coverage and cannot conceal a body gap.
- Theorem 14.1: relative entropy is the log Radon--Nikodym integral when
  `P ≪ Q`, and is infinite otherwise.
- Theorem 14.2, Eq. (14.7): for probability measures `P,Q` and measurable
  event `A`, `P(A) + Q(Aᶜ) >= exp(-D(P,Q))/2`.
- Exercise 14.10: data processing under restriction to a sub-sigma-algebra;
  the compiled event/binary version is a dependency leaf, not a renumbered
  source theorem.
- Textbook card: `TXT-LATTIMORE-SZEPESVARI-2020`.
- Scenario card: `SCN-STOCHASTIC-FINITE`.

## Frozen whole-chapter completion contract

The chapter can be promoted from `partial` only when every required row below
is locally compiled and canaried.  A definition-only row is satisfied by an
exact typed definition; theorem/proposition rows require proofs.  Imported
Mathlib results may discharge leaves but must be exposed through a source-
mapped local adapter before they count as chapter evidence.

| Source body node | Exact required content | Current evidence | Status |
| --- | --- | --- | --- |
| opening motivation | information-theory/KL role in generalising Chapter 13 | maintained source map; no theorem claim | mapped |
| §14.1 code model | binary codewords, injectivity, prefix freedom, codeword length, and expected length | `BinaryPrefixCode`, its uniquely-decodable range, finite codebook, Kraft adapter, and `expectedCodeLength` compile; the explicit nonempty-codeword contract is recorded | partial |
| Eq. (14.1) | optimal expected-length objective over valid prefix codes | `huffmanOptimalCode`, `huffmanCode_optimal`; exact global minimization, full gate dff13cb | compiled |
| Eq. (14.2) | Huffman optimum satisfies `H₂(P) ≤ L* ≤ H₂(P)+1` | `huffmanOptimalCode` recursively merges two least weights; global optimality and entropy sandwich for finite alphabets, ties/zeros included; classical real-weight construction, not an executable encoder; full gate passed at dff13cb | compiled |
| §14.1 asymptotic statement | arithmetic coding approaches entropy and no code improves the asymptotic rate | named interval-address arithmetic block code with zero-mass escape tag; rate tends to entropy on Fin k, matching universal prefix-code converse; focused build/canary passed, full gate and source audit pending | partial |
| Eqs. (14.2)--(14.3) definitions | finite discrete base-two entropy, natural entropy, and exact unit conversion | `discreteEntropy`, `discreteEntropyBaseTwo`, their exact conversion, and nonnegativity compile | compiled |
| Eq. (14.4) | arbitrary finite-alphabet discrete relative entropy with exact zero/support endpoints | `relativeEntropy_finite_sum_log`, `relativeEntropy_finite_eq_if`, and `relativeEntropy_finite_eq_top_iff` compile; root-import finite/singular three-symbol canaries pass | compiled |
| Eq. (14.5) | relative entropy as the supremum over all finite measurable discretisations | `finitePartitionRelativeEntropy_eq_relativeEntropy` compiles for arbitrary finite measures, using finite encodings of the concrete density filtration; root and aggregate Tests pass | compiled |
| Theorem 14.1 | Eq. (14.5) equals the RN/log-likelihood formula, including the singular and nonintegrable branches | full supremum/RN equality and exact RN branch adapters compile; no finite-KL or AC premise on the equality; root and aggregate Tests pass | compiled |
| Eq. (14.6) | common-dominating-measure density formula | `relativeEntropy_commonDensity_eq_if` and the nonnegative `klFun` formula; root/aggregate/full harness passed at `78846b8` for arbitrary sigma-finite domination | compiled |
| §14.2 metric properties | nonnegativity, `D(P,Q)=0 ↔ P=Q`, and counterexamples to symmetry/triangle inequality | zero/separation compiles; `bernoulliRelativeEntropy_asymmetry` and `relativeEntropy_triangle_counterexample` focused-build passed; aggregate pending | partial |
| Gaussian example | common-variance Gaussian KL formula | `klDiv_gaussianReal_same_variance`; root/aggregate/full harness passed at `1e8af14` | compiled |
| Bernoulli example | endpoint-complete binary KL formula | `bernoulliRelativeEntropy` and endpoint lemmas compile | compiled |
| Theorem 14.2 / Eq. (14.7) | unconditional Bretagnolle--Huber event inequality in direction `D(P,Q)` | exact local terminal compiles | compiled |
| Eq. (14.8) | measure-level overlap lower bound used in the source proof | attaining-event and integral-Jensen/Cauchy--Schwarz routes; root/aggregate/full harness passed at `b8325c2` | compiled |
| Eq. (14.9) | measure-level Le Cam affinity/overlap inequality | `half_commonDensityAffinity_sq_le_overlap`; root/aggregate/full harness passed at `b8325c2` | compiled |
| Gaussian testing application | the displayed Gaussian error bound and the `3/10`, `3/20` consequences under `Δ²/σ²≤1` | exponential and both rational bounds; root/aggregate/full harness passed at `1e8af14` | compiled |

Optional rows are §14.3 Notes, §14.4 Bibliographic Remarks, and Exercises
14.1--14.15.  Exercise 14.10 is a high-value optional target: the existing
event/Bernoulli theorem is its two-cell specialization, while
`relativeEntropy_trim_le` now compiles the arbitrary-sub-sigma-algebra result
for finite measures.

## Frozen Lean target

Target file: `BanditRLProof/LowerBounds/InformationTheory.lean`.

Expected public declarations (names may gain narrowly descriptive helpers but
the semantic signatures may not be weakened):

```lean
LowerBounds.relativeEntropy
LowerBounds.relativeEntropy_of_absolutelyContinuous_of_integrable
LowerBounds.relativeEntropy_eq_top_of_not_absolutelyContinuous
LowerBounds.relativeEntropy_ne_top_iff
LowerBounds.relativeEntropy_eq_zero_iff
LowerBounds.BinaryPrefixCode
LowerBounds.BinaryPrefixCode.kraft_inequality
LowerBounds.discreteEntropy
LowerBounds.discreteEntropyBaseTwo
LowerBounds.expectedCodeLength
LowerBounds.bernoulliRelativeEntropy
LowerBounds.relativeEntropy_trim_le
LowerBounds.bernoulliRelativeEntropy_event_le
LowerBounds.binaryBretagnolleHuber
LowerBounds.bretagnolleHuberScale
LowerBounds.bretagnolleHuber
```

The public terminal uses a real-valued scale `0` when `D(P,Q)=∞`, and
`exp (-(D(P,Q)).toReal)/2` otherwise. This is the explicit Lean encoding of
the source convention `exp(-∞)=0`; no finiteness assumption is added to
Theorem 14.2.

## Exact regularity contract

- `P` and `Q` are probability measures on one measurable space.
- The event is a `MeasurableSet`.
- KL direction is `D(P,Q)`, never silently reversed.
- `P ≪ Q` is derived from finite KL when needed; the infinite branch is
  discharged by the explicit testing scale.
- Integrability of `llr P Q` is explicit in the finite integral formula and is
  characterized by `relativeEntropy_ne_top_iff`.
- Bernoulli parameters are event probabilities in `[0,1]`; singular endpoints
  use `∞`, matching absolute continuity.
- No policy, horizon, filtration, kernel-composition, stopping-time, or bandit
  model assumption belongs to this chapter terminal.
- `BinaryPrefixCode` requires every codeword to be nonempty.  This is needed
  for its range to be uniquely decodable under arbitrary finite message
  concatenation; a singleton empty codeword would otherwise be prefix-free.

## Proof obligations

- [x] Official edition, chapter/section, printed/PDF pages, DOI and stable PDF
  are recorded without copying source prose.
- [x] Theorem 14.1 and Theorem 14.2 are mapped with exact KL direction and
  extended-real conventions.
- [x] Existing project Bernoulli KL and installed Mathlib KL APIs are audited.
- [x] Relative-entropy definition and Theorem 14.1 branch adapters compile.
- [x] Event-level Bernoulli data processing compiles from RN/f-divergence APIs.
- [x] Scalar binary Bretagnolle--Huber compiles with endpoint cases.
- [x] Exact measure-level Theorem 14.2 compiles without a hidden finite-KL
  assumption.
- [x] Root import, focused build, typed canary, Tests, axiom scan, full harness,
  proof export, evidence indexes, documentation and website pass.
- [x] Independent read-only review finds no unresolved P0--P3 issue.
- [x] PR, authoritative-main Actions, Pages deployment and live desktop/mobile
  page are verified before this task becomes accepted.

## 2026-09-04 whole-body extension local evidence

- Detached short-path checkout `C:\a14` at `50dce67` passed the 2,670-job
  focused information-theory build, the root-import Chapter 14 typed canary,
  the 8,852-job root-library build, and the 8,894-job `Tests` build.
- `python tools/bandit.py check` passed: both Lean gates, proof-graph export,
  and 400 Python tests with seven expected skips completed successfully.
- The typed canary includes a concrete one-bit Boolean prefix code and checks
  unique decoding, Kraft, and expected length. Its axiom reports contain only
  `propext`, `Classical.choice`, and `Quot.sound`.
- The lean-verified site build/check passed with 604 modules, 8,224
  declarations, zero placeholders, and 658 checked pages. In-app browser
  inspection at desktop and 390×844 mobile widths confirmed the compiled vs.
  partial split, all exact gap families, rendered math, official source links,
  and no document-level horizontal overflow.
- Independent read-only review found two P2 evidence-consistency defects; the
  missing arbitrary finite-alphabet Eq. (14.4) gap and historical/current gate
  ambiguity were corrected. No P0, P1, P2, or P3 issue remains unresolved.

## Historical §14.2 local verification evidence

- Commit `5a84d26` passed `python3 tools/bandit.py check` in detached
  short-path worktree `C:\abrl-p4-ch14-final-5a84d26`: the root library built
  in 3,690 jobs, `Tests` built in 3,703 jobs, and all 42 Python tests passed
  with one expected skip.
- The root-import typed canary covers finite and singular examples. Its axiom
  reports contain only `propext`, `Classical.choice`, and `Quot.sound`.
- The lean-verified site build/check passed with 560 modules, 7,383
  declarations, zero placeholders, and 588 checked pages. Desktop and 390px
  mobile inspections confirmed rendered MathJax, no broken images, no
  document-level overflow, and a locally scrollable long table.
- Independent read-only session
  `01a00a9a-8d8b-7440-aac3-ad45d1a634f6` found no actionable P0--P3 issue.
  Its statement audit confirmed KL direction, complement ownership, finite
  and singular branches, Bernoulli endpoints, and the Chapter 15 history-law
  nonclaim. See
  `reviews/2026-08-16-textbook-part-iv-chapter-14-information-theory-spine.md`.

## Historical §14.2 remote verification evidence

- PR #11 passed `Lean and documentation / build` in run `31948234489`, job
  `95167560544` (22m25s), and was merged without a direct push to `main`.
- Merge commit: `194aca91b5d9b50c26fffaf5b02c610112a7daa7`.
- Authoritative-main run `31949303227` passed: build job `95170181038`
  completed in 20m56s with Lean, Tests, site generation, site checks, and
  Pages artifact upload; deployment job `95172626370` completed in 10s.
- Live page:
  <https://dakebu.github.io/Auto-Bandit-RL-Proof-In-Sleep/textbook-spine/chapter-14-information-theory/>.
  Desktop 1280px and mobile 390x844 inspections confirmed the verified
  banner, overall `PARTIAL` chapter status, compiled Theorem 14.2 mapping,
  Chapter 15 history-KL nonclaim, five MathJax containers, zero broken images,
  and no document-level horizontal overflow.

Remote acceptance applies to the scoped §14.2 Lean surface. It does not
promote §14.1 coding results, full Exercise 14.10, or adaptive history KL to
compiled status.

## Mathlib-ready leaf contract

| Leaf | Local APIs/imports | Intended proof route | Regularity contracts | Mathlib status |
| --- | --- | --- | --- | --- |
| KL/RN surface | `InformationTheory.klDiv`, `MeasureTheory.llr`, `klDiv_of_ac_of_integrable`, `klDiv_of_not_ac`, `klDiv_ne_top_iff` | transparent project aliases/adapters | same measurable space; finite measures for the imported API; probability measures at source terminal | imported Mathlib, project wrappers |
| Bernoulli endpoint surface | `KLUCB.bernoulliKL`, `bernoulliKLCore`, endpoint/self lemmas | reuse exact existing `ENNReal` support convention | parameters in `[0,1]`; second-parameter endpoints explicit | compiled project-local dependency |
| arbitrary sub-sigma-algebra DPI | `Measure.trim`, `toReal_rnDeriv_trim`, conditional expectation/Jensen, `integral_trim` | split infinite KL; in the finite branch identify the trimmed RN density with a conditional expectation and apply Jensen to `klFun` | finite measures; `m ≤ m₀`; finite KL supplies AC/integrability | Mathlib-candidate project leaf, compiled as `relativeEntropy_trim_le` |
| event data processing | `klDiv_eq_lintegral_klFun_of_ac`, `mul_klFun_le_toReal_klDiv`, RN derivative under restriction, measure partition | restrict to `A,Aᶜ`, apply convexity, add the two pieces | `MeasurableSet A`; finite-KL branch supplies AC/integrability | Mathlib-candidate project leaf |
| binary testing | real log/exp/sqrt, two-point Jensen/AM--GM, Cauchy--Schwarz algebra | source's affinity/overlap proof specialized to two atoms | Bernoulli endpoint cases separated | project-local |
| source terminal | binary testing plus event data processing | split `klDiv=∞` from finite KL; use `toReal` only in finite branch | probability measures; measurable event; direction `P` to `Q` | project-local source theorem |
| history KL decomposition | Chapter 14 measure KL plus `InformationTheory.klDiv_compProd_eq_add` | compiled Chapter 15 conditional-KL and iterative same-policy history construction | kernels, measurability, common randomized policy, countably generated rewards | compiled Chapter 15 source theorem; not a Chapter 14 claim |

## Retrieval cards

- Mathlib candidates: `InformationTheory.klDiv`,
  `InformationTheory.klDiv_of_ac_of_integrable`,
  `InformationTheory.klDiv_of_not_ac`,
  `InformationTheory.klDiv_ne_top_iff`,
  `InformationTheory.klDiv_eq_lintegral_klFun_of_ac`,
  `InformationTheory.mul_klFun_le_toReal_klDiv`, and
  `InformationTheory.klDiv_compProd_eq_add`.
- Local compiled dependency: `BanditRLProof.KLUCB.bernoulliKL` and its exact
  endpoint/core lemmas.
- Textbook: `TXT-LATTIMORE-SZEPESVARI-2020`.
- Scenario: `SCN-STOCHASTIC-FINITE`.
- LML: none promoted; no local LML dependency is needed.
- Route evidence only: `WEAPON-KL-CHANGE-OF-MEASURE`.

## Nonclaims and failure policy

- The §14.1 typed code/entropy surface and Kraft adapter compile, but neither
  Huffman optimality nor the finite/block source-coding theorem is claimed.
- The full sub-sigma-algebra data-processing Exercise 14.10 compiles as
  `relativeEntropy_trim_le`; the event theorem remains a distinct specialization.
- The adaptive-bandit divergence decomposition is Chapter 15, not Chapter 14.
- Mathlib declarations and theorem cards are imported/route evidence, not new
  local proofs.
- Never add finite KL, mutual absolute continuity, or reversed KL direction to
  make the source terminal easier. On a real block, retain the exact terminal
  as planned/blocked and record the smallest general leaf and missing API.
