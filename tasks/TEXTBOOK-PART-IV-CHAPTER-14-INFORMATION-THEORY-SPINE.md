# Textbook Part IV Chapter 14 information-theory spine

Task id: `TEXTBOOK-PART-IV-CHAPTER-14-INFORMATION-THEORY-SPINE`

Kind: `theoremFormalization`

Status: `active`

Harness: `hierarchical`

## Goal

Formalize the source-faithful information-theoretic foundation of Chapter 14,
*Foundations of Information Theory*. The compiled slice must expose the
extended-real relative entropy with its absolute-continuity/integrability
branches, the source's Bernoulli endpoint convention, an event-level
data-processing leaf, and the exact Bretagnolle--Huber testing inequality.
It must not claim the adaptive-bandit history decomposition from Chapter 15.

## Source

- Authors: Tor Lattimore and Csaba Szepesvári.
- Book: *Bandit Algorithms*, Cambridge University Press, 2020.
- DOI: <https://doi.org/10.1017/9781108571401>.
- Formal author version: <https://tor-lattimore.com/downloads/book/book.pdf>.
- Placement: Part IV, Chapter 14, printed pp. 186--197, PDF pp. 195--206.
- Main target window: §14.2, printed pp. 188--191 / PDF pp. 197--200.
- Theorem 14.1: relative entropy is the log Radon--Nikodym integral when
  `P ≪ Q`, and is infinite otherwise.
- Theorem 14.2, Eq. (14.7): for probability measures `P,Q` and measurable
  event `A`, `P(A) + Q(Aᶜ) >= exp(-D(P,Q))/2`.
- Exercise 14.10: data processing under restriction to a sub-sigma-algebra;
  the compiled event/binary version is a dependency leaf, not a renumbered
  source theorem.
- Textbook card: `TXT-LATTIMORE-SZEPESVARI-2020`.
- Scenario card: `SCN-STOCHASTIC-FINITE`.

## Frozen Lean target

Target file: `BanditRLProof/LowerBounds/InformationTheory.lean`.

Expected public declarations (names may gain narrowly descriptive helpers but
the semantic signatures may not be weakened):

```lean
LowerBounds.relativeEntropy
LowerBounds.relativeEntropy_of_absolutelyContinuous_of_integrable
LowerBounds.relativeEntropy_eq_top_of_not_absolutelyContinuous
LowerBounds.relativeEntropy_ne_top_iff
LowerBounds.bernoulliRelativeEntropy
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

## Proof obligations

- [x] Official edition, chapter/section, printed/PDF pages, DOI and stable PDF
  are recorded without copying source prose.
- [x] Theorem 14.1 and Theorem 14.2 are mapped with exact KL direction and
  extended-real conventions.
- [x] Existing project Bernoulli KL and installed Mathlib KL APIs are audited.
- [ ] Relative-entropy definition and Theorem 14.1 branch adapters compile.
- [ ] Event-level Bernoulli data processing compiles from RN/f-divergence APIs.
- [ ] Scalar binary Bretagnolle--Huber compiles with endpoint cases.
- [ ] Exact measure-level Theorem 14.2 compiles without a hidden finite-KL
  assumption.
- [ ] Root import, focused build, typed canary, Tests, axiom scan, full harness,
  proof export, evidence indexes, documentation and website pass.
- [ ] Independent read-only review finds no unresolved P0--P3 issue.
- [ ] PR, authoritative-main Actions, Pages deployment and live desktop/mobile
  page are verified before this task becomes accepted.

## Mathlib-ready leaf contract

| Leaf | Local APIs/imports | Intended proof route | Regularity contracts | Mathlib status |
| --- | --- | --- | --- | --- |
| KL/RN surface | `InformationTheory.klDiv`, `MeasureTheory.llr`, `klDiv_of_ac_of_integrable`, `klDiv_of_not_ac`, `klDiv_ne_top_iff` | transparent project aliases/adapters | same measurable space; finite measures for the imported API; probability measures at source terminal | imported Mathlib, project wrappers |
| Bernoulli endpoint surface | `KLUCB.bernoulliKL`, `bernoulliKLCore`, endpoint/self lemmas | reuse exact existing `ENNReal` support convention | parameters in `[0,1]`; second-parameter endpoints explicit | compiled project-local dependency |
| event data processing | `klDiv_eq_lintegral_klFun_of_ac`, `mul_klFun_le_toReal_klDiv`, RN derivative under restriction, measure partition | restrict to `A,Aᶜ`, apply convexity, add the two pieces | `MeasurableSet A`; finite-KL branch supplies AC/integrability | Mathlib-candidate project leaf |
| binary testing | real log/exp/sqrt, two-point Jensen/AM--GM, Cauchy--Schwarz algebra | source's affinity/overlap proof specialized to two atoms | Bernoulli endpoint cases separated | project-local |
| source terminal | binary testing plus event data processing | split `klDiv=∞` from finite KL; use `toReal` only in finite branch | probability measures; measurable event; direction `P` to `Q` | project-local source theorem |
| history KL decomposition | `InformationTheory.klDiv_compProd_eq_add` is retrieval evidence | Chapter 15 iterative same-policy history construction | kernels, measurability, policy consistency | planned Chapter 15; not a Chapter 14 claim |

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

- Entropy/source coding in §14.1 is mapped pedagogically, but the formal
  theorem spine targets the lower-bound dependencies in §14.2; no coding
  theorem is claimed.
- The full sub-sigma-algebra data-processing Exercise 14.10 is not claimed
  unless separately compiled; only its event/binary specialization is required.
- The adaptive-bandit divergence decomposition is Chapter 15, not Chapter 14.
- Mathlib declarations and theorem cards are imported/route evidence, not new
  local proofs.
- Never add finite KL, mutual absolute continuity, or reversed KL direction to
  make the source terminal easier. On a real block, retain the exact terminal
  as planned/blocked and record the smallest general leaf and missing API.
