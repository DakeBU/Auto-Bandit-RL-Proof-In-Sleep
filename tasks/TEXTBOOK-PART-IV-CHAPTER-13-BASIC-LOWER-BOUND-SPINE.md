# Textbook Part IV Chapter 13 lower-bound basic ideas spine

Task id: `TEXTBOOK-PART-IV-CHAPTER-13-BASIC-LOWER-BOUND-SPINE`

Kind: `theoremFormalization`

Status: `accepted`

Harness: `hierarchical`

## Goal

Build the source-faithful deterministic and order-theoretic interface used by
Chapter 13, *Lower Bounds: Basic Ideas*, and connect it to the minimax lower
bound whose proof the source defers to Chapter 15. The compiled Chapter 13
module exposes minimax/worst-case expected-regret semantics, the
least-explored alternative-arm averaging step, and the conditional algebraic
two-environment reduction behind equations (13.2)--(13.3); the separately
compiled Chapter 15 construction supplies the caller-free Gaussian endpoint.

The maintained public names remain **BanditRLlib** and
*ABRL: A Target-Faithful Autoformalization Harness and Lean 4 Library for
Bandit and Reinforcement Learning Theory*.

## Source

- Authors: Tor Lattimore and Csaba Szepesvári.
- Book: *Bandit Algorithms*, Cambridge University Press, 2020.
- DOI: <https://doi.org/10.1017/9781108571401>.
- Formal author version: <https://tor-lattimore.com/downloads/book/book.pdf>.
- Placement: Part IV, Chapter 13, CUP print pp. 155--159, author-online
  pp. 180--185, physical PDF pp. 189--194.  Theorem 13.1 is CUP p. 155 /
  author-online p. 180 / physical PDF p. 189; Section 13.1 starts at CUP
  p. 155 / author-online pp. 181--182 / physical PDF pp. 190--191.
- Textbook card: `TXT-LATTIMORE-SZEPESVARI-2020`.
- Scenario card: `SCN-STOCHASTIC-FINITE`.
- Proof inspiration only: `WEAPON-KL-CHANGE-OF-MEASURE`.

The source statement is restated rather than copied: for the class of
`k`-armed unit-variance Gaussian bandits whose mean vector belongs to
`[0,1]^k`, there is a universal positive constant `c` such that, when `k > 1`
and `n >= k`, the infimum over policies of the worst-case expected cumulative
pseudo-regret is at least `c * sqrt (k*n)`. Chapter 13 labels this as Theorem
13.1 and explicitly defers its proof to Chapter 15.

## Frozen Chapter 13 target contract

The Chapter 13 gate compiles only the interfaces that the chapter actually
develops before that deferral:

1. For arbitrary policy and environment types, define worst-case and minimax
   expected regret in `ENNReal` over explicit policy/environment classes.
   Empty classes keep the standard complete-lattice semantics; intended
   Gaussian use will require explicit nonemptiness at the consumer.
2. Index a `k = m + 1` arm problem by distinguished base arm `0` and
   alternative arms `Fin m` mapped through `Fin.succ`. From nonnegative
   expected pulls and the exact pull budget `sum_a E[T_a(n)] = n`, prove that
   some alternative arm has expected pulls at most `n / m`.
3. Define the exact Chapter 13 algebraic expressions

   ```text
   base lower-bound expression    = Delta * (n - E_nu[T_0(n)])
   changed lower-bound expression = Delta * E_nu'[T_0(n)].
   ```

   Prove the quantitative maximum lower bound
   `Delta * (n - error) / 2` only under the explicit comparison
   `E_nu[T_0(n)] - E_nu'[T_0(n)] <= error`, and retain the half-horizon
   statement as its zero-error corollary. The comparison is a named missing
   information-theoretic bridge, not a hidden assumption and not a caller-free
   lower-bound theorem.
4. Publish the declarations through the root library and a full-typed external
   canary. The canary must instantiate nonempty policy/environment classes and
   a nondegenerate three-arm expected-pull vector.

Target files: `BanditRLProof/LowerBounds/BasicIdeas.lean` and the downstream
consumer `BanditRLProof/LowerBounds/GaussianMinimax.lean`.

Expected public declarations:

```lean
LowerBounds.worstCaseExpectedRegret
LowerBounds.minimaxExpectedRegret
LowerBounds.expectedRegret_le_worstCaseExpectedRegret
LowerBounds.minimaxExpectedRegret_le_worstCaseExpectedRegret
LowerBounds.le_minimaxExpectedRegret
LowerBounds.exists_alternative_le_average
LowerBounds.alternativeExpectedPullBudget_le
LowerBounds.exists_leastExploredAlternative
LowerBounds.baseEnvironmentRegret
LowerBounds.changedEnvironmentRegretLowerBound
LowerBounds.max_base_changed_regretLowerBound_ge_half_sub_error
LowerBounds.max_base_changed_regretLowerBound_ge_half
LowerBounds.unitGaussianMinimaxExpectedPseudoRegret_ge_one_div_fiftyFour_sqrt
```

## Proof obligations

- [x] The formal source and page placement are recorded.
- [x] Theorem 13.1 is fenced as source-stated and is compiled through the
  Chapter 15 specialization with explicit universal constant `1/54`.
- [x] The compiled Chapter 13 semantic signature is frozen before tactics.
- [x] Hidden regularity assumptions are explicit in the conversion window.
- [x] Minimax and worst-case definitions and order leaves compile.
- [x] Alternative-arm averaging leaves compile from the exact pull budget.
- [x] Conditional two-environment algebra leaves compile without a statistical
  nonclaim being promoted.
- [x] Root import, focused build, typed canary, Tests, axiom scan, full harness
  check, proof export, evidence indexes, documentation, and website pass.
- [x] Independent read-only review finds no unresolved P0--P3 issue.
- [x] The earlier dependency-slice PR #9, remote Actions run `31942624241`, merge commit `44c3e153`,
  Pages deployment job `95156292456`, and the live desktop/mobile Chapter 13
  page pass.
- [ ] The current Chapter 15 downstream Theorem 13.1 consumer passes its own
  PR, authoritative-main Actions, Pages deployment, and live Chapter 13 check.

## Mathlib-ready leaf contract

| Leaf | Local APIs/imports | Intended proof route | Regularity contracts | Mathlib status |
| --- | --- | --- | --- | --- |
| minimax surface | `iSup`, `iInf`, `ENNReal`, subtypes | complete-lattice introduction/elimination | explicit policy/environment subsets; nonemptiness only at semantic consumers | project-local |
| finite average | `Fin.sum_univ_succ`, `Finset.exists_le_of_sum_le`, `Fintype.card_fin` | split arm zero, bound alternative sum, compare with constant average | `0 < m`, every expected pull nonnegative, exact total expected-pull identity | mathlib-composed project leaf |
| two-environment algebra | ordered-field arithmetic, `max`, `nlinarith` | combine base and changed lower expressions under a named upper bound on `E_nu[T_0]-E_nu'[T_0]` | `0 <= Delta`; the quantitative cross-law discrepancy is explicit and remains unproved here | project-local |
| history change of measure | compiled Chapter 15 Lemma 15.1 | Chapter 14 KL plus the Chapter 15 randomized-history construction | measurability, common randomized policy, countably generated rewards | compiled downstream dependency |
| Gaussian minimax terminal | `unitGaussianMinimaxExpectedPseudoRegret_ge_one_div_fiftyFour_sqrt` | Chapter 15 consumption of Chapter 14 information bridge and Chapter 13 algebra | unit variance, means in `[0,1]^k`, `k > 1`, `n >= k` | compiled source-order endpoint with explicit `c=1/54` |

## Retrieval cards

- Mathlib: `MLIB-FINSET-SUMS`, `MLIB-FINTYPE-FIN`,
  `MLIB-ORDER-ALGEBRA`.
- Textbook: `TXT-LATTIMORE-SZEPESVARI-2020`.
- Scenario: `SCN-STOCHASTIC-FINITE`.
- LML: none required by the first compiled leaves.
- Route evidence only: `WEAPON-KL-CHANGE-OF-MEASURE`.

## Nonclaims

- Theorem 13.1 is not proved inside the Chapter 13 module; the project-level
  source endpoint is the separately compiled Chapter 15 consumer.
- No Gaussian measure, adaptive history likelihood ratio, KL chain rule,
  event-level binary KL inequality, Pinsker/Bretagnolle--Huber inequality, or
  absolute-continuity result is claimed locally in this chapter.
- An external theorem card or proof-weapon card is never a local Lean proof.
- The compiled conditional algebra theorem alone does not establish the
  cross-environment comparison; the Chapter 14--15 route supplies it on the
  same policy and history law.
- The chapter does not cover finite-arm minimax sharp constants,
  instance-dependent asymptotics, or high-probability lower bounds.

## Failure policy

Do not weaken Theorem 13.1, identify expectations from different environments,
drop the policy-consistency or absolute-continuity requirements of the future
bridge, or relabel deterministic scaffolding as the Gaussian minimax theorem.
For any broader replacement route, preserve the exact source target and record
the smallest missing definition, Mathlib API, regularity assumption, and
reusable leaf before changing route.
