# Textbook Part IV Chapter 16 instance-dependent lower-bounds spine

Task id: `TEXTBOOK-PART-IV-CHAPTER-16-INSTANCE-DEPENDENT-LOWER-BOUNDS-SPINE`

Kind: `theoremFormalization`

Status: `verified_locally`

Harness: `hierarchical`

## Goal

Formalize the source-faithful instance-dependent lower-bound route in
Lattimore--Szepesvári, *Bandit Algorithms* (2020), Chapter 16. The exact
terminals are Definition 16.1, Theorem 16.2, Lemma 16.3, and Theorem 16.4.
The compiled first slice freezes the consistency quantifiers, the extended-real
`d_inf` interface, candidate inequalities in the original-to-alternative KL
direction, the unit-Gaussian perturbed-alternative cost, and the subpolynomial
log-growth step. It must not be reported as any blocked source terminal.

## Source

- Authors: Tor Lattimore and Csaba Szepesvári.
- Book: *Bandit Algorithms*, Cambridge University Press, 2020.
- Book DOI: <https://doi.org/10.1017/9781108571401>.
- Chapter DOI: <https://doi.org/10.1017/9781108571401.021>.
- CUP chapter page:
  <https://www.cambridge.org/core/books/abs/bandit-algorithms/instancedependent-lower-bounds/C6CDB8FD64DF85192F18CC0811667470>.
- Official author PDF: <https://tor-lattimore.com/downloads/book/book.pdf>.
- Placement: Part IV, Chapter 16, CUP print pp. 177--184; author-online
  page labels 206--214; physical PDF pp. 215--223.
- §16.1 Asymptotic Bounds: CUP pp. 177--179; author-online pp. 207--208;
  physical PDF pp. 216--217. Definition 16.1 and Theorem 16.2.
- §16.2 Finite-Time Bounds: CUP p. 180; author-online pp. 209--210;
  physical PDF pp. 218--219. Lemma 16.3 and Theorem 16.4.
- §16.3 Notes: CUP p. 181; author-online p. 210; physical PDF p. 219.
- §16.4 Bibliographic Remarks: CUP p. 181; author-online p. 211;
  physical PDF p. 220.
- §16.5 Exercises: CUP pp. 181--184; author-online pp. 211--214;
  physical PDF pp. 220--223.
- Textbook card: `TXT-LATTIMORE-SZEPESVARI-2020` plus Chapter 16 cards below.
- Scenario card: `SCN-STOCHASTIC-FINITE`.

The CUP print pagination, author-online page labels, and physical PDF pages are
edition-specific fields. The author PDF explicitly warns that its pagination
does not match the print edition, so no constant page offset is inferred.

## Frozen source targets

Definition 16.1 calls a policy `pi` consistent over an environment class `E`
when, for every `nu in E` and every real `p>0`,

```text
lim_{n -> infinity} R_n(pi,nu) / n^p = 0.                 (16.1)
```

Let `E=M_1 x ... x M_k` be an unstructured class whose component laws have
finite means. For a law `P in M` with mean below `muStar`, define

```text
d_inf(P,muStar,M) = inf { D(P,P') : P' in M, mean(P') > muStar }.
```

Theorem 16.2 says that every policy consistent over `E` satisfies, for every
`nu=(P_i)` in `E`,

```text
liminf_{n -> infinity} R_n(pi,nu)/log(n)
  >= c*(nu,E)
   = sum_{i: Delta_i>0} Delta_i / d_inf(P_i,muStar,M_i).  (16.2)
```

The KL direction is always original law `P_i` to confusing alternative
`P_i'`. The proof changes only suboptimal arm `i` to a law whose mean is
strictly above the original optimal mean and uses
`A={T_i(n)>n/2}`. Expected pulls are under the original environment.

Lemma 16.3 considers environments differing only at arm `i`, where `i` is
suboptimal in `nu` and uniquely optimal in `nu'`. With
`lambda=mu_i(nu')-mu_i(nu)`, it gives the finite-time pull-count bound

```text
E_nu[T_i(n)] >=
  (log(min{lambda-Delta_i(nu),Delta_i(nu)}/4)
    + log(n) - log(R_n(nu)+R_n(nu')))
  / D(P_i,P_i').                                         (16.4)
```

Theorem 16.4 specializes to unit-variance Gaussian bandits. For a nonempty set
`N` of horizons, `C>0`, `p in (0,1)`, and a policy satisfying
`R_n(pi,nu')<=C n^p` for every `n in N` and every coordinatewise local
alternative `nu' in E(nu)`, it states that for `epsilon in (0,1]` and `n in N`,

```text
R_n(pi,nu) >= 2/(1+epsilon)^2
  * sum_{i:Delta_i>0}
      (((1-p)log(n)+log(epsilon*Delta_i/(8C)))/Delta_i)^+. (16.5)
```

## Lean target and status fence

Target file: `BanditRLProof/LowerBounds/InstanceDependent.lean`.

Compiled public declarations:

```lean
LowerBounds.IsConsistentRegret
LowerBounds.IsConsistentPolicyOver
LowerBounds.IsConsistentRegret.add
LowerBounds.IsConsistentRegret.eventually_add_le_rpow
LowerBounds.IsConsistentRegret.eventually_log_add_div_log_le
LowerBounds.divergenceInfimum
LowerBounds.divergenceInfimum_le
LowerBounds.parametricDivergenceInfimum
LowerBounds.parametricDivergenceInfimum_le
LowerBounds.unitGaussianDivergenceInfimum
LowerBounds.unitGaussianDivergenceInfimum_le_perturbed
```

Reserved source terminals, with no declaration claimed:

```lean
LowerBounds.consistentPolicy_liminf_expectedPull_div_log_ge_inv_dInf
LowerBounds.consistentPolicy_liminf_expectedRegret_div_log_ge
LowerBounds.expectedPullCount_ge_log_regret_changeOfMeasure
LowerBounds.gaussianExpectedRegret_ge_finiteTimeInstanceDependent
```

The chapter stays `partial`. The compiled declarations are definitions and
general dependency leaves; they are not Theorem 16.2, Lemma 16.3, or Theorem
16.4.

## Exact regularity contract

- The class in Theorem 16.2 is unstructured: a Cartesian product of per-arm
  distribution classes. Structured-bandit information constraints are not
  silently included.
- Component laws are probability measures with finite real means.
- Consistency quantifiers are `forall nu in E, forall p>0`; `p` is real, not
  a fixed exponent or a natural number.
- Regret is expected pseudo-regret and is nonnegative. The generic compiled
  consistency predicate does not hide nonnegativity as a field.
- `d_inf` is extended-real. Empty confusing-alternative sets yield `infinity`;
  zero and infinite information costs require explicit branches before real
  division or reciprocal manipulation.
- Confusing alternatives have mean strictly greater than `muStar`, not merely
  greater than or equal to it.
- KL direction is original `P_i` to alternative `P_i'`; expectations in the
  pull constraint are under the original environment.
- The history laws use the same possibly randomized nonanticipating policy.
- Theorem 16.2 uses a `liminf`; the proof's log-growth step must not be
  replaced by convergence without proving it.
- Lemma 16.3's logarithm arguments are positive because the original gap and
  the alternative optimality margin are positive. A real-valued division
  branch also needs finite positive arm KL.
- Theorem 16.4 uses unit-variance Gaussian arms, a nonempty horizon set,
  `C>0`, `p in (0,1)`, `epsilon in (0,1]`, and the positive part in Eq. (16.5).

## Current semantic blocker

Theorem 16.2 and Lemma 16.3 require Lemma 15.1's same-policy adaptive-history
divergence decomposition. Installed Mathlib exposes a composition-product KL
chain rule but not the conditional integral of pointwise kernel KL, and the
repository has no canonical possibly randomized policy-kernel history law.
Therefore neither the event bridge nor the bandit pull-count KL constraint can
compile yet. Theorem 16.4 inherits that blocker through Lemma 16.3.

The remaining Chapter 16-specific analytic leaves are the exact `d_inf`
Gaussian infimum formula, extended-real zero/infinity branches, and the final
`liminf` extraction. These are independent proof obligations, not reasons to
weaken the source bandit semantics.

## Proof obligations

- [x] Official edition, book/chapter DOI, stable author PDF, section titles,
  and three-way pagination are recorded.
- [x] Definition 16.1, Theorem 16.2, Lemma 16.3, and Theorem 16.4 are frozen
  with exact quantifiers, KL direction, event orientation, constants, and
  positive-part placement.
- [x] Existing Chapter 14--15 and Mathlib asymptotic/infimum APIs are audited.
- [x] Exact generic consistency and `d_inf` interfaces compile.
- [x] Sum closure, eventual every-power domination, and eventual log-ratio
  dependency leaves compile.
- [x] Candidate `d_inf` bounds and the unit-Gaussian perturbed-alternative KL
  cost compile.
- [ ] Exact Gaussian `d_inf` equality compiles with all infimum branches.
- [ ] Lemma 15.1 or an equivalent source-faithful history information
  constraint compiles.
- [ ] Theorem 16.2's per-arm and regret `liminf` terminals compile.
- [ ] Lemma 16.3 and Theorem 16.4 compile.
- [x] Root import, canary, Tests, scans, full harness, exports, indexes, site,
  browser, and independent local review pass.
- [ ] PR, authoritative-main Actions, Pages deployment, and live checks pass.

## Mathlib-ready leaf contract

| Leaf | Local APIs/imports | Intended proof route | Regularity contracts | Mathlib status |
| --- | --- | --- | --- | --- |
| consistency closure and power domination | `Tendsto.add`, `eventually_lt_const`, `Real.rpow_pos_of_pos` | add normalized limits, then clear an eventually positive denominator | positive real exponent; natural horizon eventually nonzero | compiled project-local |
| log-growth adapter | `Real.log_le_log`, `Real.log_rpow`, positive division | convert eventual power domination into an eventual log-ratio inequality | positive regret sum; horizon greater than one | compiled project-local |
| distribution-class `d_inf` | complete-lattice `sInf`, Chapter 14 extended-real KL | retain empty, zero, finite, and infinite branches | measurable reward space; explicit mean functional and class membership | compiled project-local interface |
| parameterized `d_inf` candidate | `sInf_le`, Gaussian arm KL | insert a strictly better alternative and preserve KL direction | strict mean improvement | compiled project-local |
| Gaussian exact `d_inf` | preceding candidate plus lower bound and limit/infimum approximation | squeeze perturbed alternatives as epsilon tends to zero | original mean below target; extended-real conversion | open Mathlib/project leaf |
| history information constraint | Chapter 15 conditional kernel KL and stochastic history law | change one arm and apply Lemma 15.1 | same stochastic policy; first-law expectation; finite KL branch | connected blocker |
| asymptotic terminal | finite-time information inequality plus consistency log leaf | divide by log horizon and take liminf | positive gap/information; zero/infinite branches | blocked source terminal |
| finite-time Gaussian terminal | Lemma 16.3, Gaussian KL, regret decomposition | choose mean shift `Delta_i(1+epsilon)`, sum positive parts | exact local class and horizon quantifiers | blocked source terminal |

## Retrieval cards

- Mathlib: `MLIB-ASYMPTOTICS`, `MLIB-REAL-LOG-SQRT`,
  `MLIB-EXP-LOG-INEQUALITIES`, `MLIB-ORDER-ALGEBRA`, measure KL and complete
  lattice `sInf` APIs.
- Local compiled dependencies: Chapter 14 `bretagnolleHuber`; Chapter 15
  `relativeEntropy`, `klDiv_gaussianReal_one`, and the current Gaussian law.
- Textbook: `TXT-LATTIMORE-SZEPESVARI-2020`,
  `TXT-LS-2020-DEF-16-1-CONSISTENCY`, `TXT-LS-2020-THM-16-2-ASYMPTOTIC`,
  `TXT-LS-2020-LEMMA-16-3-FINITE-TIME`, and
  `TXT-LS-2020-THM-16-4-GAUSSIAN-FINITE-TIME`.
- Scenario: `SCN-STOCHASTIC-FINITE`.
- LML: none promoted.
- Route evidence only: `WEAPON-KL-CHANGE-OF-MEASURE`.

## Nonclaims and failure policy

- A generic `Tendsto` or `sInf` leaf is not a bandit lower-bound terminal.
- The Gaussian perturbed-alternative upper bound is not the exact Gaussian
  `d_inf` equality from Table 16.1.
- A theorem that assumes the history KL/pull-count inequality is a conditional
  analytic leaf, not a proof of Lemma 15.1 or Theorem 16.2.
- Theorem cards and source prose remain route evidence only.
- If the terminals remain blocked, preserve their exact contracts and publish
  only compiled reusable leaves plus the blockers. Do not restrict the policy
  to a deterministic map, reverse KL, weaken strict alternative optimality, or
  delete the consistency quantifiers.
