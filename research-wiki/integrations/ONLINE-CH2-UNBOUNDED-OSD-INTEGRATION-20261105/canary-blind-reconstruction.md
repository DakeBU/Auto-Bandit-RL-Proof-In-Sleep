# Complete neutral-check reconstruction

**Finding:** check1 has seven top-level conjuncts and check2 has nine. Every conjunct is decoded below. These are supplied mathematical assertions, not checked implementation proofs.

Input SHA-256: `dc22754c3faccbca9f45d0e96b72eb173f50af4738dd0e71f9740d0a6724bea6`, matching the supplied hash.

## Definitions and indexing

- **schedule:** eta(s)=schedule(1/2,s)=(s+1)^(-1/2)=1/sqrt(s+1).
- **scalarRun:** x^T_0=0; x^T_{s+1}=x^T_s-eta(s)*sigma_T(s), where sigma_T(s)=-1 for s<ceil(T/2) and +1 otherwise. scalarRun(T,t)=x^T_t.
- **scalarRegret:** scalarRegret(T)=sum_{s=0}^{T-1} sigma_T(s)*x^T_s, since comparator 0 has loss 0.
- **direction:** d=PiLp.single 2 0 1 in EuclideanSpace R (Fin 2); standard coordinate reading (1,0). Its unit norm is explicitly included in check2.
- **vectorRun:** X^T_0=0; X^T_{s+1}=X^T_s-eta(s)*sigma_T(s)*d. vectorRun(T,t)=X^T_t=-sum_{s=0}^{t-1} eta(s)*sigma_T(s)*d.
- **vectorRegret:** vectorRegret(T)=sum_{s=0}^{T-1} sigma_T(s)*<d,X^T_s>, versus the zero vector comparator.

The time-t point has undergone t updates. Round s is scored at the point before applying its own update. For horizon T, regret scores points indexed 0 through T-1; the final point at T is outside that sum. The first argument of scalarRun/vectorRun selects the horizon-dependent loss stream, while the second selects the iterate time. Changing the first argument can therefore change the entire trajectory, even at early fixed times.

## Complete supplied typed interfaces

```lean
noncomputable section
open Set Finset Filter Topology
open scoped InnerProductSpace
set_option autoImplicit false
namespace NeutralCanary
open NeutralPacket
abbrev scalarRun (T t : ℕ) : ℝ :=
  BanditRL.OnlineSubgradientDescent.iterate BanditRL.OnlineHuber.fullSpace (schedule (1/2))
    (fun s z => (payoff T (1 : ℝ) s z : EReal)) 0 t
abbrev scalarRegret (T : ℕ) : ℝ :=
  BanditRL.OnlineSubgradientDescent.regret BanditRL.OnlineHuber.fullSpace (schedule (1/2))
    (fun s z => (payoff T (1 : ℝ) s z : EReal)) 0 0 T
abbrev direction : EuclideanSpace ℝ (Fin 2) := PiLp.single 2 0 1
abbrev vectorRun (T t : ℕ) : EuclideanSpace ℝ (Fin 2) :=
  BanditRL.OnlineSubgradientDescent.iterate BanditRL.OnlineHuber.fullSpace (schedule (1/2))
    (fun s z => (payoff T direction s z : EReal)) 0 t
abbrev vectorRegret (T : ℕ) : ℝ :=
  BanditRL.OnlineSubgradientDescent.regret BanditRL.OnlineHuber.fullSpace (schedule (1/2))
    (fun s z => (payoff T direction s z : EReal)) 0 0 T

theorem check1 :
    schedule (1/2) 0 = 1 ∧
    0 < schedule (1/2) 1 ∧
    schedule (1/2) 1 < schedule (1/2) 0 ∧
    scalarRun 2 0 = 0 ∧ scalarRun 2 1 = 1 ∧
    scalarRun 2 2 = 1 - (2 : ℝ) ^ (-(1/2 : ℝ)) ∧
    scalarRegret 2 = 1

theorem check2 :
    ‖direction‖ = 1 ∧ vectorRun 64 1 = direction ∧
    (∀ t < 64, ConvexOn ℝ univ (payoff 64 direction t) ∧
      LipschitzWith 1 (payoff 64 direction t)) ∧
    (1/15 : ℝ) ≤ coefficient (1/2) ∧
    2 / ((1 - (1/2 : ℝ)) * coefficient (1/2)) ≤ (64 : ℝ) ∧
    (1/2 : ℝ) * coefficient (1/2) * (64 : ℝ) ^ (2 - (1/2 : ℝ)) ≤ vectorRegret 64 ∧
    (256/15 : ℝ) ≤ vectorRegret 64 ∧ (17 : ℝ) < vectorRegret 64 ∧
    (∃ loss : ℕ → EuclideanSpace ℝ (Fin 2) → ℝ,
      (∀ t < 64, ConvexOn ℝ univ (loss t) ∧ LipschitzWith 1 (loss t)) ∧
      (1/2 : ℝ) * coefficient (1/2) * (64 : ℝ) ^ (2 - (1/2 : ℝ)) ≤
        BanditRL.OnlineSubgradientDescent.regret BanditRL.OnlineHuber.fullSpace
          (schedule (1/2)) (fun t z => (loss t z : EReal)) 0 0 64)
```

## check1 conjuncts

### Conjunct 1

- **Objects and spaces:** Real scalars, schedule eta(s)=(s+1)^(-1/2), full feasible space R.
- **Quantifiers:** No free variables.
- **Assumptions:** No external hypotheses; this is a conjunct of a closed theorem.
- **Conclusion:** schedule(1/2,0)=1.
- **Constants and indexing:** The initial step size eta(0)=1^(-1/2).
- **Probability and feedback:** Deterministic assertion. No randomness, expectation, probability level or feedback protocol is specified.
- **Boundaries:** This is the first step size, not the first post-update point.

### Conjunct 2

- **Objects and spaces:** Real scalars, schedule eta(s)=(s+1)^(-1/2), full feasible space R.
- **Quantifiers:** No free variables.
- **Assumptions:** No external hypotheses; this is a conjunct of a closed theorem.
- **Conclusion:** 0<schedule(1/2,1).
- **Constants and indexing:** The second step size is eta(1)=2^(-1/2).
- **Probability and feedback:** Deterministic assertion. No randomness, expectation, probability level or feedback protocol is specified.
- **Boundaries:** Strict positivity; not a lower bound uniform over all times.

### Conjunct 3

- **Objects and spaces:** Real scalars, schedule eta(s)=(s+1)^(-1/2), full feasible space R.
- **Quantifiers:** No free variables.
- **Assumptions:** No external hypotheses; this is a conjunct of a closed theorem.
- **Conclusion:** schedule(1/2,1)<schedule(1/2,0).
- **Constants and indexing:** Equivalently 2^(-1/2)<1.
- **Probability and feedback:** Deterministic assertion. No randomness, expectation, probability level or feedback protocol is specified.
- **Boundaries:** This conjunct compares only times 1 and 0; it does not itself quantify general monotonicity.

### Conjunct 4

- **Objects and spaces:** Real scalars, schedule eta(s)=(s+1)^(-1/2), full feasible space R.
- **Quantifiers:** No free variables.
- **Assumptions:** No external hypotheses; this is a conjunct of a closed theorem.
- **Conclusion:** scalarRun(2,0)=0.
- **Constants and indexing:** T=2 selects the stream, while t=0 selects the point before any update.
- **Probability and feedback:** Deterministic assertion. No randomness, expectation, probability level or feedback protocol is specified.
- **Boundaries:** The initial point is zero. The first argument is not a time index.

### Conjunct 5

- **Objects and spaces:** Real scalars, schedule eta(s)=(s+1)^(-1/2), full feasible space R.
- **Quantifiers:** No free variables.
- **Assumptions:** No external hypotheses; this is a conjunct of a closed theorem.
- **Conclusion:** scalarRun(2,1)=1.
- **Constants and indexing:** At round s=0 the loss is -z and eta(0)=1, so one update from zero yields 1.
- **Probability and feedback:** Deterministic assertion. No randomness, expectation, probability level or feedback protocol is specified.
- **Boundaries:** This is the point used to score round 1 after round 0 has updated the state.

### Conjunct 6

- **Objects and spaces:** Real scalars, schedule eta(s)=(s+1)^(-1/2), full feasible space R.
- **Quantifiers:** No free variables.
- **Assumptions:** No external hypotheses; this is a conjunct of a closed theorem.
- **Conclusion:** scalarRun(2,2)=1-2^(-1/2).
- **Constants and indexing:** At round s=1 the T=2 loss is +z; eta(1)=2^(-1/2) is subtracted from x(1)=1.
- **Probability and feedback:** Deterministic assertion. No randomness, expectation, probability level or feedback protocol is specified.
- **Boundaries:** This is the point after two updates. It is not scored in the horizon-two regret, which stops at round 1.

### Conjunct 7

- **Objects and spaces:** Real scalars, schedule eta(s)=(s+1)^(-1/2), full feasible space R.
- **Quantifiers:** No free variables.
- **Assumptions:** No external hypotheses; this is a conjunct of a closed theorem.
- **Conclusion:** scalarRegret(2)=1.
- **Constants and indexing:** The score sums rounds s=0 and s=1 at pre-update points x(0)=0 and x(1)=1, versus comparator 0. Contributions are -0-(-0)=0 and 1-0=1.
- **Probability and feedback:** Deterministic assertion. No randomness, expectation, probability level or feedback protocol is specified.
- **Boundaries:** Fixed-comparator loss difference, not the loss at x(2), an average, or best-comparator regret.

## check2 conjuncts

### Conjunct 1

- **Objects and spaces:** E=EuclideanSpace R (Fin 2), the two-dimensional real Euclidean space; d=direction=PiLp.single 2 0 1.
- **Quantifiers:** No free variables.
- **Assumptions:** No external hypotheses; this is a conjunct of a closed theorem.
- **Conclusion:** ||d||=1.
- **Constants and indexing:** The supplied single-coordinate constructor has the usual Euclidean reading d=(1,0), with nonzero coordinate indexed by 0 in Fin 2.
- **Probability and feedback:** Deterministic assertion. No randomness, expectation, probability level or feedback protocol is specified.
- **Boundaries:** The constructor implementation is not supplied; the unit-norm property is expressly asserted as this conjunct.

### Conjunct 2

- **Objects and spaces:** E=EuclideanSpace R (Fin 2), the two-dimensional real Euclidean space; d=direction=PiLp.single 2 0 1.
- **Quantifiers:** No free variables.
- **Assumptions:** No external hypotheses; this is a conjunct of a closed theorem.
- **Conclusion:** vectorRun(64,1)=d.
- **Constants and indexing:** At round 0 the sign is -1, eta(0)=1, initial point is 0, and the update subtracts -d.
- **Probability and feedback:** Deterministic assertion. No randomness, expectation, probability level or feedback protocol is specified.
- **Boundaries:** One update is asserted, not an identity for every subsequent time.

### Conjunct 3

- **Objects and spaces:** E=EuclideanSpace R (Fin 2), the two-dimensional real Euclidean space; d=direction=PiLp.single 2 0 1.
- **Quantifiers:** For every natural t satisfying t<64.
- **Assumptions:** No external hypotheses; this is a conjunct of a closed theorem.
- **Conclusion:** payoff(64,d,t,.) is convex on all E and LipschitzWith 1.
- **Constants and indexing:** Rounds are precisely 0,...,63. Each Lipschitz inequality bounds |f(x)-f(y)| by ||x-y|| for all x,y in E.
- **Probability and feedback:** Deterministic assertion. No randomness, expectation, probability level or feedback protocol is specified.
- **Boundaries:** Two regularity properties occur inside this single top-level conjunct. They are required globally in space but only at the stated 64 times. No loss-value bound is asserted.

### Conjunct 4

- **Objects and spaces:** Real coefficient C=coefficient(1/2).
- **Quantifiers:** No free variables.
- **Assumptions:** No external hypotheses; this is a conjunct of a closed theorem.
- **Conclusion:** 1/15<=C.
- **Constants and indexing:** A weak lower bound by the exact real fraction 1/15. Algebraically C=sqrt(2)-4/3 from the supplied coefficient definition.
- **Probability and feedback:** Deterministic assertion. No randomness, expectation, probability level or feedback protocol is specified.
- **Boundaries:** This is not an equality or an asserted upper bound.

### Conjunct 5

- **Objects and spaces:** Real threshold with horizon 64 and C=coefficient(1/2).
- **Quantifiers:** No free variables.
- **Assumptions:** No external hypotheses; this is a conjunct of a closed theorem.
- **Conclusion:** 2/((1-1/2)*C)<=64.
- **Constants and indexing:** The exact threshold simplifies to 4/C. C>=1/15>0 gives 4/C<=60<=64.
- **Probability and feedback:** Deterministic assertion. No randomness, expectation, probability level or feedback protocol is specified.
- **Boundaries:** The original weak inequality is preserved; the statement is a concrete eligibility check for T=64, not T=2.

### Conjunct 6

- **Objects and spaces:** E=EuclideanSpace R (Fin 2), the two-dimensional real Euclidean space; d=direction=PiLp.single 2 0 1. The regret result is real.
- **Quantifiers:** No free variables.
- **Assumptions:** No external hypotheses; this is a conjunct of a closed theorem.
- **Conclusion:** (1/2)*C*64^(2-1/2)<=vectorRegret(64).
- **Constants and indexing:** The exponent is 3/2 and 64^(3/2)=512, so the stated lower bound simplifies to 256*C.
- **Probability and feedback:** Deterministic assertion. No randomness, expectation, probability level or feedback protocol is specified.
- **Boundaries:** The bound concerns the explicitly defined T=64 direction stream, initial vector 0 and comparator vector 0. No expectation is present.

### Conjunct 7

- **Objects and spaces:** E=EuclideanSpace R (Fin 2), the two-dimensional real Euclidean space; d=direction=PiLp.single 2 0 1. The regret result is real.
- **Quantifiers:** No free variables.
- **Assumptions:** No external hypotheses; this is a conjunct of a closed theorem.
- **Conclusion:** 256/15<=vectorRegret(64).
- **Constants and indexing:** Weak inequality with exact rational constant 256/15; follows mathematically from the preceding bound and C>=1/15.
- **Probability and feedback:** Deterministic assertion. No randomness, expectation, probability level or feedback protocol is specified.
- **Boundaries:** A numerical consequence, not a claim that the regret equals 256/15.

### Conjunct 8

- **Objects and spaces:** E=EuclideanSpace R (Fin 2), the two-dimensional real Euclidean space; d=direction=PiLp.single 2 0 1. The regret result is real.
- **Quantifiers:** No free variables.
- **Assumptions:** No external hypotheses; this is a conjunct of a closed theorem.
- **Conclusion:** 17<vectorRegret(64).
- **Constants and indexing:** Strict inequality. The preceding rational lower bound exceeds 17 because 256/15=17+1/15.
- **Probability and feedback:** Deterministic assertion. No randomness, expectation, probability level or feedback protocol is specified.
- **Boundaries:** Strictness is retained. It is not merely 17<=regret.

### Conjunct 9

- **Objects and spaces:** E=EuclideanSpace R (Fin 2), the two-dimensional real Euclidean space; d=direction=PiLp.single 2 0 1. loss:N->E->R; its real values are embedded into EReal for the regret API.
- **Quantifiers:** There exists one sequence loss defined for all natural times such that both: for every natural t<64, its round loss is convex and LipschitzWith 1; and its regret satisfies the stated bound.
- **Assumptions:** No external hypotheses; this is a conjunct of a closed theorem.
- **Conclusion:** Exists loss with [forall t<64, ConvexOn R univ (loss(t)) and LipschitzWith 1 (loss(t))] and [(1/2)*C*64^(3/2)<=regret(fullSpace,schedule(1/2),EReal-embedded loss,0,0,64)].
- **Constants and indexing:** The initial point and comparator are separately supplied zero vectors. The lower bound is 256*C. The inner t is a natural round index and is local to the witness properties.
- **Probability and feedback:** Deterministic assertion. No randomness, expectation, probability level or feedback protocol is specified.
- **Boundaries:** One witness must satisfy both properties. The theorem does not name it or equate it to the stream in vectorRegret. The explicitly named payoff(64,d) stream is nevertheless a candidate witness from conjuncts 3 and 6. This existential neither reuses the T=2 scalar stream nor requires a single stream valid at multiple horizons.

## Distinct horizon-dependent streams

- **conclusion:** The two checks instantiate the same parameterized construction at different horizons and in different spaces; they do not share one fixed loss sequence.
- **T2:** m=ceil(2/2)=1: scalar loss is -z at s=0 and +z at every s>=1. Its tested horizon scores s=0,1.
- **T64:** m=ceil(64/2)=32: vector loss is -<d,z> at s=0,...,31 and +<d,z> at every s>=32. Its tested horizon scores s=0,...,63.
- **explicit_difference:** At s=1, the T=2 scalar stream has positive sign whereas the T=64 vector stream has negative sign. Even under the natural identification z=r*d, these losses are opposite for nonzero r. The definitions therefore cannot be read as one common horizon-independent sequence.
- **witness_scope:** The last conjunct of check2 introduces its own existentially quantified vector-valued-domain loss sequence. No identity with another named or existential sequence is imposed; the named T64 payoff stream satisfies the requested properties if the other stated conjuncts hold.

## Concrete score and numerical audit

For T=2, x(0)=0, x(1)=1, and x(2)=1-1/sqrt(2). The two scored losses against zero are 0 and 1, yielding regret exactly 1. The value x(2) is an update-output check and contributes no third score.

For T=64, the first 32 losses have negative sign and the next 32 have positive sign. In particular X(1)=d. The point X(32) is obtained after all 32 negative-sign updates and is the point used to score the first positive-sign loss, at round 32. The update using that round yields X(33)=X(32)-d/sqrt(33). The final scored round is 63 at X(63); X(64) is not scored.

Writing C=coefficient(1/2)=sqrt(2)-4/3, the asserted coefficient bound is C>=1/15>0. The threshold simplifies to 4/C<=60<=64. The regret lower bound simplifies to 256*C, which is at least 256/15=17+1/15>17. All weak versus strict inequality directions in the original targets are retained. The T=2 test asserts its exact regret directly and does not assert satisfaction of the large-horizon threshold.

## Limits and access disclosure

- Textual mathematical reconstruction only; no source-fidelity approval or source identity lookup.
- No compilation, elaboration or target proof checking.
- Closed-form update equations use the affine subgradient and step statements supplied in the original packet and the full-space projection contract previously reconstructed; their target proof bodies were not inspected.
- Standard notation and constructor meanings are interpreted mathematically. PiLp.single implementation and full elaborated supporting signatures are not supplied.
- No probability, expectation, bandit observation protocol or algorithmic oracle guarantee is specified.
- The numerical simplifications are transparent mathematical deductions, not separately Lean-checked proofs.

Actor: `/root/batch41_blind_decoder`, continuing the original source-withheld reconstruction. The only newly read pre-existing file was the authorized canary packet. Prior packet and projection supplement content and hashes were retained from earlier authorized reads, not reread here. Generic ABRL environment context remains as previously disclosed. Existing outputs were not changed.
