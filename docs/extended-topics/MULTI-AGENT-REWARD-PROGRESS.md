# Arbitrary bounded rewards and simultaneous exploration mean accuracy

Source: Rosenski, Shamir and Szlak, *Multi-Player Bandits -- a Musical Chairs
Approach*, ICML2016 PMLR48:155--163, static Algorithm1 and supplement A.1
Lemma2. The pinned official source and separate repair review are in
MULTI-AGENT-CONTRACT.md and multi-agent-source-review.json. This implements the
previously reviewed random-count proof preserving the first exploration term.
It does not establish the population estimator, ranking, full good event or
complete unknown-N regret. This checkpoint remains scratch-only.

## Exact model and theorem

For each arm a, supply an arbitrary Borel probability measure nu(a) on Real,
a.e. supported on [0,1]. Define mu(a) as its integral of the identity function.
No finite-support or Bernoulli restriction is imposed. The reward-array law is

    rewardLaw(nu,T) = product_(t in Fin T) product_(a in Fin k) nu(a).

A coordinate r(t,a) has precisely law nu(a), with mean mu(a). Couple this law
with the previously constructed actual independent uniform exploration action
schedule PMF by a product measure. The actual feedback readout provides zero
on collision, a separate collision bit, and r(t,chosen_arm) on a collision-free
round. Local empirical means use only the resulting player-local feedback,
collision-free count/sum, and the zero-count fallback fixed earlier.

For k>0, n<=k, a player i, arm a, every finite T, and0<=eps<=1, the new bound is

    P(abs(localMean(i,a)-mu(a)) >= eps/2)
      <= 2 exp(-T eps^2/(16k)).

This event is measured on the ACTUAL joint action/reward law. There is no
supplied correct-estimator event, tail bound, count distribution or selected
reward independence premise. For eps>0 and delta>0, if

    T >= (16k/eps^2) log(4k^2/delta),

then with probability at least1-delta/2, every player/arm local mean has error
STRICTLY smaller than eps/2. The Lean probability lower bound uses ENNReal
truncated subtraction, so remains valid for any positive delta; the full
learner later uses delta<1. This is the mean-accuracy portion of the required
exploration good event. Population recovery and top-set construction are still
separate required producers. The source complete setting1<=n<k is stronger than
this component's n<=k; tagged statements require i:Fin n. The all-player result
also covers the vacuous n=0 case. The nonempty-arm condition k>0 is retained.

## Fixed action schedule: actual selected rewards

Projecting nested product measures proves each reward coordinate's exact
marginal and integral. The a.e. range [0,1] transfers along this measure-
preserving projection. Mathlib's hasSubgaussianMGF_of_mem_Icc then yields a
centered proxy1/4. iIndepFun_pi produces time-coordinate independence from the
constructed reward law; independence is not postulated for adaptively selected
or stopping-time rewards.

For a FIXED complete action schedule x, player i and arm a, define S(x,i,a) as
the finite set of times at which i chooses a without collision. This filter
depends on actions alone. Its cardinality D equals the actual observationCount
from the previous prototype. The exact localRewardSum identity supplies the
sum of r(t,a) over this filter, and localEmpiricalMean_eq_selectedMean proves
the actual local mean is the selected sum divided by D, with explicit zero
fallback. Applying sub-Gaussian finite-sum bounds to S and its negative gives

    rewardLaw{abs(sum_(t in S) (r(t,a)-mu(a))) >= u}
      <= 2 exp(-u^2/(2*(D/4))).

For D>0, choose u=D eps/2 and use the exact centered-sum identity. This gives
2 exp(-D eps^2/2) for the local mean event. For D=0, the same claimed bound is2,
and the separate branch uses probability<=1<=2. It never divides by zero or
silently discards empty-sample histories. At T=0 the general single-coordinate
bound is likewise the valid loose2; the positive exploration-budget condition
prevents claiming small failure probability at zero time in the normal delta<1
regime.

## Mixing the actual random count

Measurability of the selected mean and the joint local mean is proved. Since
the action-schedule space is finite/discrete, product measurability follows
from the measurable fixed-schedule sections. The product-measure event formula
and finite lintegral give the exact identity

    P_joint(bad(i,a)) = sum_x p(x) rewardLaw(bad(i,a) at fixed x).

This is the proved finite mixture identity; no explicit condDistrib or
normalized-history conditional-measure theorem is asserted. Independence of
rewards from actions is encoded by the constructed product measure. The
fixed-schedule argument is therefore valid here; it would not justify arbitrary
reward-dependent selection rules.

Use the previously proved transform of the actual D(x), with eta=eps^2/2:

    P_joint(bad(i,a))
      <= 2 E_x[exp(-D(x) eps^2/2)]
      = 2 (q exp(-eps^2/2) + 1-q)^T,
    q = (1/k) ((k-1)/k)^(n-1) >= 1/(4k).

All finite measure/real-to-ENNReal conversions are explicit. The uniform
numerical producer is reused to prove the real q lower bound. For0<=x<=1,
exp(x)>=1+x implies x/2<=1-exp(-x). Setting x=eps^2/2 yields
1-exp(-eps^2/2)>=eps^2/4. Also1-y<=exp(-y), so the exact mixture is at most
2 exp(-T q eps^2/4), hence2 exp(-T eps^2/(16k)). This establishes the original
first coefficient16 without a separate lower-count Chernoff event.

Union over the actual n*k events requires no independence between players or
arms. Since n<=k,

    P(any local mean error >=eps/2) <= 2 k^2 exp(-T eps^2/(16k)).

The stated logarithmic budget makes this <=delta/2. The complement is explicitly
the event allMeanAccurate of strict error<eps/2 for all players and arms. Its
probability bound is proved, not an assumed premise. Converting the algorithm's
ceil(max(...)) duration into this budget, combining the population-estimation
event, and constructing the learned candidate set remain open.

## Concrete measure and endpoint checks

RewardCanary.unitUniform is Lebesgue measure restricted to [0,1]. Its probability
normalization and a.e. range are proved. The actual n=2,k=3,T=2 joint process
with this arm law satisfies the single-local-mean bound2 exp(-eps^2/24). This
exercises a non-discrete reward law; the mean remains defined by its actual
integral (no evaluated1/2 identity is claimed in this canary). Additional
identities check that a singleton observed-time set reads its actual reward,
and an empty set returns zero. These are component checks, not the mandatory
full-learner Bernoulli example with population recovery and ranking.

## Dependencies, status and remaining boundary

Actual reused project interfaces are the previous exploration action law,
observationCount_laplace, local feedback/count/sum definitions and identities,
and real_uniform_hazard_lower. Mathlib supplies Measure.pi, measure-preserving
evaluation, integral_map, iIndepFun_pi, bounded-variable sub-Gaussian MGFs,
finite-sum tails, product-measure application, finite lintegrals and exp/log
algebra. No dependency or toolchain changes were made.

The exact prior exploration prototype remains immutable context in this
scratch file. Newly added reward/mean-accuracy declarations and the three named
probability instances are audited separately. Public shared extraction,
combined root/Tests/harness/site/registry gates have not been run for this new
scratch layer. Production remains at the earlier accepted coordination-regret
checkpoint. Source/semantic review and exact execution hashes are recorded in
runs/extended-topics-20260920/multi-agent-reward-review.json.

Still required: collision-count concentration and simultaneous Nhat recovery,
total inverse-log rounding, ranking under the boundary gap, actual complete
exploration good event, post-exploration coordination-law identification,
full conditional/unconditional regret and short-horizon/1-over-T statements,
full-learner canary, recent-source proof comparison and ICLR evidence. The
second exploration logarithm's reviewed all-player correction is unchanged.
No topic or overall Goal completion, main merge or deployment is claimed.

## Exact scratch Lean (including unchanged exploration context)

<details><summary>Actual reward law, count mixture, mean-accuracy proofs and canaries</summary>

```lean
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import BanditRLProof.Algorithms.MusicalChairsCoordinationTime

open scoped Classical ENNReal
set_option autoImplicit false

namespace BanditRLProof.FinitePMF

noncomputable def iid {α : Type*} [Fintype α] (p : PMF α) (T : ℕ) : PMF (Fin T → α) :=
  PMF.ofFintype (fun x => ∏ t, p (x t)) (by
    rw [← Fintype.prod_sum]
    have hp : ∑ a, p a = 1 := by simpa [tsum_fintype] using p.tsum_coe
    simp [hp])

theorem iid_apply {α : Type*} [Fintype α] (p : PMF α) (T : ℕ) (x : Fin T → α) :
    iid p T x = ∏ t, p (x t) := by simp [iid, PMF.ofFintype_apply]

theorem iid_product_expectation {α : Type*} [Fintype α] (p : PMF α) (T : ℕ)
    (f : Fin T → α → ℝ≥0∞) :
    ∑ x, iid p T x * ∏ t, f t (x t) = ∏ t, ∑ a, p a * f t a := by
  simp_rw [iid_apply, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun t a => p a * f t a)).symm

noncomputable def eventCount {α : Type*} {T : ℕ} (E : Set α) (x : Fin T → α) : ℕ :=
  (Finset.univ.filter (fun t => x t ∈ E)).card

theorem pow_eventCount {α : Type*} {T : ℕ} (E : Set α) (x : Fin T → α) (z : ℝ≥0∞) :
    z ^ eventCount E x = ∏ t, if x t ∈ E then z else 1 := by
  simp [eventCount, ← Finset.prod_filter]

theorem indicator_weight_sum {α : Type*} [Fintype α] (p : PMF α) (E : Set α)
    (z : ℝ≥0∞) :
    ∑ a, p a * (if a ∈ E then z else 1) =
      p.toOuterMeasure E * z + p.toOuterMeasure Eᶜ := by
  rw [PMF.toOuterMeasure_apply_fintype, PMF.toOuterMeasure_apply_fintype,
    Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : a ∈ E <;> simp [h, Set.indicator]

theorem iid_count_pgf {α : Type*} [Fintype α] (p : PMF α) (T : ℕ)
    (E : Set α) (z : ℝ≥0∞) :
    ∑ x, iid p T x * z ^ eventCount E x =
      (p.toOuterMeasure E * z + p.toOuterMeasure Eᶜ)^T := by
  simp_rw [pow_eventCount]
  rw [iid_product_expectation p T (fun _ a => if a ∈ E then z else 1)]
  simp_rw [indicator_weight_sum]
  simp

end BanditRLProof.FinitePMF

namespace BanditRLProof.MusicalChairs

noncomputable def explorationDraw (n k : ℕ) (hk : 0 < k) : PMF (Fin n → Fin k) :=
  jointDraw (fun _ => Finset.univ) (fun _ => ⟨⟨0, hk⟩, Finset.mem_univ _⟩)

noncomputable def explorationLaw (n k T : ℕ) (hk : 0 < k) :
    PMF (Fin T → Fin n → Fin k) := FinitePMF.iid (explorationDraw n k hk) T

def observes {n k : ℕ} (i : Fin n) (a : Fin k) : Set (Fin n → Fin k) :=
  {draw | draw i = a ∧ CollisionFree draw i}

theorem observes_rectangle {n k : ℕ} (i : Fin n) (a : Fin k) :
    observes i a = {draw | ∀ j, draw j ∈ isolationWindow i a j} := by
  ext draw
  constructor
  · intro ⟨hi, hc⟩ j
    by_cases hj : j = i
    · subst j; simpa [isolationWindow] using hi
    · simpa [isolationWindow, hj, hi] using hc j hj
  · intro h
    have hi : draw i = a := by simpa [isolationWindow] using h i
    refine ⟨hi, ?_⟩
    intro j hj
    simpa [isolationWindow, hj, hi] using h j

theorem exploration_observes_probability {n k : ℕ} (hk : 0 < k) (i : Fin n) (a : Fin k) :
    (explorationDraw n k hk).toOuterMeasure (observes i a) =
      (1 / (k : ℝ≥0∞)) * (((k-1 : ℕ) : ℝ≥0∞) / (k : ℝ≥0∞))^(n-1) := by
  rw [observes_rectangle, explorationDraw, jointDraw_rectangle_product]
  have hentry (j : Fin n) :
      (((Finset.univ : Finset (Fin k)) ∩ isolationWindow i a j).card : ℝ≥0∞) /
        ((Finset.univ : Finset (Fin k)).card : ℝ≥0∞) =
      if j = i then 1 / (k : ℝ≥0∞) else (((k-1 : ℕ) : ℝ≥0∞) / (k : ℝ≥0∞)) := by
    by_cases h : j = i <;> simp [isolationWindow, h]
  simp_rw [hentry]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  simp only [ite_true]
  congr 1
  calc
    _ = ∏ _j ∈ (Finset.univ.erase i),
        (((k-1 : ℕ) : ℝ≥0∞) / (k : ℝ≥0∞)) := by
      apply Finset.prod_congr rfl
      intro j hj
      simp [(Finset.mem_erase.mp hj).1]
    _ = _ := by simp


theorem exploration_collisionFree_split {n k : ℕ} (hk : 0 < k) (i : Fin n) :
    (explorationDraw n k hk).toOuterMeasure {draw | CollisionFree draw i} =
      ∑ a : Fin k, (explorationDraw n k hk).toOuterMeasure (observes i a) := by
  simp_rw [PMF.toOuterMeasure_apply_fintype]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro draw _
  rw [Finset.sum_eq_single (draw i)]
  · simp [observes, Set.indicator]
  · intro a _ ha
    simp [observes, Set.indicator, Ne.symm ha]
  · simp

theorem exploration_collisionFree_probability {n k : ℕ} (hk : 0 < k) (i : Fin n) :
    (explorationDraw n k hk).toOuterMeasure {draw | CollisionFree draw i} =
      (((k-1 : ℕ) : ℝ≥0∞) / (k : ℝ≥0∞))^(n-1) := by
  rw [exploration_collisionFree_split]
  simp_rw [exploration_observes_probability hk i]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← mul_assoc]
  have hk0 : (k : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  simp [one_div, ENNReal.mul_inv_cancel hk0 (by simp)]

theorem exploration_collision_probability {n k : ℕ} (hk : 0 < k) (i : Fin n) :
    (explorationDraw n k hk).toOuterMeasure {draw | ¬ CollisionFree draw i} =
      1 - (((k-1 : ℕ) : ℝ≥0∞) / (k : ℝ≥0∞))^(n-1) := by
  have h := event_add_compl (explorationDraw n k hk) {draw | CollisionFree draw i}
  rw [exploration_collisionFree_probability hk i] at h
  have he : ({draw : Fin n → Fin k | CollisionFree draw i} : Set _)ᶜ =
      {draw | ¬ CollisionFree draw i} := rfl
  rw [he] at h
  apply ENNReal.eq_sub_of_add_eq
  · have hb : (((k-1 : ℕ) : ℝ≥0∞) / (k : ℝ≥0∞))^(n-1) ≤ 1 := by
      calc
        _ ≤ _ + (explorationDraw n k hk).toOuterMeasure {draw | ¬ CollisionFree draw i} := le_self_add
        _ = 1 := h
    exact ne_of_lt (lt_of_le_of_lt hb ENNReal.one_lt_top)
  · simpa [add_comm] using h

noncomputable def observationCount {n k T : ℕ} (i : Fin n) (a : Fin k)
    (x : Fin T → Fin n → Fin k) : ℕ := FinitePMF.eventCount (observes i a) x

noncomputable def collisionCount {n k T : ℕ} (i : Fin n)
    (x : Fin T → Fin n → Fin k) : ℕ :=
  FinitePMF.eventCount {draw | ¬ CollisionFree draw i} x

theorem observationCount_pgf {n k : ℕ} (hk : 0 < k) (T : ℕ) (i : Fin n)
    (a : Fin k) (z : ℝ≥0∞) :
    let q := (1 / (k : ℝ≥0∞)) * (((k-1 : ℕ) : ℝ≥0∞) / (k : ℝ≥0∞))^(n-1)
    ∑ x, explorationLaw n k T hk x * z ^ observationCount i a x =
      (q * z + (1-q))^T := by
  dsimp
  simp only [explorationLaw, observationCount]
  rw [FinitePMF.iid_count_pgf]
  have hc := event_add_compl (explorationDraw n k hk) (observes i a)
  have hp := exploration_observes_probability hk i a
  rw [hp] at hc ⊢
  have he : (explorationDraw n k hk).toOuterMeasure (observes i a)ᶜ =
      1 - (1 / (k : ℝ≥0∞)) * (((k-1 : ℕ) : ℝ≥0∞) / (k : ℝ≥0∞))^(n-1) := by
    apply ENNReal.eq_sub_of_add_eq
    · have hle : (1 / (k : ℝ≥0∞)) * (((k-1 : ℕ) : ℝ≥0∞) / (k : ℝ≥0∞))^(n-1) ≤ 1 := by
        calc
          _ ≤ _ + (explorationDraw n k hk).toOuterMeasure (observes i a)ᶜ := le_self_add
          _ = 1 := hc
      exact ne_of_lt (lt_of_le_of_lt hle ENNReal.one_lt_top)
    · simpa [add_comm] using hc
  rw [he]

theorem collisionCount_pgf {n k : ℕ} (hk : 0 < k) (T : ℕ) (i : Fin n)
    (z : ℝ≥0∞) :
    let b := (((k-1 : ℕ) : ℝ≥0∞) / (k : ℝ≥0∞))^(n-1)
    ∑ x, explorationLaw n k T hk x * z ^ collisionCount i x =
      ((1-b) * z + b)^T := by
  dsimp
  simp only [explorationLaw, collisionCount]
  rw [FinitePMF.iid_count_pgf,
    exploration_collision_probability hk i]
  have he : ({draw : Fin n → Fin k | ¬ CollisionFree draw i} : Set _)ᶜ =
      {draw | CollisionFree draw i} := by ext draw; simp
  rw [he, exploration_collisionFree_probability hk i]


theorem exploration_observes_lower {n k : ℕ} (hk : 0 < k) (hnk : n ≤ k)
    (i : Fin n) (a : Fin k) :
    (1 : ℝ≥0∞) / (4*k) ≤ (explorationDraw n k hk).toOuterMeasure (observes i a) := by
  rw [exploration_observes_probability hk i a]
  have hk0 : (k : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  have hb : (((k-1 : ℕ) : ℝ≥0∞) / (k : ℝ≥0∞)) ≤ 1 := by
    calc
      _ ≤ (k : ℝ≥0∞) / (k : ℝ≥0∞) := by
        gcongr
        exact_mod_cast (Nat.sub_le k 1)
      _ = 1 := ENNReal.div_self hk0 (by simp)
  calc
    _ ≤ (1 / (k : ℝ≥0∞)) * (((k-1 : ℕ) : ℝ≥0∞) / (k : ℝ≥0∞))^(k-1) :=
      uniform_hazard_lower k hk
    _ ≤ _ := mul_le_mul_right
      (pow_le_pow_of_le_one (zero_le _) hb (Nat.sub_le_sub_right hnk 1)) _


theorem observationCount_laplace {n k : ℕ} (hk : 0 < k) (T : ℕ) (i : Fin n)
    (a : Fin k) (eta : ℝ) :
    let q := (1 / (k : ℝ≥0∞)) * (((k-1 : ℕ) : ℝ≥0∞) / (k : ℝ≥0∞))^(n-1)
    ∑ x, explorationLaw n k T hk x *
      ENNReal.ofReal (Real.exp (-eta * (observationCount i a x : ℝ))) =
      (q * ENNReal.ofReal (Real.exp (-eta)) + (1-q))^T := by
  have he (m : ℕ) : ENNReal.ofReal (Real.exp (-eta * (m : ℝ))) =
      ENNReal.ofReal (Real.exp (-eta))^m := by
    rw [← ENNReal.ofReal_pow (Real.exp_nonneg _), ← Real.exp_nat_mul]
    congr 2
    ring
  simp_rw [he]
  exact observationCount_pgf hk T i a (ENNReal.ofReal (Real.exp (-eta)))


structure ExplorationFeedback (k : ℕ) where
  arm : Fin k
  collided : Bool
  reward : ℝ

noncomputable def explorationFeedback {n k T : ℕ} (x : Fin T → Fin n → Fin k)
    (rewards : Fin T → Fin k → ℝ) (i : Fin n) : Fin T → ExplorationFeedback k :=
  fun t => ⟨x t i, decide (¬ CollisionFree (x t) i),
    if CollisionFree (x t) i then rewards t (x t i) else 0⟩

noncomputable def localObservationCount {k T : ℕ} (f : Fin T → ExplorationFeedback k)
    (a : Fin k) : ℕ :=
  (Finset.univ.filter (fun t => (f t).arm = a ∧ (f t).collided = false)).card

noncomputable def localCollisionCount {k T : ℕ} (f : Fin T → ExplorationFeedback k) : ℕ :=
  (Finset.univ.filter (fun t => (f t).collided = true)).card

noncomputable def localRewardSum {k T : ℕ} (f : Fin T → ExplorationFeedback k)
    (a : Fin k) : ℝ :=
  ∑ t ∈ Finset.univ.filter (fun t => (f t).arm = a ∧ (f t).collided = false), (f t).reward

noncomputable def localEmpiricalMean {k T : ℕ} (f : Fin T → ExplorationFeedback k)
    (a : Fin k) : ℝ :=
  if localObservationCount f a = 0 then 0 else localRewardSum f a / localObservationCount f a

theorem localObservationCount_eq {n k T : ℕ} (x : Fin T → Fin n → Fin k)
    (rewards : Fin T → Fin k → ℝ) (i : Fin n) (a : Fin k) :
    localObservationCount (explorationFeedback x rewards i) a = observationCount i a x := by
  unfold localObservationCount observationCount FinitePMF.eventCount
  congr 1
  ext t
  simp [explorationFeedback, observes]

theorem localCollisionCount_eq {n k T : ℕ} (x : Fin T → Fin n → Fin k)
    (rewards : Fin T → Fin k → ℝ) (i : Fin n) :
    localCollisionCount (explorationFeedback x rewards i) = collisionCount i x := by
  unfold localCollisionCount collisionCount FinitePMF.eventCount
  congr 1
  ext t
  simp [explorationFeedback]

theorem localRewardSum_eq {n k T : ℕ} (x : Fin T → Fin n → Fin k)
    (rewards : Fin T → Fin k → ℝ) (i : Fin n) (a : Fin k) :
    localRewardSum (explorationFeedback x rewards i) a =
      ∑ t ∈ Finset.univ.filter (fun t => x t ∈ observes i a), rewards t a := by
  unfold localRewardSum
  apply Finset.sum_congr
  · ext t
    simp [explorationFeedback, observes]
  · intro t ht
    have h : x t i = a ∧ CollisionFree (x t) i := by
      simpa [explorationFeedback] using (Finset.mem_filter.mp ht).2
    simp [explorationFeedback, h.1, h.2]


namespace ExplorationCanary

theorem effective_probability :
    (explorationDraw 2 3 (by decide)).toOuterMeasure (observes (0 : Fin 2) (0 : Fin 3)) = 2/9 := by
  rw [exploration_observes_probability]
  norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num

theorem collision_probability :
    (explorationDraw 2 3 (by decide)).toOuterMeasure {draw | ¬ CollisionFree draw (0 : Fin 2)} = 1/3 := by
  rw [exploration_collision_probability]
  norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_sub_of_le (by norm_num [ENNReal.div_le_iff]) (by simp)]
  norm_num

theorem effective_pgf (T : ℕ) (z : ℝ≥0∞) :
    ∑ x, explorationLaw 2 3 T (by decide) x * z ^ observationCount (0 : Fin 2) (0 : Fin 3) x =
      ((2/9)*z+7/9)^T := by
  have h := observationCount_pgf (n := 2) (k := 3) (by decide) T (0 : Fin 2) (0 : Fin 3) z
  norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one] at h
  have hq : (1/3 : ℝ≥0∞) * (2/3) = 2/9 := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num
  have hc : (1 : ℝ≥0∞) - 2/9 = 7/9 := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    rw [ENNReal.toReal_sub_of_le (by norm_num [ENNReal.div_le_iff]) (by simp)]
    norm_num
  simpa only [hq, hc] using h

def mixedDraws : Fin 2 → Fin 2 → Fin 3 := fun t i =>
  if t = 0 then 0 else if i = 0 then 0 else 1

theorem mixed_counts : observationCount (0 : Fin 2) (0 : Fin 3) mixedDraws = 1 ∧
    collisionCount (0 : Fin 2) mixedDraws = 1 := by
  simp only [observationCount, collisionCount, FinitePMF.eventCount,
    Finset.card_eq_sum_ones, Finset.sum_filter, Fin.sum_univ_two]
  norm_num [mixedDraws, observes, CollisionFree, Fin.forall_fin_two]


theorem free_zero_reward :
    (explorationFeedback mixedDraws (fun _ _ => 0) (0 : Fin 2) (1 : Fin 2)).reward = 0 ∧
    (explorationFeedback mixedDraws (fun _ _ => 0) (0 : Fin 2) (1 : Fin 2)).collided = false := by
  norm_num [explorationFeedback, mixedDraws, CollisionFree, Fin.forall_fin_two]

theorem collision_zero_reward :
    (explorationFeedback mixedDraws (fun _ _ => 1) (0 : Fin 2) (0 : Fin 2)).reward = 0 ∧
    (explorationFeedback mixedDraws (fun _ _ => 1) (0 : Fin 2) (0 : Fin 2)).collided = true := by
  norm_num [explorationFeedback, mixedDraws, CollisionFree, Fin.forall_fin_two]

end ExplorationCanary
end BanditRLProof.MusicalChairs

namespace BanditRLProof.MusicalChairs
open MeasureTheory ProbabilityTheory

noncomputable def rewardLaw {k : ℕ} (nu : Fin k → Measure ℝ) (T : ℕ) :
    Measure (Fin T → Fin k → ℝ) := Measure.pi (fun _ : Fin T => Measure.pi nu)

instance rewardLaw_probability {k : ℕ} (nu : Fin k → Measure ℝ)
    [∀ a, IsProbabilityMeasure (nu a)] (T : ℕ) : IsProbabilityMeasure (rewardLaw nu T) := by
  unfold rewardLaw
  infer_instance

noncomputable def armMean {k : ℕ} (nu : Fin k → Measure ℝ) (a : Fin k) : ℝ :=
  ∫ y, y ∂nu a

theorem reward_coordinate_preserving {k T : ℕ} (nu : Fin k → Measure ℝ)
    [∀ a, IsProbabilityMeasure (nu a)] (t : Fin T) (a : Fin k) :
    MeasurePreserving (fun r : Fin T → Fin k → ℝ => r t a) (rewardLaw nu T) (nu a) := by
  exact (measurePreserving_eval nu a).comp
    (measurePreserving_eval (fun _ : Fin T => Measure.pi nu) t)

theorem reward_coordinate_mean {k T : ℕ} (nu : Fin k → Measure ℝ)
    [∀ a, IsProbabilityMeasure (nu a)] (t : Fin T) (a : Fin k) :
    (∫ r, r t a ∂rewardLaw nu T) = armMean nu a := by
  have hm := reward_coordinate_preserving nu t a
  calc
    _ = ∫ y, y ∂(rewardLaw nu T).map (fun r => r t a) :=
      (integral_map hm.measurable.aemeasurable measurable_id.aestronglyMeasurable).symm
    _ = _ := by rw [hm.map_eq]; rfl

theorem reward_coordinate_bounded {k T : ℕ} (nu : Fin k → Measure ℝ)
    [∀ a, IsProbabilityMeasure (nu a)]
    (hb : ∀ a, ∀ᵐ y ∂nu a, y ∈ Set.Icc (0 : ℝ) 1) (t : Fin T) (a : Fin k) :
    ∀ᵐ r ∂rewardLaw nu T, r t a ∈ Set.Icc (0 : ℝ) 1 :=
  (reward_coordinate_preserving nu t a).quasiMeasurePreserving.ae (hb a)

theorem reward_coordinate_subGaussian {k T : ℕ} (nu : Fin k → Measure ℝ)
    [∀ a, IsProbabilityMeasure (nu a)]
    (hb : ∀ a, ∀ᵐ y ∂nu a, y ∈ Set.Icc (0 : ℝ) 1) (t : Fin T) (a : Fin k) :
    HasSubgaussianMGF (fun r : Fin T → Fin k → ℝ => r t a - armMean nu a)
      (1/4 : NNReal) (rewardLaw nu T) := by
  have h := hasSubgaussianMGF_of_mem_Icc
    (reward_coordinate_preserving nu t a).measurable.aemeasurable
    (reward_coordinate_bounded nu hb t a)
  norm_num [reward_coordinate_mean] at h ⊢
  exact h

theorem reward_time_independent {k T : ℕ} (nu : Fin k → Measure ℝ)
    [∀ a, IsProbabilityMeasure (nu a)] (a : Fin k) :
    iIndepFun (fun t (r : Fin T → Fin k → ℝ) => r t a - armMean nu a) (rewardLaw nu T) := by
  apply iIndepFun_pi (Ω := fun _ : Fin T => Fin k → ℝ) (𝓧 := fun _ : Fin T => ℝ)
    (μ := fun _ : Fin T => Measure.pi nu)
    (X := fun _ (r : Fin k → ℝ) => r a - armMean nu a)
  intro t
  exact (show Measurable (fun r : Fin k → ℝ => r a - armMean nu a) from
    (measurable_pi_apply a).sub measurable_const).aemeasurable

theorem selected_sum_subGaussian {k T : ℕ} (nu : Fin k → Measure ℝ)
    [∀ a, IsProbabilityMeasure (nu a)]
    (hb : ∀ a, ∀ᵐ y ∂nu a, y ∈ Set.Icc (0 : ℝ) 1) (S : Finset (Fin T)) (a : Fin k) :
    HasSubgaussianMGF (fun r : Fin T → Fin k → ℝ => ∑ t ∈ S, (r t a - armMean nu a))
      ((S.card : NNReal)/4) (rewardLaw nu T) := by
  have h := HasSubgaussianMGF.sum_of_iIndepFun (reward_time_independent nu a)
    (fun t (_ : t ∈ S) => reward_coordinate_subGaussian nu hb t a)
  simpa [div_eq_mul_inv] using h


theorem selected_sum_abs_tail {k T : ℕ} (nu : Fin k → Measure ℝ)
    [∀ a, IsProbabilityMeasure (nu a)]
    (hb : ∀ a, ∀ᵐ y ∂nu a, y ∈ Set.Icc (0 : ℝ) 1) (S : Finset (Fin T)) (a : Fin k)
    (u : ℝ) (hu : 0 ≤ u) :
    (rewardLaw nu T).real {r | u ≤ |∑ t ∈ S, (r t a - armMean nu a)|} ≤
      2 * Real.exp (-u^2 / (2 * ((S.card : ℝ)/4))) := by
  have h := selected_sum_subGaussian nu hb S a
  have hp := h.measure_ge_le hu
  have hn := h.neg.measure_ge_le hu
  have he : {r : Fin T → Fin k → ℝ | u ≤ |∑ t ∈ S, (r t a - armMean nu a)|} =
      {r | u ≤ ∑ t ∈ S, (r t a - armMean nu a)} ∪
      {r | u ≤ -(∑ t ∈ S, (r t a - armMean nu a))} := by
    ext r
    simp only [Set.mem_setOf_eq, Set.mem_union, le_abs]
  rw [he]
  have hU := measureReal_union_le (μ := rewardLaw nu T)
    {r | u ≤ ∑ t ∈ S, (r t a - armMean nu a)}
    {r | u ≤ -(∑ t ∈ S, (r t a - armMean nu a))}
  simp only [Pi.neg_apply, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_ofNat] at hp hn
  linarith

noncomputable def selectedMean {k T : ℕ} (S : Finset (Fin T)) (a : Fin k)
    (r : Fin T → Fin k → ℝ) : ℝ :=
  if S.card = 0 then 0 else (∑ t ∈ S, r t a) / S.card

theorem selected_centered_sum {k T : ℕ} (nu : Fin k → Measure ℝ)
    (S : Finset (Fin T)) (a : Fin k) (hS : 0 < S.card) (r : Fin T → Fin k → ℝ) :
    (∑ t ∈ S, (r t a - armMean nu a)) = (S.card : ℝ) * (selectedMean S a r - armMean nu a) := by
  have h0 : (S.card : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hS)
  simp only [selectedMean, if_neg (Nat.ne_of_gt hS), Finset.sum_sub_distrib,
    Finset.sum_const, nsmul_eq_mul]
  field_simp

theorem selectedMean_tail_pos {k T : ℕ} (nu : Fin k → Measure ℝ)
    [∀ a, IsProbabilityMeasure (nu a)]
    (hb : ∀ a, ∀ᵐ y ∂nu a, y ∈ Set.Icc (0 : ℝ) 1) (S : Finset (Fin T)) (a : Fin k)
    (hS : 0 < S.card) (eps : ℝ) (heps : 0 ≤ eps) :
    (rewardLaw nu T).real {r | eps/2 ≤ |selectedMean S a r - armMean nu a|} ≤
      2 * Real.exp (-(S.card : ℝ) * eps^2 / 2) := by
  have hD : 0 < (S.card : ℝ) := by exact_mod_cast hS
  have he : {r : Fin T → Fin k → ℝ | eps/2 ≤ |selectedMean S a r - armMean nu a|} =
      {r | (S.card : ℝ) * eps/2 ≤ |∑ t ∈ S, (r t a - armMean nu a)|} := by
    ext r
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq, selected_centered_sum nu S a hS r,
      abs_mul, abs_of_pos hD]
    rw [mul_div_assoc, mul_le_mul_iff_right₀ hD]
  rw [he]
  have h := selected_sum_abs_tail nu hb S a ((S.card : ℝ)*eps/2) (by positivity)
  convert h using 1
  congr 2
  field_simp
  ring


theorem selectedMean_tail {k T : ℕ} (nu : Fin k → Measure ℝ)
    [∀ a, IsProbabilityMeasure (nu a)]
    (hb : ∀ a, ∀ᵐ y ∂nu a, y ∈ Set.Icc (0 : ℝ) 1) (S : Finset (Fin T)) (a : Fin k)
    (eps : ℝ) (heps : 0 ≤ eps) :
    (rewardLaw nu T).real {r | eps/2 ≤ |selectedMean S a r - armMean nu a|} ≤
      2 * Real.exp (-(S.card : ℝ) * eps^2 / 2) := by
  by_cases hS : S.card = 0
  · have h : (rewardLaw nu T).real {r | eps/2 ≤ |selectedMean S a r - armMean nu a|} ≤ 1 :=
      measureReal_le_one
    simpa [hS] using h.trans (by norm_num : (1 : ℝ) ≤ 2)
  · exact selectedMean_tail_pos nu hb S a (Nat.pos_of_ne_zero hS) eps heps

noncomputable def observedTimes {n k T : ℕ} (x : Fin T → Fin n → Fin k)
    (i : Fin n) (a : Fin k) : Finset (Fin T) :=
  Finset.univ.filter (fun t => x t ∈ observes i a)

theorem localEmpiricalMean_eq_selectedMean {n k T : ℕ} (x : Fin T → Fin n → Fin k)
    (r : Fin T → Fin k → ℝ) (i : Fin n) (a : Fin k) :
    localEmpiricalMean (explorationFeedback x r i) a = selectedMean (observedTimes x i a) a r := by
  simp only [localEmpiricalMean, localObservationCount_eq, localRewardSum_eq,
    selectedMean, observedTimes, observationCount, FinitePMF.eventCount]

theorem localEmpiricalMean_fixed_tail {n k T : ℕ} (nu : Fin k → Measure ℝ)
    [∀ a, IsProbabilityMeasure (nu a)]
    (hb : ∀ a, ∀ᵐ y ∂nu a, y ∈ Set.Icc (0 : ℝ) 1)
    (x : Fin T → Fin n → Fin k) (i : Fin n) (a : Fin k) (eps : ℝ) (heps : 0 ≤ eps) :
    (rewardLaw nu T).real {r | eps/2 ≤ |localEmpiricalMean (explorationFeedback x r i) a - armMean nu a|} ≤
      2 * Real.exp (-(observationCount i a x : ℝ) * eps^2 / 2) := by
  simp_rw [localEmpiricalMean_eq_selectedMean]
  exact selectedMean_tail nu hb (observedTimes x i a) a eps heps

theorem measurable_selectedMean {k T : ℕ} (S : Finset (Fin T)) (a : Fin k) :
    Measurable (selectedMean S a) := by
  unfold selectedMean
  split_ifs <;> fun_prop

theorem measurable_jointEmpiricalMean {n k T : ℕ} (i : Fin n) (a : Fin k) :
    Measurable (fun z : (Fin T → Fin n → Fin k) × (Fin T → Fin k → ℝ) =>
      localEmpiricalMean (explorationFeedback z.1 z.2 i) a) := by
  apply measurable_from_prod_countable_right
  intro x
  simp_rw [localEmpiricalMean_eq_selectedMean]
  exact measurable_selectedMean (observedTimes x i a) a

noncomputable def explorationRewardLaw {n k T : ℕ} (hk : 0 < k)
    (nu : Fin k → Measure ℝ) :
    Measure ((Fin T → Fin n → Fin k) × (Fin T → Fin k → ℝ)) :=
  (explorationLaw n k T hk).toMeasure.prod (rewardLaw nu T)

instance explorationRewardLaw_probability {n k T : ℕ} (hk : 0 < k)
    (nu : Fin k → Measure ℝ) [∀ a, IsProbabilityMeasure (nu a)] :
    IsProbabilityMeasure (explorationRewardLaw (n := n) (T := T) hk nu) := by
  unfold explorationRewardLaw
  infer_instance

def meanBadEvent {n k T : ℕ} (nu : Fin k → Measure ℝ) (i : Fin n) (a : Fin k) (eps : ℝ) :
    Set ((Fin T → Fin n → Fin k) × (Fin T → Fin k → ℝ)) :=
  {z | eps/2 ≤ |localEmpiricalMean (explorationFeedback z.1 z.2 i) a - armMean nu a|}

theorem measurableSet_meanBadEvent {n k T : ℕ} (nu : Fin k → Measure ℝ)
    (i : Fin n) (a : Fin k) (eps : ℝ) : MeasurableSet (meanBadEvent (T := T) nu i a eps) := by
  exact measurableSet_le measurable_const ((measurable_jointEmpiricalMean i a).sub_const (armMean nu a)).abs

theorem meanBadEvent_mixture {n k T : ℕ} (hk : 0 < k) (nu : Fin k → Measure ℝ)
    [∀ a, IsProbabilityMeasure (nu a)] (i : Fin n) (a : Fin k) (eps : ℝ) :
    explorationRewardLaw hk nu (meanBadEvent (T := T) nu i a eps) =
      ∑ x, explorationLaw n k T hk x *
        rewardLaw nu T {r | eps/2 ≤ |localEmpiricalMean (explorationFeedback x r i) a - armMean nu a|} := by
  rw [explorationRewardLaw, Measure.prod_apply (measurableSet_meanBadEvent nu i a eps), lintegral_fintype]
  apply Finset.sum_congr rfl
  intro x _
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton x), mul_comm]
  rfl


theorem meanBadEvent_count_bound {n k T : ℕ} (hk : 0 < k) (nu : Fin k → Measure ℝ)
    [∀ a, IsProbabilityMeasure (nu a)]
    (hb : ∀ a, ∀ᵐ y ∂nu a, y ∈ Set.Icc (0 : ℝ) 1)
    (i : Fin n) (a : Fin k) (eps : ℝ) (heps : 0 ≤ eps) :
    let q := (1 / (k : ℝ≥0∞)) * (((k-1 : ℕ) : ℝ≥0∞) / (k : ℝ≥0∞))^(n-1)
    explorationRewardLaw hk nu (meanBadEvent (T := T) nu i a eps) ≤
      2 * (q * ENNReal.ofReal (Real.exp (-(eps^2/2))) + (1-q))^T := by
  dsimp
  rw [meanBadEvent_mixture]
  calc
    _ ≤ ∑ x, explorationLaw n k T hk x * ENNReal.ofReal
        (2 * Real.exp (-(observationCount i a x : ℝ) * eps^2 / 2)) := by
      apply Finset.sum_le_sum
      intro x _
      apply mul_le_mul_right
      rw [← ofReal_measureReal (μ := rewardLaw nu T)]
      exact ENNReal.ofReal_le_ofReal (localEmpiricalMean_fixed_tail nu hb x i a eps heps)
    _ = 2 * (∑ x, explorationLaw n k T hk x * ENNReal.ofReal
        (Real.exp (-(eps^2/2) * (observationCount i a x : ℝ)))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      have he : -(observationCount i a x : ℝ) * eps^2 / 2 =
          -(eps^2/2) * (observationCount i a x : ℝ) := by ring
      rw [he, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num only [ENNReal.ofReal_ofNat]
      ring
    _ = _ := by rw [observationCount_laplace]


theorem half_le_one_sub_exp_neg (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x/2 ≤ 1 - Real.exp (-x) := by
  have hprod : (1+x) * Real.exp (-x) ≤ 1 := by
    calc
      _ ≤ Real.exp x * Real.exp (-x) := by
        gcongr
        linarith [Real.add_one_le_exp x]
      _ = 1 := by rw [← Real.exp_add]; simp
  have hquad : 0 ≤ x * (1-x) := mul_nonneg hx0 (sub_nonneg.mpr hx1)
  by_contra hh
  have hlt : (1-x/2)*(1+x) < Real.exp (-x)*(1+x) := by
    apply mul_lt_mul_of_pos_right _ (by linarith)
    linarith
  nlinarith

theorem count_mixture_exp_bound (q eps : ℝ) (T : ℕ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (heps0 : 0 ≤ eps) (heps1 : eps ≤ 1) :
    (q * Real.exp (-(eps^2/2)) + (1-q))^T ≤
      Real.exp (-(T : ℝ)*q*eps^2/4) := by
  have hsmall := half_le_one_sub_exp_neg (eps^2/2) (by positivity) (by nlinarith)
  have hbase : q * Real.exp (-(eps^2/2)) + (1-q) ≤
      Real.exp (-q*(1-Real.exp (-(eps^2/2)))) := by
    have h := Real.add_one_le_exp (-q*(1-Real.exp (-(eps^2/2))))
    nlinarith
  calc
    _ ≤ (Real.exp (-q*(1-Real.exp (-(eps^2/2)))))^T := by
      gcongr
      exact add_nonneg (mul_nonneg hq0 (Real.exp_nonneg _)) (sub_nonneg.mpr hq1)
    _ = Real.exp ((T : ℝ) * (-q*(1-Real.exp (-(eps^2/2))))) :=
      (Real.exp_nat_mul _ _).symm
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hmul := mul_le_mul_of_nonneg_left hsmall (mul_nonneg (Nat.cast_nonneg T) hq0)
      nlinarith


noncomputable def explorationProbReal (n k : ℕ) : ℝ :=
  (1 / (k : ℝ)) * (((k-1 : ℕ) : ℝ) / (k : ℝ))^(n-1)

theorem explorationProbReal_nonneg (n k : ℕ) : 0 ≤ explorationProbReal n k := by
  unfold explorationProbReal
  positivity

theorem explorationProbReal_le_one (n k : ℕ) (hk : 0 < k) : explorationProbReal n k ≤ 1 := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hb : (((k-1 : ℕ) : ℝ) / (k : ℝ)) ≤ 1 := by
    rw [div_le_one hkR]
    exact_mod_cast (Nat.sub_le k 1)
  have hp : ((((k-1 : ℕ) : ℝ) / (k : ℝ))^(n-1)) ≤ 1 := by
    calc
      _ ≤ (1 : ℝ)^(n-1) := by gcongr
      _ = 1 := one_pow _
  have hdiv : (1 : ℝ)/k ≤ 1 := by
    rw [div_le_one hkR]
    exact_mod_cast (Nat.succ_le_iff.mpr hk)
  exact (mul_le_mul_of_nonneg_left hp (by positivity)).trans (by simpa using hdiv)

theorem explorationProbReal_lower (n k : ℕ) (hk : 0 < k) (hnk : n ≤ k) :
    (1 : ℝ)/(4*k) ≤ explorationProbReal n k := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hb : (((k-1 : ℕ) : ℝ) / (k : ℝ)) ≤ 1 := by
    rw [div_le_one hkR]
    exact_mod_cast (Nat.sub_le k 1)
  calc
    _ ≤ (1/(k : ℝ)) * (((k-1 : ℕ) : ℝ)/(k : ℝ))^(k-1) := real_uniform_hazard_lower k hk
    _ ≤ explorationProbReal n k := mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one (by positivity) hb (Nat.sub_le_sub_right hnk 1)) (by positivity)

theorem ofReal_explorationProbReal (n k : ℕ) (hk : 0 < k) :
    ENNReal.ofReal (explorationProbReal n k) =
      (1/(k : ℝ≥0∞)) * (((k-1 : ℕ) : ℝ≥0∞)/(k : ℝ≥0∞))^(n-1) := by
  unfold explorationProbReal
  simp only [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1/k),
    ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) < k), ENNReal.ofReal_one,
    ENNReal.ofReal_natCast,
    ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ ((k-1 : ℕ) : ℝ)/(k : ℝ))]

theorem meanBadEvent_exponential_bound {n k T : ℕ} (hk : 0 < k) (hnk : n ≤ k)
    (nu : Fin k → Measure ℝ) [∀ a, IsProbabilityMeasure (nu a)]
    (hb : ∀ a, ∀ᵐ y ∂nu a, y ∈ Set.Icc (0 : ℝ) 1)
    (i : Fin n) (a : Fin k) (eps : ℝ) (heps0 : 0 ≤ eps) (heps1 : eps ≤ 1) :
    explorationRewardLaw hk nu (meanBadEvent (T := T) nu i a eps) ≤
      ENNReal.ofReal (2 * Real.exp (-(T : ℝ)*eps^2/(16*k))) := by
  let q := explorationProbReal n k
  have hq0 : 0 ≤ q := explorationProbReal_nonneg n k
  have hq1 : q ≤ 1 := explorationProbReal_le_one n k hk
  have hbase : 0 ≤ q * Real.exp (-(eps^2/2)) + (1-q) :=
    add_nonneg (mul_nonneg hq0 (Real.exp_nonneg _)) (sub_nonneg.mpr hq1)
  have hconv : 2 * (((1/(k : ℝ≥0∞)) * (((k-1 : ℕ) : ℝ≥0∞)/(k : ℝ≥0∞))^(n-1)) *
      ENNReal.ofReal (Real.exp (-(eps^2/2))) +
      (1-((1/(k : ℝ≥0∞)) * (((k-1 : ℕ) : ℝ≥0∞)/(k : ℝ≥0∞))^(n-1))))^T =
      ENNReal.ofReal (2 * (q * Real.exp (-(eps^2/2)) + (1-q))^T) := by
    simp only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_ofNat, ENNReal.ofReal_pow hbase,
      ENNReal.ofReal_add (mul_nonneg hq0 (Real.exp_nonneg _)) (sub_nonneg.mpr hq1),
      ENNReal.ofReal_mul hq0, ENNReal.ofReal_sub 1 hq0, ENNReal.ofReal_one,
      q, ofReal_explorationProbReal n k hk]
  calc
    _ ≤ _ := meanBadEvent_count_bound hk nu hb i a eps heps0
    _ = _ := hconv
    _ ≤ ENNReal.ofReal (2 * Real.exp (-(T : ℝ)*q*eps^2/4)) := by
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_left (count_mixture_exp_bound q eps T hq0 hq1 heps0 heps1) (by norm_num)
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.exp_le_exp.mpr
      have hmul := mul_le_mul_of_nonneg_left (explorationProbReal_lower n k hk hnk)
        (by positivity : 0 ≤ (T : ℝ)*eps^2/4)
      calc
        _ = -((T : ℝ)*eps^2/4*q) := by ring
        _ ≤ -((T : ℝ)*eps^2/4*(1/(4*k))) := neg_le_neg hmul
        _ = _ := by ring


def allMeanBadEvent {n k T : ℕ} (nu : Fin k → Measure ℝ) (eps : ℝ) :
    Set ((Fin T → Fin n → Fin k) × (Fin T → Fin k → ℝ)) :=
  ⋃ i : Fin n, ⋃ a : Fin k, meanBadEvent nu i a eps

theorem allMeanBadEvent_exponential_bound {n k T : ℕ} (hk : 0 < k) (hnk : n ≤ k)
    (nu : Fin k → Measure ℝ) [∀ a, IsProbabilityMeasure (nu a)]
    (hb : ∀ a, ∀ᵐ y ∂nu a, y ∈ Set.Icc (0 : ℝ) 1)
    (eps : ℝ) (heps0 : 0 ≤ eps) (heps1 : eps ≤ 1) :
    explorationRewardLaw hk nu (allMeanBadEvent (n := n) (T := T) nu eps) ≤
      ENNReal.ofReal (2 * (k : ℝ)^2 * Real.exp (-(T : ℝ)*eps^2/(16*k))) := by
  let M := explorationRewardLaw (n := n) (T := T) hk nu
  let B := ENNReal.ofReal (2 * Real.exp (-(T : ℝ)*eps^2/(16*k)))
  have hnkE : (n : ℝ≥0∞) ≤ k := by exact_mod_cast hnk
  calc
    _ ≤ ∑ i : Fin n, M (⋃ a : Fin k, meanBadEvent nu i a eps) := by
      simpa only [tsum_fintype] using (measure_iUnion_le (μ := M)
        (fun i : Fin n => ⋃ a : Fin k, meanBadEvent nu i a eps))
    _ ≤ ∑ i : Fin n, ∑ a : Fin k, M (meanBadEvent nu i a eps) := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [tsum_fintype] using (measure_iUnion_le (μ := M) (fun a : Fin k => meanBadEvent nu i a eps))
    _ ≤ ∑ _i : Fin n, ∑ _a : Fin k, B := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro a _
      exact meanBadEvent_exponential_bound hk hnk nu hb i a eps heps0 heps1
    _ = (n : ℝ≥0∞) * (k : ℝ≥0∞) * B := by simp [mul_assoc]
    _ ≤ (k : ℝ≥0∞) * (k : ℝ≥0∞) * B := by gcongr
    _ = _ := by
      simp only [B, ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2*(k : ℝ)^2),
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat,
        ENNReal.ofReal_pow (Nat.cast_nonneg k), ENNReal.ofReal_natCast]
      ring

theorem mean_exploration_threshold (k T : ℕ) (hk : 0 < k) (eps delta : ℝ)
    (heps : 0 < eps) (hdelta : 0 < delta)
    (hT : (16*(k : ℝ)/eps^2) * Real.log (4*(k : ℝ)^2/delta) ≤ T) :
    2*(k : ℝ)^2 * Real.exp (-(T : ℝ)*eps^2/(16*k)) ≤ delta/2 := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hlog : Real.log (4*(k : ℝ)^2/delta) ≤ (T : ℝ)*eps^2/(16*k) := by
    have hmul := mul_le_mul_of_nonneg_right hT (by positivity : 0 ≤ eps^2/(16*(k : ℝ)))
    have he : ((16*(k : ℝ)/eps^2) * Real.log (4*(k : ℝ)^2/delta)) * (eps^2/(16*(k : ℝ))) =
        Real.log (4*(k : ℝ)^2/delta) := by field_simp
    rw [he] at hmul
    simpa only [mul_div_assoc] using hmul
  calc
    _ ≤ 2*(k : ℝ)^2 * Real.exp (-Real.log (4*(k : ℝ)^2/delta)) := by
      gcongr
      convert neg_le_neg hlog using 1
      ring
    _ = delta/2 := by
      rw [Real.exp_neg, Real.exp_log (by positivity)]
      field_simp
      ring

theorem allMeanBadEvent_le_half_delta {n k T : ℕ} (hk : 0 < k) (hnk : n ≤ k)
    (nu : Fin k → Measure ℝ) [∀ a, IsProbabilityMeasure (nu a)]
    (hb : ∀ a, ∀ᵐ y ∂nu a, y ∈ Set.Icc (0 : ℝ) 1)
    (eps delta : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1) (hdelta : 0 < delta)
    (hT : (16*(k : ℝ)/eps^2) * Real.log (4*(k : ℝ)^2/delta) ≤ T) :
    explorationRewardLaw hk nu (allMeanBadEvent (n := n) (T := T) nu eps) ≤
      ENNReal.ofReal (delta/2) := by
  exact (allMeanBadEvent_exponential_bound hk hnk nu hb eps heps.le heps1).trans
    (ENNReal.ofReal_le_ofReal (mean_exploration_threshold k T hk eps delta heps hdelta hT))



def allMeanAccurate {n k T : ℕ} (nu : Fin k → Measure ℝ) (eps : ℝ) :
    Set ((Fin T → Fin n → Fin k) × (Fin T → Fin k → ℝ)) :=
  {z | ∀ i : Fin n, ∀ a : Fin k,
    |localEmpiricalMean (explorationFeedback z.1 z.2 i) a - armMean nu a| < eps/2}

theorem allMeanAccurate_eq_compl {n k T : ℕ} (nu : Fin k → Measure ℝ) (eps : ℝ) :
    allMeanAccurate (n := n) (T := T) nu eps = (allMeanBadEvent nu eps)ᶜ := by
  ext z
  simp [allMeanAccurate, allMeanBadEvent, meanBadEvent]

theorem allMeanAccurate_probability {n k T : ℕ} (hk : 0 < k) (hnk : n ≤ k)
    (nu : Fin k → Measure ℝ) [∀ a, IsProbabilityMeasure (nu a)]
    (hb : ∀ a, ∀ᵐ y ∂nu a, y ∈ Set.Icc (0 : ℝ) 1)
    (eps delta : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1) (hdelta : 0 < delta)
    (hT : (16*(k : ℝ)/eps^2) * Real.log (4*(k : ℝ)^2/delta) ≤ T) :
    1 - ENNReal.ofReal (delta/2) ≤
      explorationRewardLaw hk nu (allMeanAccurate (n := n) (T := T) nu eps) := by
  have hm : MeasurableSet (allMeanBadEvent (n := n) (T := T) nu eps) :=
    MeasurableSet.iUnion (fun i => MeasurableSet.iUnion (fun a => measurableSet_meanBadEvent nu i a eps))
  rw [allMeanAccurate_eq_compl, measure_compl hm (by finiteness), measure_univ]
  exact tsub_le_tsub_left (allMeanBadEvent_le_half_delta hk hnk nu hb eps delta heps heps1 hdelta hT) 1

namespace RewardCanary

noncomputable def unitUniform : Measure ℝ := volume.restrict (Set.Icc 0 1)

instance unitUniform_probability : IsProbabilityMeasure unitUniform := by
  constructor
  norm_num [unitUniform, Measure.restrict_apply_univ]

theorem unitUniform_bounded : ∀ᵐ y ∂unitUniform, y ∈ Set.Icc (0 : ℝ) 1 := by
  exact ae_restrict_mem measurableSet_Icc

theorem continuous_reward_tail (eps : ℝ) (heps0 : 0 ≤ eps) (heps1 : eps ≤ 1) :
    explorationRewardLaw (n := 2) (T := 2) (by decide) (fun _ : Fin 3 => unitUniform)
      (meanBadEvent (fun _ : Fin 3 => unitUniform) (0 : Fin 2) (0 : Fin 3) eps) ≤
      ENNReal.ofReal (2 * Real.exp (-eps^2/24)) := by
  have h := meanBadEvent_exponential_bound (n := 2) (T := 2) (k := 3) (by decide) (by decide)
    (fun _ => unitUniform) (fun _ => unitUniform_bounded) (0 : Fin 2) (0 : Fin 3) eps heps0 heps1
  convert h using 1
  congr 3
  norm_num
  ring

theorem selected_single_value (r : Fin 2 → Fin 3 → ℝ) :
    selectedMean ({1} : Finset (Fin 2)) (0 : Fin 3) r = r 1 0 := by
  simp [selectedMean]

theorem selected_empty_zero (r : Fin 2 → Fin 3 → ℝ) :
    selectedMean (∅ : Finset (Fin 2)) (0 : Fin 3) r = 0 := by
  simp [selectedMean]

end RewardCanary
end BanditRLProof.MusicalChairs
```

</details>
