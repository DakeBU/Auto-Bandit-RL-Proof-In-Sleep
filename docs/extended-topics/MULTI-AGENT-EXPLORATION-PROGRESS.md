# Musical Chairs exploration: actual action and observation-count laws

Source: Rosenski, Shamir and Szlak, *Multi-Player Bandits -- a Musical Chairs
Approach*, ICML2016 PMLR48:155--163, static Algorithm1 and supplement A.1
Lemmas2/3. The pinned official source hashes, exact full-learner target and
separately reviewed corrections remain in MULTI-AGENT-CONTRACT.md. This is a
scratch probability/readout checkpoint, not a completed concentration theorem
or an integrated full learner. Exact execution and semantic evidence belong in
runs/extended-topics-20260920/multi-agent-exploration-review.json.

## Model, actual law, and local information

Take n players, k>0 arms and a finite exploration duration T. In each round,
every player independently draws uniformly from all k arms. explorationDraw
reuses the existing jointDraw on full candidate sets. explorationLaw is an
actual PMF on complete finite action schedules x:Fin T -> Fin n -> Fin k,
whose mass is the product of the constructed one-round masses. Its
normalization is proved, not assumed. The generic FinitePMF.iid helper and
product-expectation identity are used by BOTH observation and collision counts.

For tagged player i and arm a, observes(i,a) means x_i=a and no other player
chooses x_i in that round. A collision means the negation of this CollisionFree
event. These events depend on actual joint actions, not independent synthetic
Bernoulli variables. Indicators for different players or arms in the SAME
round are not asserted independent. The independence across rounds follows
from the constructed product masses and the proved product-expectation identity.

The deterministic readout accepts any real array rewards(t,a). It returns the
player's own action, a separate collision bit, and zero on collision or that
arm's array value otherwise. No law for this reward array is constructed here.
Local observation count, collision count, reward sum and empirical mean take
ONLY the player's feedback sequence and arm labels, not n. An empty empirical
mean is explicitly zero. Three identities prove these local statistics equal
the actual joint-action counts and selected reward sum. Thus the global model
may index players without feeding true n into local statistics. Full local
population estimation/ranking/policy construction is still open.

## Exact one-round probabilities

Write b=((k-1)/k)^(n-1), with natural predecessor k-1 in Lean. For every player
and arm, the actual law satisfies

    P(observes(i,a)) = q = (1/k) b,
    P(no collision for i) = b,
    P(collision for i) = 1-b.

To prove q, identify observes(i,a) with the existing isolation rectangle: the
tagged coordinate equals a and every other coordinate avoids a. The existing
jointDraw rectangle factorization gives one factor1/k and n-1 factors(k-1)/k.
Then partition collision-free actions by the tagged player's arm. These k
events are disjoint by their actual arm coordinate, so their total mass is kq.
Use the actual PMF complement identity to obtain collision mass1-b. No collision
probability is imported as an assumption.

If n<=k, decreasing powers of a base in[0,1] and the already proved conservative
uniform_hazard_lower at k imply q>=1/(4k). This is a reusable cross-phase use of
the existing numerical producer; it does not assume the future observation
count is large. The source full learner requires1<=n<k; this component permits
n=k. Tagged statements have i:Fin n and hence exclude n=0; the underlying empty
player schedule is still defined. For k=1,n=1, exponent zero uses0^0=1 and the
exact observation probability is1, with collision probability0.

## Constructed finite counts and exact transforms

For any finite PMF p and event E, eventCount E x counts times t<T with x(t) in E.
The actual product PMF satisfies, for z in the nonnegative extended reals,

    sum_x iid(p,T)(x) z^(eventCount E x)
      = (p(E) z + p(complement E))^T.

Proof: z^count is the product over times of the weight z on the event and1 on
its complement. Distribute finite products of finite sums. Each one-round
weighted sum partitions exactly into p(E)z+p(complement E). This proves the
transform of the ACTUAL count. We do not merely postulate a Binomial count, and
no equality with Mathlib's named Binomial distribution is claimed yet.

Specializing the same generic producer twice gives

    E[z^D_ia] = (q z + 1-q)^T,
    E[z^C_i] = ((1-b) z + b)^T,

where D_ia and C_i are counts computed from the actual action schedule.
The same observation-count identity also gives, for every real eta,

    E[exp(-eta D_ia)] = (q exp(-eta) + 1-q)^T,

represented exactly with ENNReal.ofReal(exp(...)) on both sides. This is an
exact transform, not a tail bound. Every time sum and support is finite. The
PGF allows z=0 and z=infinity with Lean's extended-real zero-product/power
conventions; the exponential specialization uses finite positive z. At T=0
the count is zero and both sides are1.

## Six concrete diagnostic theorems

With n=2,k=3 the actual probabilities are q=2/9 and collision mass1/3. The
observation PGF is ((2/9)z+7/9)^T for every finite T. A two-round schedule first
makes both players choose arm0, then chooses distinct arms0 and1. For player0,
the arm0 observation count and collision count both equal1. With zero latent
rewards, the second round has reward0 and collision=false. With unit latent
rewards, the first round has reward0 and collision=true. These examples verify
that zero reward is not used to detect collisions. This is NOT the mandatory
full-learner stochastic canary: no reward distribution, population estimate,
ranking or exploration-to-coordination switch is executed here.

## Remaining obligations and reuse boundary

Next construct the joint law of these action schedules and arbitrary stationary
[0,1] arm reward arrays, then derive conditional selected-reward laws given the
reward-independent action schedule. Prove the random-count two-sided mean tail,
collision-count Hoeffding, all-player union bounds, total inverse-log rounding,
rank boundary preservation and the actual good event. Finally identify the
fresh post-exploration process with the already accepted coordination law and
assemble the full regret with delta*n*T. No supplied good event, concentration
bound or oracle n is allowed to replace these producers.

Mathlib reuse: PMF.ofFintype, Fintype.prod_sum, finite sums/products, PMF outer
mass, finite ENNReal arithmetic and Real.exp_nat_mul. BanditRLProof reuse:
jointDraw, jointDraw_rectangle_product, isolationWindow, CollisionFree,
event_add_compl and uniform_hazard_lower. No toolchain/dependency changes.
The generic finite product/count producer has two actual consumers, but public
shared-module extraction is pending. This file remains scratch-only; previous
production gates do not validate this new source. No topic completion,
main-branch merge, deployment or ICLR evaluation is claimed.

## Exact scratch Lean

<details><summary>Actual finite laws, local statistics, proofs and examples</summary>

```lean
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
```

</details>
