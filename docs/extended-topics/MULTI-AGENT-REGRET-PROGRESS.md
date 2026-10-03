# Actual coordination pseudo-regret: scratch proof checkpoint

Source: Jonathan Rosenski, Ohad Shamir and Liran Szlak, *Multi-Player Bandits --
a Musical Chairs Approach*, ICML2016 PMLR48:155--163, static Algorithm2 and
supplement A.1 Lemma4. Pinned official main and supplement, exact hashes and
reviewed source repairs are in MULTI-AGENT-CONTRACT.md. This checkpoint closes
the previously missing coordination regret charge, not the unknown-N learner.

## Objects and statement

There are n players and k arms. A fixed player's state stores its arm; an
unfixed player's state is none. Actions and collision-free events use the
existing actual coordination definitions. Let S be a nonempty set of n arms,
and let every arm mean mu(a) lie in [0,1]. Let U(s) count unfixed players.
For an actual draw vector d, define

    reward(s,d) = sum_i 1{no other player chooses action_i} mu(action_i),
    r(s,d) = sum_(a in S) mu(a) - reward(s,d).

The deterministic theorem proves r(s,d) <= 2 U(s) whenever fixed arms are
distinct and belong to S. It does not require the draw vector to lie in S.
If all draws lie in S, r(s,d) >= 0 as well. Under the actual common-S stateLaw
and fresh jointDraw, both support invariants are produced by existing theorems.
For every finite T, including zero,

    sum_(t<T) sum_s p_t(s) sum_d q(d) r(s,d) <= 8 n^2.

The terminal expectedCoordinationRegret_real_le is this ordinary REAL sum with
real PMF weights. Its ENNReal companion uses ofReal(r), but a separate exact
conversion proves equality with the real expectation: negative values outside
the support carry zero weight; r is nonnegative on supported state/draw pairs.
Thus truncation does not change the actual supported random quantity.

## Derivation

Let F be the fixed players, H the fixed players suffering a collision, and
B = F minus H. Every i in H has a distinct player j choosing the same arm.
Such j cannot be fixed: distinct fixed arms would imply j=i. Choose one such
unfixed partner per i. If two i's choose the same partner, their actions are
equal and fixed-arm injectivity makes them equal. Hence |H| <= U. Since
|F|+U=n and |B|+|H|=|F|, n <= |B|+2U.

The actions of B are distinct and form A subset S, with |A|=|B|. Each is
collision-free, so actual reward is at least sum_(a in A) mu(a); contributions
of other successful players are nonnegative. Therefore

    r <= sum_(a in S minus A) mu(a) <= |S minus A| <= 2U.

For nonnegative regret on support, all successful players' actions are
pairwise distinct and inside S. Their total mean is therefore at most the
full S mean. This argument does not assume that S is a globally best set.
When the full learner produces the true top-n set, this same comparison is
the desired global pseudo-regret. That producer is still required.

For the expected bound, multiply the deterministic bound by the actual q(d)
and sum. Its total mass is one. At each t, stateLaw_distinct and
stateLaw_within discharge the state conditions on p_t's support; off-support
states contribute zero. Sum over states and time, and use the previously
compiled expected_unfixed_occupation_le <= 4 n^2 to get 8 n^2. No independent
geometric waiting times, stopping-time interchange or externally supplied
regret bound is assumed. All expectations and horizons here are finite.

## Dependencies and exact scope

Actual shared dependencies: action, CollisionFree, DistinctFixed, FixedWithin,
stateLaw, jointDraw, stateLaw_distinct, stateLaw_within, jointDraw_mem,
unfixedCount and expected_unfixed_occupation_le. Mathlib supplies finite
injection/cardinality and sum algebra, PMF normalization/support and exact
ENNReal-toReal identities. This adds no library, toolchain or axiom.

The source discusses coordination after successful exploration. This theorem
accepts a common S directly and starts from the existing all-unfixed initial
state. It does not construct an exploration history or prove conditioning on
its good event; no full path-space law or realized reward expectation is
claimed. Unknown population estimation, rank concentration, continuous reward
law construction and the delta*n*T bad-event term remain open. The coefficient
8 follows the already reviewed conservative numerical 1/(4n) hazard; it is an
explicit bounded coordination route, not the full source Theorem1.

## Concrete examples and status

The included two-player, three-arm example has means (3/4,1/2,1/4), S={0,1},
one player fixed on arm0 and one unfixed. Both choosing arm0 yields actual
pseudo-regret 5/4 with U=1. The unfixed player choosing arm1 yields zero regret.
The oneFixed state is an invariant-compatible diagnostic state, not a state
reachable from the two-player all-unfixed common-{0,1} process: there, each
round either both collide or both fix. The fourth canary instead starts from
the actual all-unfixed state law and verifies its arbitrary finite-horizon
expected bound <=32. These are component examples; they do not run exploration or
estimate n. Scratch-only focused compilation is separate from semantic review
and shared public-root/harness/site integration. No topic is complete.

## Exact scratch Lean

<details><summary>Definitions, proof and four canaries</summary>

```lean
import BanditRLProof.Algorithms.MusicalChairsCoordinationTime

namespace BanditRLProof.MusicalChairs
open scoped Classical ENNReal
set_option autoImplicit false

noncomputable def fixedPlayers {n k : ℕ} (s : State n k) : Finset (Fin n) :=
  Finset.univ.filter (fun i => s i ≠ none)

noncomputable def hitFixed {n k : ℕ} (s : State n k) (draw : Fin n → Fin k) :
    Finset (Fin n) := (fixedPlayers s).filter (fun i => ¬ CollisionFree (action s draw) i)

noncomputable def safeFixed {n k : ℕ} (s : State n k) (draw : Fin n → Fin k) :
    Finset (Fin n) := (fixedPlayers s) \ (hitFixed s draw)

theorem fixed_action_injective {n k : ℕ} (s : State n k) (draw : Fin n → Fin k)
    (hs : DistinctFixed s) : Set.InjOn (action s draw) (fixedPlayers s) := by
  intro i hi j hj heq
  have hi' : s i ≠ none := (Finset.mem_filter.mp hi).2
  have hj' : s j ≠ none := (Finset.mem_filter.mp hj).2
  cases hsi : s i with
  | none => exact False.elim (hi' hsi)
  | some a =>
    cases hsj : s j with
    | none => exact False.elim (hj' hsj)
    | some b =>
      have hab : a = b := by simpa [action, hsi, hsj] using heq
      exact hs i j a hsi (hsj.trans (congrArg some hab.symm))

theorem hitFixed_partner {n k : ℕ} (s : State n k) (draw : Fin n → Fin k)
    (hs : DistinctFixed s) (i : Fin n) (hi : i ∈ hitFixed s draw) :
    ∃ j, s j = none ∧ action s draw j = action s draw i := by
  obtain ⟨hif, hic⟩ := Finset.mem_filter.mp hi
  obtain ⟨j, hji, haj⟩ : ∃ j, j ≠ i ∧ action s draw j = action s draw i := by
    simpa [CollisionFree] using hic
  refine ⟨j, ?_, haj⟩
  by_contra hj
  have hjf : j ∈ fixedPlayers s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
  exact hji (fixed_action_injective s draw hs hjf hif haj)

theorem hitFixed_card_le {n k : ℕ} (s : State n k) (draw : Fin n → Fin k)
    (hs : DistinctFixed s) : (hitFixed s draw).card ≤ unfixedCount s := by
  let f : Fin n → Fin n := fun i => if h : i ∈ hitFixed s draw then
    (hitFixed_partner s draw hs i h).choose else i
  apply Finset.card_le_card_of_injOn f
  · intro i hi
    change i ∈ hitFixed s draw at hi
    change f i ∈ Finset.univ.filter (fun i => s i = none)
    have hf := (hitFixed_partner s draw hs i hi).choose_spec
    simp only [f, dif_pos hi, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hf.1
  · intro i hi j hj hij
    change i ∈ hitFixed s draw at hi
    change j ∈ hitFixed s draw at hj
    have hfi := (hitFixed_partner s draw hs i hi).choose_spec.2
    have hfj := (hitFixed_partner s draw hs j hj).choose_spec.2
    have heq : action s draw i = action s draw j := by
      rw [← hfi, ← hfj]
      congr 1
      simpa only [f, dif_pos hi, dif_pos hj] using hij
    exact fixed_action_injective s draw hs
      (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hj).1 heq

theorem safeFixed_count {n k : ℕ} (s : State n k) (draw : Fin n → Fin k)
    (hs : DistinctFixed s) : n ≤ (safeFixed s draw).card + 2 * unfixedCount s := by
  have hpartition : (fixedPlayers s).card + unfixedCount s = n := by
    simpa [fixedPlayers, unfixedCount] using
      Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
        (fun i => s i ≠ none)
  have hhit : hitFixed s draw ⊆ fixedPlayers s := Finset.filter_subset _ _
  have hsplit := Finset.card_sdiff_add_card_eq_card hhit
  have hle := hitFixed_card_le s draw hs
  change (safeFixed s draw).card + (hitFixed s draw).card = (fixedPlayers s).card at hsplit
  omega


noncomputable def roundMeanReward {n k : ℕ} (mu : Fin k → ℝ)
    (s : State n k) (draw : Fin n → Fin k) : ℝ :=
  ∑ i : Fin n, if CollisionFree (action s draw) i then mu (action s draw i) else 0

noncomputable def roundPseudoRegret {n k : ℕ} (S : Finset (Fin k)) (mu : Fin k → ℝ)
    (s : State n k) (draw : Fin n → Fin k) : ℝ :=
  (∑ a ∈ S, mu a) - roundMeanReward mu s draw

theorem safeFixed_mem {n k : ℕ} (s : State n k) (draw : Fin n → Fin k)
    (i : Fin n) (hi : i ∈ safeFixed s draw) :
    i ∈ fixedPlayers s ∧ CollisionFree (action s draw) i := by
  have h := Finset.mem_sdiff.mp hi
  refine ⟨h.1, ?_⟩
  by_contra hc
  exact h.2 (Finset.mem_filter.mpr ⟨h.1, hc⟩)

theorem safeFixed_arms_subset {n k : ℕ} (S : Finset (Fin k)) (s : State n k)
    (draw : Fin n → Fin k) (hw : FixedWithin (fun _ => S) s) :
    (safeFixed s draw).image (action s draw) ⊆ S := by
  intro a ha
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
  have hif := (safeFixed_mem s draw i hi).1
  have hn : s i ≠ none := (Finset.mem_filter.mp hif).2
  cases hsi : s i with
  | none => exact False.elim (hn hsi)
  | some a => simpa [action, hsi] using hw i a hsi

theorem safeFixed_reward_le {n k : ℕ} (mu : Fin k → ℝ)
    (hmu : ∀ a, 0 ≤ mu a) (s : State n k) (draw : Fin n → Fin k)
    (hs : DistinctFixed s) :
    ∑ a ∈ (safeFixed s draw).image (action s draw), mu a ≤ roundMeanReward mu s draw := by
  rw [Finset.sum_image]
  · calc
      _ = ∑ i ∈ safeFixed s draw,
          if CollisionFree (action s draw) i then mu (action s draw i) else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [if_pos (safeFixed_mem s draw i hi).2]
      _ ≤ roundMeanReward mu s draw := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        intro i _ _
        split_ifs
        · exact hmu _
        · exact le_rfl
  · intro i hi j hj heq
    exact fixed_action_injective s draw hs (safeFixed_mem s draw i hi).1
      (safeFixed_mem s draw j hj).1 heq

theorem roundPseudoRegret_le_twice_unfixed {n k : ℕ} (S : Finset (Fin k))
    (hcard : S.card = n) (mu : Fin k → ℝ) (hmu : ∀ a, 0 ≤ mu a ∧ mu a ≤ 1)
    (s : State n k) (draw : Fin n → Fin k) (hs : DistinctFixed s)
    (hw : FixedWithin (fun _ => S) s) :
    roundPseudoRegret S mu s draw ≤ 2 * (unfixedCount s : ℝ) := by
  let A := (safeFixed s draw).image (action s draw)
  have hsub : A ⊆ S := safeFixed_arms_subset S s draw hw
  have hA : A.card = (safeFixed s draw).card := by
    apply Finset.card_image_iff.mpr
    intro i hi j hj heq
    exact fixed_action_injective s draw hs (safeFixed_mem s draw i hi).1
      (safeFixed_mem s draw j hj).1 heq
  have hmissing : (S \ A).card ≤ 2 * unfixedCount s := by
    have hp := Finset.card_sdiff_add_card_eq_card hsub
    have hc := safeFixed_count s draw hs
    omega
  have hsum : (∑ a ∈ S \ A, mu a) ≤ ((S \ A).card : ℝ) := by
    simpa using (S \ A).sum_le_card_nsmul mu (1 : ℝ) (fun a _ => (hmu a).2)
  have hreward := safeFixed_reward_le mu (fun a => (hmu a).1) s draw hs
  have hpartition := Finset.sum_sdiff hsub (f := mu)
  have hcast : ((S \ A).card : ℝ) ≤ 2 * (unfixedCount s : ℝ) := by exact_mod_cast hmissing
  change (∑ a ∈ S, mu a) - roundMeanReward mu s draw ≤ _
  change (∑ a ∈ A, mu a) ≤ _ at hreward
  linarith


theorem roundPseudoRegret_nonneg {n k : ℕ} (S : Finset (Fin k))
    (mu : Fin k → ℝ) (hmu : ∀ a, 0 ≤ mu a) (s : State n k)
    (draw : Fin n → Fin k) (hw : FixedWithin (fun _ => S) s)
    (hd : ∀ i, draw i ∈ S) : 0 ≤ roundPseudoRegret S mu s draw := by
  let J := Finset.univ.filter (fun i => CollisionFree (action s draw) i)
  have hinj : Set.InjOn (action s draw) J := by
    intro i hi j hj heq
    by_contra hij
    exact (Finset.mem_filter.mp hi).2 j (Ne.symm hij) heq.symm
  have hsub : J.image (action s draw) ⊆ S := by
    intro a ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    cases hsi : s i with
    | none => simpa [action, hsi] using hd i
    | some a => simpa [action, hsi] using hw i a hsi
  have hrew : roundMeanReward mu s draw = ∑ a ∈ J.image (action s draw), mu a := by
    rw [Finset.sum_image hinj]
    simp [J, Finset.sum_filter, roundMeanReward]
  unfold roundPseudoRegret
  rw [sub_nonneg, hrew]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun a _ _ => hmu a)

theorem expected_round_charge {n k : ℕ} (S : Finset (Fin k)) (hne : S.Nonempty)
    (hcard : S.card = n) (mu : Fin k → ℝ) (hmu : ∀ a, 0 ≤ mu a ∧ mu a ≤ 1)
    (s : State n k) (hs : DistinctFixed s) (hw : FixedWithin (fun _ => S) s) :
    ∑ draw, (jointDraw (fun _ : Fin n => S) (fun _ => hne)) draw *
      ENNReal.ofReal (roundPseudoRegret S mu s draw) ≤ 2 * (unfixedCount s : ℝ≥0∞) := by
  let q := jointDraw (fun _ : Fin n => S) (fun _ => hne)
  have hq : ∑ draw, q draw = 1 := by simpa [tsum_fintype] using q.tsum_coe
  calc
    _ ≤ ∑ draw, q draw * (2 * (unfixedCount s : ℝ≥0∞)) := by
      apply Finset.sum_le_sum
      intro draw _
      apply mul_le_mul_right
      have h := ENNReal.ofReal_le_ofReal (roundPseudoRegret_le_twice_unfixed
        S hcard mu hmu s draw hs hw)
      simpa using h
    _ = _ := by rw [← Finset.sum_mul, hq, one_mul]

noncomputable def expectedCoordinationRegret {n k : ℕ} (S : Finset (Fin k))
    (hne : S.Nonempty) (mu : Fin k → ℝ) (T : ℕ) : ℝ≥0∞ :=
  ∑ t ∈ Finset.range T, ∑ s, (stateLaw (fun _ : Fin n => S) (fun _ => hne) t) s *
    ∑ draw, (jointDraw (fun _ : Fin n => S) (fun _ => hne)) draw *
      ENNReal.ofReal (roundPseudoRegret S mu s draw)

theorem expectedCoordinationRegret_le {n k : ℕ} (S : Finset (Fin k))
    (hne : S.Nonempty) (hcard : S.card = n) (mu : Fin k → ℝ)
    (hmu : ∀ a, 0 ≤ mu a ∧ mu a ≤ 1) (T : ℕ) :
    expectedCoordinationRegret (n := n) S hne mu T ≤ 8 * (n : ℝ≥0∞)^2 := by
  calc
    _ ≤ ∑ t ∈ Finset.range T, ∑ s,
        (stateLaw (fun _ : Fin n => S) (fun _ => hne) t) s *
          (2 * (unfixedCount s : ℝ≥0∞)) := by
      apply Finset.sum_le_sum
      intro t _
      apply Finset.sum_le_sum
      intro s _
      by_cases hp : s ∈ (stateLaw (fun _ : Fin n => S) (fun _ => hne) t).support
      · exact mul_le_mul_right (expected_round_charge S hne hcard mu hmu s
          (stateLaw_distinct _ _ t s hp) (stateLaw_within _ _ t s hp)) _
      · have hz : (stateLaw (fun _ : Fin n => S) (fun _ => hne) t) s = 0 := by
          simpa [PMF.mem_support_iff] using hp
        simp [hz]
    _ = 2 * (∑ t ∈ Finset.range T, ∑ s,
        (stateLaw (fun _ : Fin n => S) (fun _ => hne) t) s *
          (unfixedCount s : ℝ≥0∞)) := by
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      apply Finset.sum_congr rfl
      intro s _
      ring
    _ ≤ 2 * (4 * (n : ℝ≥0∞)^2) :=
      mul_le_mul_right (expected_unfixed_occupation_le S hne hcard T) _
    _ = _ := by ring


theorem expectedCoordinationRegret_toReal {n k : ℕ} (S : Finset (Fin k))
    (hne : S.Nonempty) (mu : Fin k → ℝ) (hmu : ∀ a, 0 ≤ mu a) (T : ℕ) :
    (expectedCoordinationRegret (n := n) S hne mu T).toReal =
      ∑ t ∈ Finset.range T, ∑ s,
        ((stateLaw (fun _ : Fin n => S) (fun _ => hne) t) s).toReal *
        ∑ draw, ((jointDraw (fun _ : Fin n => S) (fun _ => hne)) draw).toReal *
          roundPseudoRegret S mu s draw := by
  unfold expectedCoordinationRegret
  rw [ENNReal.toReal_sum (by simp [ENNReal.mul_ne_top, PMF.apply_ne_top])]
  apply Finset.sum_congr rfl
  intro t _
  rw [ENNReal.toReal_sum (by simp [ENNReal.mul_ne_top, PMF.apply_ne_top])]
  apply Finset.sum_congr rfl
  intro s _
  rw [ENNReal.toReal_mul]
  by_cases hp : s ∈ (stateLaw (fun _ : Fin n => S) (fun _ => hne) t).support
  · rw [ENNReal.toReal_sum (by simp [ENNReal.mul_ne_top, PMF.apply_ne_top])]
    congr 1
    apply Finset.sum_congr rfl
    intro draw _
    rw [ENNReal.toReal_mul]
    by_cases hq : draw ∈ (jointDraw (fun _ : Fin n => S) (fun _ => hne)).support
    · rw [ENNReal.toReal_ofReal (roundPseudoRegret_nonneg S mu hmu s draw
        (stateLaw_within _ _ t s hp) (jointDraw_mem _ _ draw hq))]
    · have hz : (jointDraw (fun _ : Fin n => S) (fun _ => hne)) draw = 0 := by
        simpa [PMF.mem_support_iff] using hq
      simp [hz]
  · have hz : (stateLaw (fun _ : Fin n => S) (fun _ => hne) t) s = 0 := by
      simpa [PMF.mem_support_iff] using hp
    simp [hz]

theorem expectedCoordinationRegret_real_le {n k : ℕ} (S : Finset (Fin k))
    (hne : S.Nonempty) (hcard : S.card = n) (mu : Fin k → ℝ)
    (hmu : ∀ a, 0 ≤ mu a ∧ mu a ≤ 1) (T : ℕ) :
    (∑ t ∈ Finset.range T, ∑ s,
      ((stateLaw (fun _ : Fin n => S) (fun _ => hne) t) s).toReal *
      ∑ draw, ((jointDraw (fun _ : Fin n => S) (fun _ => hne)) draw).toReal *
        roundPseudoRegret S mu s draw) ≤ 8 * (n : ℝ)^2 := by
  rw [← expectedCoordinationRegret_toReal S hne mu (fun a => (hmu a).1) T]
  apply ENNReal.toReal_le_of_le_ofReal (by positivity)
  simpa using expectedCoordinationRegret_le S hne hcard mu hmu T


namespace RegretCanary

noncomputable def means (a : Fin 3) : ℝ := if a = 0 then 3/4 else if a = 1 then 1/2 else 1/4

def oneFixed : State 2 3 := fun i => if i = 0 then some 0 else none

theorem collision_positive_regret :
    roundPseudoRegret ({0, 1} : Finset (Fin 3)) means oneFixed (fun _ => 0) = 5/4 := by
  norm_num [roundPseudoRegret, roundMeanReward, means, oneFixed, action,
    CollisionFree, Fin.sum_univ_two, Fin.forall_fin_succ]

theorem collision_one_unfixed : unfixedCount oneFixed = 1 := by
  decide +kernel

theorem separated_zero_regret :
    roundPseudoRegret ({0, 1} : Finset (Fin 3)) means oneFixed
      (fun i => if i = 0 then 0 else 1) = 0 := by
  norm_num [roundPseudoRegret, roundMeanReward, means, oneFixed, action,
    CollisionFree, Fin.sum_univ_two, Fin.forall_fin_succ]

theorem two_player_expected (T : ℕ) :
    expectedCoordinationRegret (n := 2) ({0, 1} : Finset (Fin 3)) (by decide) means T ≤ 32 := by
  have h := expectedCoordinationRegret_le (n := 2) ({0, 1} : Finset (Fin 3))
    (by decide) (by decide) means (by intro a; fin_cases a <;> norm_num [means]) T
  norm_num at h ⊢
  exact h

end RegretCanary
end BanditRLProof.MusicalChairs
```

</details>
