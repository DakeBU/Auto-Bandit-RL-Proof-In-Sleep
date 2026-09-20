import BanditRLProof.Algorithms.MusicalChairsCoordinationTime
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Algebra.Order.Round
import Mathlib.Data.Finset.Sort
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import BanditRLProof.Algorithms.MusicalChairsCoordinationRegret
import BanditRLProof.Algorithms.MusicalChairsHandoff

open scoped Classical ENNReal
set_option autoImplicit false

namespace BanditRLProof.FinitePMF

theorem iid_sum_snoc {α : Type*} [Fintype α] (p : PMF α) (T : ℕ)
    (f : (Fin (T+1) → α) → ℝ≥0∞) :
    ∑ d, iid p (T+1) d * f d =
      ∑ x, iid p T x * ∑ a, p a * f (Fin.snoc x a) := by
  calc
    _ = ∑ z : α × (Fin T → α),
        iid p (T+1) (Fin.snoc z.2 z.1) * f (Fin.snoc z.2 z.1) := by
      exact (Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (T+1) => α))
        (fun z => iid p (T+1) (Fin.snoc z.2 z.1) * f (Fin.snoc z.2 z.1))
        (fun d => iid p (T+1) d * f d) (fun z => rfl)).symm
    _ = _ := by
      simp_rw [iid_apply, Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      simp_rw [Finset.mul_sum, mul_assoc]

theorem iid_snoc {α : Type*} [Fintype α] (p : PMF α) (T : ℕ) :
    iid p (T+1) = (iid p T).bind (fun x => p.map (Fin.snoc x)) := by
  classical
  ext d
  have h := iid_sum_snoc p T (fun x => if d = x then 1 else 0)
  simp [PMF.bind_apply, PMF.map_apply, tsum_fintype, mul_ite] at h ⊢
  refine h.trans (Finset.sum_congr rfl ?_)
  intro x _
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  by_cases he : d = Fin.snoc x a <;> simp [he]

end BanditRLProof.FinitePMF

namespace BanditRLProof.MusicalChairs

theorem trajectory_snoc_prefix {n k T : ℕ} (hk : 0 < k)
    (d : Fin T → Fin n → Fin k) (a : Fin n → Fin k) :
    trajectory (extendedCoordinationDraws hk (Fin.snoc d a)) T =
      trajectory (extendedCoordinationDraws hk d) T := by
  apply trajectory_eq_of_prefix
  intro u hu
  simp [extendedCoordinationDraws, hu, show u < T+1 by omega, Fin.snoc]

theorem trajectory_snoc_last {n k T : ℕ} (hk : 0 < k)
    (d : Fin T → Fin n → Fin k) (a : Fin n → Fin k) :
    trajectory (extendedCoordinationDraws hk (Fin.snoc d a)) (T+1) =
      step (trajectory (extendedCoordinationDraws hk d) T) a := by
  rw [trajectory, trajectory_snoc_prefix]
  congr 1
  simp only [extendedCoordinationDraws, dif_pos (Nat.lt_succ_self T)]
  change Fin.snoc (α := fun _ => Fin n → Fin k) d a (Fin.last T) = a
  simp

theorem iid_trajectory_stateLaw {n k : ℕ} (hk : 0 < k)
    (C : Fin n → Finset (Fin k)) (hne : ∀ i, (C i).Nonempty) (T : ℕ) :
    (FinitePMF.iid (jointDraw C hne) T).map
      (fun d => trajectory (extendedCoordinationDraws hk d) T) = stateLaw C hne T := by
  induction T with
  | zero =>
    simpa only [trajectory, stateLaw] using
      (PMF.map_const (FinitePMF.iid (jointDraw C hne) 0) (initial n k))
  | succ T ih =>
    rw [FinitePMF.iid_snoc, PMF.map_bind]
    simp_rw [PMF.map_comp, Function.comp_def, trajectory_snoc_last]
    rw [stateLaw, ← ih, PMF.bind_map]
    rfl

end BanditRLProof.MusicalChairs

namespace BanditRLProof.FinitePMF

theorem iid_take {α : Type*} [Fintype α] (p : PMF α) {T L : ℕ} (h : T ≤ L) :
    (iid p L).map (fun d t => d (Fin.castLE h t)) = iid p T := by
  induction L with
  | zero =>
    have hT : T = 0 := by omega
    subst T
    convert PMF.map_id (iid p 0) using 1
  | succ L ih =>
    by_cases heq : T = L+1
    · subst T
      convert PMF.map_id (iid p (L+1)) using 1
    · have hTL : T ≤ L := by omega
      rw [iid_snoc, PMF.map_bind]
      have he (d : Fin L → α) :
          (p.map (fun a : α => (Fin.snoc d a : Fin (L+1) → α))).map
            (fun (x : Fin (L+1) → α) (t : Fin T) => x (Fin.castLE h t)) =
            PMF.pure (fun t => d (Fin.castLE hTL t)) := by
        rw [PMF.map_comp]
        have hf : ((fun (x : Fin (L+1) → α) (t : Fin T) => x (Fin.castLE h t)) ∘
              (fun a : α => (Fin.snoc d a : Fin (L+1) → α))) =
            Function.const α (fun t => d (Fin.castLE hTL t)) := by
          funext a t
          have ht : Fin.castLE h t = (Fin.castLE hTL t).castSucc := by
            apply Fin.ext
            rfl
          simp only [Function.comp_apply, Function.const_apply, ht, Fin.snoc_castSucc]
        rw [hf, PMF.map_const]
      simp_rw [he]
      exact ih hTL

theorem sum_map {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α) (g : α → β) (f : β → ℝ≥0∞) :
    ∑ b, p.map g b * f b = ∑ a, p a * f (g a) := by
  simp only [PMF.map_apply, tsum_fintype, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp [ite_mul]

end BanditRLProof.FinitePMF

namespace BanditRLProof.MusicalChairs

theorem trajectory_take {n k T L : ℕ} (hk : 0 < k) (h : T ≤ L)
    (d : Fin L → Fin n → Fin k) :
    trajectory (extendedCoordinationDraws hk d) T =
      trajectory (extendedCoordinationDraws hk (fun t => d (Fin.castLE h t))) T := by
  apply trajectory_eq_of_prefix
  intro u hu
  simp [extendedCoordinationDraws, hu, show u < L from lt_of_lt_of_le hu h]

theorem iid_trajectory_marginal {n k T L : ℕ} (hk : 0 < k) (h : T ≤ L)
    (C : Fin n → Finset (Fin k)) (hne : ∀ i, (C i).Nonempty) :
    (FinitePMF.iid (jointDraw C hne) L).map
      (fun d => trajectory (extendedCoordinationDraws hk d) T) = stateLaw C hne T := by
  simp_rw [trajectory_take hk h]
  change (FinitePMF.iid (jointDraw C hne) L).map
    ((fun d => trajectory (extendedCoordinationDraws hk d) T) ∘
      (fun d t => d (Fin.castLE h t))) = _
  rw [← PMF.map_comp, FinitePMF.iid_take]
  exact iid_trajectory_stateLaw hk C hne T

theorem iid_last_state_draw {n k T : ℕ} (hk : 0 < k)
    (C : Fin n → Finset (Fin k)) (hne : ∀ i, (C i).Nonempty) :
    (FinitePMF.iid (jointDraw C hne) (T+1)).map
      (fun d => (trajectory (extendedCoordinationDraws hk d) T, d (Fin.last T))) =
    (stateLaw C hne T).bind (fun s => (jointDraw C hne).map (fun a => (s,a))) := by
  rw [FinitePMF.iid_snoc, PMF.map_bind]
  simp_rw [PMF.map_comp, Function.comp_def, trajectory_snoc_prefix, Fin.snoc_last]
  rw [← iid_trajectory_stateLaw hk C hne T, PMF.bind_map]
  rfl

theorem iid_round_state_draw {n k L : ℕ} (hk : 0 < k) (t : Fin L)
    (C : Fin n → Finset (Fin k)) (hne : ∀ i, (C i).Nonempty) :
    (FinitePMF.iid (jointDraw C hne) L).map
      (fun d => (trajectory (extendedCoordinationDraws hk d) t.val, d t)) =
    (stateLaw C hne t.val).bind (fun s => (jointDraw C hne).map (fun a => (s,a))) := by
  let h : t.val+1 ≤ L := t.isLt
  have hf : (fun d : Fin L → Fin n → Fin k =>
      (trajectory (extendedCoordinationDraws hk d) t.val, d t)) =
    ((fun d : Fin (t.val+1) → Fin n → Fin k =>
      (trajectory (extendedCoordinationDraws hk d) t.val, d (Fin.last t.val))) ∘
        (fun d u => d (Fin.castLE h u))) := by
    funext d
    apply Prod.ext
    · apply trajectory_eq_of_prefix
      intro u hu
      simp [extendedCoordinationDraws, show u < t.val+1 by omega,
        show u < L from lt_trans hu t.isLt]
    · rfl
  rw [hf, ← PMF.map_comp, FinitePMF.iid_take]
  exact iid_last_state_draw hk C hne

end BanditRLProof.MusicalChairs

namespace BanditRLProof.FinitePMF

theorem sum_map_real {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α) (g : α → β) (f : β → ℝ) :
    ∑ b, (p.map g b).toReal * f b = ∑ a, (p a).toReal * f (g a) := by
  have hb (b : β) : (p.map g b).toReal = ∑ a, if b = g a then (p a).toReal else 0 := by
    rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum]
    · apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> simp
    · intro a _
      split_ifs <;> simp [PMF.apply_ne_top]
  simp_rw [hb, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp [ite_mul]

theorem sum_bind_real {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α) (q : α → PMF β) (f : β → ℝ) :
    ∑ b, (p.bind q b).toReal * f b = ∑ a, (p a).toReal * ∑ b, (q a b).toReal * f b := by
  have hb (b : β) : (p.bind q b).toReal = ∑ a, (p a).toReal * (q a b).toReal := by
    rw [PMF.bind_apply, tsum_fintype, ENNReal.toReal_sum]
    · simp_rw [ENNReal.toReal_mul]
    · intro a _
      exact ENNReal.mul_ne_top (PMF.apply_ne_top p a) (PMF.apply_ne_top (q a) b)
  simp_rw [hb, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [Finset.mul_sum, mul_assoc]

end BanditRLProof.FinitePMF

namespace BanditRLProof.MusicalChairs

noncomputable def pathCoordinationRegret {n k L : ℕ} (hk : 0 < k)
    (S : Finset (Fin k)) (mu : Fin k → ℝ) (d : Fin L → Fin n → Fin k) : ℝ :=
  ∑ t : Fin L, roundPseudoRegret S mu
    (trajectory (extendedCoordinationDraws hk d) t.val) (d t)

theorem iid_round_regret_expectation {n k L : ℕ} (hk : 0 < k) (t : Fin L)
    (C : Fin n → Finset (Fin k)) (hne : ∀ i, (C i).Nonempty)
    (S : Finset (Fin k)) (mu : Fin k → ℝ) :
    (∑ d, (FinitePMF.iid (jointDraw C hne) L d).toReal *
      roundPseudoRegret S mu (trajectory (extendedCoordinationDraws hk d) t.val) (d t)) =
    ∑ s, (stateLaw C hne t.val s).toReal *
      ∑ a, (jointDraw C hne a).toReal * roundPseudoRegret S mu s a := by
  rw [← FinitePMF.sum_map_real (FinitePMF.iid (jointDraw C hne) L)
    (fun d => (trajectory (extendedCoordinationDraws hk d) t.val,d t))
    (fun z => roundPseudoRegret S mu z.1 z.2), iid_round_state_draw,
    FinitePMF.sum_bind_real]
  simp_rw [FinitePMF.sum_map_real]

theorem iid_path_regret_expectation {n k L : ℕ} (hk : 0 < k)
    (S : Finset (Fin k)) (hne : S.Nonempty) (mu : Fin k → ℝ) :
    (∑ d, (FinitePMF.iid (jointDraw (fun _ : Fin n => S) (fun _ => hne)) L d).toReal *
      pathCoordinationRegret hk S mu d) =
    ∑ t ∈ Finset.range L, ∑ s,
      (stateLaw (fun _ : Fin n => S) (fun _ => hne) t s).toReal *
        ∑ a, (jointDraw (fun _ : Fin n => S) (fun _ => hne) a).toReal *
          roundPseudoRegret S mu s a := by
  simp only [pathCoordinationRegret, Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_range]
  apply Finset.sum_congr rfl
  intro t _
  simpa only [Finset.mul_sum] using iid_round_regret_expectation hk t
    (fun _ : Fin n => S) (fun _ => hne) S mu

theorem iid_path_regret_le {n k L : ℕ} (hk : 0 < k)
    (S : Finset (Fin k)) (hne : S.Nonempty) (hcard : S.card = n)
    (mu : Fin k → ℝ) (hmu : ∀ a, 0 ≤ mu a ∧ mu a ≤ 1) :
    (∑ d, (FinitePMF.iid (jointDraw (fun _ : Fin n => S) (fun _ => hne)) L d).toReal *
      pathCoordinationRegret hk S mu d) ≤ 8 * (n : ℝ)^2 := by
  rw [iid_path_regret_expectation]
  exact expectedCoordinationRegret_real_le S hne hcard mu hmu L

end BanditRLProof.MusicalChairs

namespace BanditRLProof.MusicalChairs
open MeasureTheory ProbabilityTheory

instance coordinationState_measurableSpace (n k : ℕ) : MeasurableSpace (State n k) := ⊤

instance coordinationState_measurableSingleton (n k : ℕ) : MeasurableSingletonClass (State n k) := by
  constructor
  intro s
  trivial

theorem learnedDrawPathKernel_state_marginal {n k T L t : ℕ} (hk : 1 < k) (ht : t ≤ L)
    (z : (Fin T → Fin n → Fin k) × (Fin T → Fin k → ℝ)) :
    (learnedDrawPathKernel hk L z).map
      (fun d => trajectory (extendedCoordinationDraws (by omega) d) t) =
    (stateLaw (learnedConfig hk z).val (learnedConfig hk z).property t).toMeasure := by
  rw [learnedDrawPathKernel_apply, PMF.toMeasure_map _ _ (measurable_of_countable _),
    iid_trajectory_marginal _ ht]

theorem learnedDrawPathKernel_round_marginal {n k T L : ℕ} (hk : 1 < k) (t : Fin L)
    (z : (Fin T → Fin n → Fin k) × (Fin T → Fin k → ℝ)) :
    (learnedDrawPathKernel hk L z).map
      (fun d => (trajectory (extendedCoordinationDraws (by omega) d) t.val, d t)) =
    ((stateLaw (learnedConfig hk z).val (learnedConfig hk z).property t.val).bind
      (fun s => (jointDraw (learnedConfig hk z).val (learnedConfig hk z).property).map
        (fun a => (s,a)))).toMeasure := by
  rw [learnedDrawPathKernel_apply, PMF.toMeasure_map _ _ (measurable_of_countable _),
    iid_round_state_draw]

theorem explorationContinuationLaw_restricted_path {n k T L : ℕ} (hk : 1 < k)
    (nu : Fin k → Measure ℝ) [∀ a, IsProbabilityMeasure (nu a)]
    (S : Finset (Fin k)) (hne : S.Nonempty)
    (E : Set ((Fin T → Fin n → Fin k) × (Fin T → Fin k → ℝ))) (hE : MeasurableSet E)
    (hEG : E ⊆ explorationGoodEvent (n := n) S) :
    ((explorationContinuationLaw hk nu L).restrict (Prod.fst ⁻¹' E)).map Prod.snd =
      explorationRewardLaw (by omega) nu E •
        (FinitePMF.iid (jointDraw (fun _ : Fin n => S) (fun _ => hne)) L).toMeasure := by
  ext B hB
  rw [Measure.map_apply measurable_snd hB,
    Measure.restrict_apply (measurable_snd hB)]
  have he : (Prod.snd ⁻¹' B) ∩ (Prod.fst ⁻¹' E) = E ×ˢ B := by
    ext x
    simp [and_comm]
  rw [he, explorationContinuationLaw_rectangle_on_good hk nu S hne E hE hEG]
  simp [Measure.smul_apply, smul_eq_mul]

theorem explorationContinuationLaw_good_regret_integral {n k T L : ℕ} (hk : 1 < k)
    (nu : Fin k → Measure ℝ) [∀ a, IsProbabilityMeasure (nu a)]
    (S : Finset (Fin k)) (hne : S.Nonempty) (mu : Fin k → ℝ)
    (E : Set ((Fin T → Fin n → Fin k) × (Fin T → Fin k → ℝ))) (hE : MeasurableSet E)
    (hEG : E ⊆ explorationGoodEvent (n := n) S) :
    (∫ z in Prod.fst ⁻¹' E, pathCoordinationRegret (by omega) S mu z.2
      ∂explorationContinuationLaw hk nu L) =
    (explorationRewardLaw (by omega) nu E).toReal *
      ∑ d, (FinitePMF.iid (jointDraw (fun _ : Fin n => S) (fun _ => hne)) L d).toReal *
        pathCoordinationRegret (by omega) S mu d := by
  rw [← integral_map measurable_snd.aemeasurable
    (measurable_of_countable (pathCoordinationRegret (by omega) S mu)).aestronglyMeasurable,
    explorationContinuationLaw_restricted_path hk nu S hne E hE hEG,
    integral_smul_measure, PMF.integral_eq_sum]
  rfl

theorem explorationContinuationLaw_conditional_coordination_regret {n k T L : ℕ} (hk : 1 < k)
    (nu : Fin k → Measure ℝ) [∀ a, IsProbabilityMeasure (nu a)]
    (S : Finset (Fin k)) (hne : S.Nonempty) (hcard : S.card = n)
    (mu : Fin k → ℝ) (hmu : ∀ a, 0 ≤ mu a ∧ mu a ≤ 1)
    (E : Set ((Fin T → Fin n → Fin k) × (Fin T → Fin k → ℝ))) (hE : MeasurableSet E)
    (hEG : E ⊆ explorationGoodEvent (n := n) S)
    (hpos : 0 < explorationRewardLaw (by omega) nu E) :
    (∫ z in Prod.fst ⁻¹' E, pathCoordinationRegret (by omega) S mu z.2
      ∂explorationContinuationLaw hk nu L) /
      (explorationContinuationLaw hk nu L (Prod.fst ⁻¹' E)).toReal ≤ 8 * (n : ℝ)^2 := by
  rw [explorationContinuationLaw_good_regret_integral hk nu S hne mu E hE hEG,
    explorationContinuationLaw_fst_event hk nu E hE]
  have hp : (explorationRewardLaw (by omega) nu E).toReal ≠ 0 :=
    ne_of_gt (ENNReal.toReal_pos (ne_of_gt hpos) (measure_ne_top _ _))
  rw [mul_comm, mul_div_cancel_right₀ _ hp]
  exact iid_path_regret_le (by omega) S hne hcard mu hmu

end BanditRLProof.MusicalChairs

namespace BanditRLProof.MusicalChairs
open MeasureTheory ProbabilityTheory


end BanditRLProof.MusicalChairs


namespace BanditRLProof.MusicalChairs
open MeasureTheory ProbabilityTheory

theorem iid_continuationAction_marginal {n k L : ℕ} (hk : 0 < k) (t : Fin L)
    (C : Fin n → Finset (Fin k)) (hne : ∀ i, (C i).Nonempty) :
    (FinitePMF.iid (jointDraw C hne) L).map (fun d => continuationAction hk d t) =
      (stateLaw C hne t.val).bind (fun s => (jointDraw C hne).map (action s)) := by
  change (FinitePMF.iid (jointDraw C hne) L).map
    ((fun z : State n k × (Fin n → Fin k) => action z.1 z.2) ∘
      (fun d => (trajectory (extendedCoordinationDraws hk d) t.val, d t))) = _
  rw [← PMF.map_comp, iid_round_state_draw, PMF.map_bind]
  simp_rw [PMF.map_comp]
  rfl

theorem source_conditional_coordination_regret {n k L : ℕ} (hn : 0 < n) (hnk : n < k)
    (nu : Fin k → Measure ℝ) [∀ a, IsProbabilityMeasure (nu a)]
    (hb : ∀ a, ∀ᵐ y ∂nu a, y ∈ Set.Icc (0 : ℝ) 1)
    (eps delta : ℝ) (heps : 0 < eps)
    (hepsgap : eps < boundaryGap (armMean nu) n hn hnk)
    (hdelta : 0 < delta) (hdelta1 : delta < 1) :
    (∫ z in Prod.fst ⁻¹' (explorationGoodEvent (n := n)
      (T := explorationLength k eps delta) (trueTopArms nu n)),
      pathCoordinationRegret (by omega) (trueTopArms nu n) (armMean nu) z.2
        ∂explorationContinuationLaw (by omega) nu L) /
      (explorationContinuationLaw (by omega) nu L
        (Prod.fst ⁻¹' (explorationGoodEvent (n := n)
          (T := explorationLength k eps delta) (trueTopArms nu n)))).toReal ≤ 8 * (n : ℝ)^2 := by
  have hc : (trueTopArms nu n).card = n := by
    simp [trueTopArms, topArms_card, min_eq_left hnk.le]
  have hne : (trueTopArms nu n).Nonempty := Finset.card_pos.mp (by omega)
  exact explorationContinuationLaw_conditional_coordination_regret (by omega) nu
    (trueTopArms nu n) hne hc (armMean nu) (fun a => armMean_mem_unitInterval nu hb a)
    _ (measurableSet_explorationGoodEvent _ hc) (Set.Subset.refl _)
    (explorationGoodEvent_positive hn hnk nu hb eps delta heps hepsgap hdelta hdelta1)

end BanditRLProof.MusicalChairs
