import BanditRLProof.Algorithms.CUCBSourceModel
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.MetricSpace.Pseudo.Pi

/-! Source bounded smoothness produces score continuity and measurable oracle
events; no extra score-measurability assumption is added to the model. -/
namespace BanditRLProof.CUCB.SourceModel
open MeasureTheory
set_option autoImplicit false
variable {A : Type*} [Fintype A] [Nonempty A] [MeasurableSpace A] {m : ℕ}
variable {M : FeedbackModel A m} (S : SourceModel M)

theorem continuous_score (a : A) : Continuous (fun v => S.score v a) := by
  apply Metric.continuous_iff.mpr
  intro v ε hε
  obtain ⟨δ, hδ, hd⟩ := Metric.continuousWithinAt_iff.mp
    (S.modulus_continuous 0 (by simp)) ε hε
  refine ⟨δ, hδ, ?_⟩
  intro w hw
  have hf := hd (show dist w v∈Set.Ici (0:ℝ) from dist_nonneg)
    (show dist (dist w v) 0<δ by simpa using hw)
  have hs := S.score_smooth w v a (dist w v) dist_nonneg (fun i _ => by
    simpa only [Subtype.dist_eq, Real.dist_eq] using dist_le_pi_dist w v i)
  rw [S.modulus_zero, dist_zero_right] at hf
  rw [Real.dist_eq]
  exact hs.trans_lt ((le_abs_self _).trans_lt hf)

theorem continuous_optimum : Continuous (scoreOptimum S.score) := by
  exact Continuous.finset_sup'_apply Finset.univ_nonempty (fun a _ => S.continuous_score a)

variable [MeasurableSingletonClass A]

theorem measurable_joint_score : Measurable (fun p : Input m × A => S.score p.1 p.2) := by
  classical
  have he : (fun p : Input m × A => S.score p.1 p.2) =
      fun p => ∑a: A, if p.2=a then S.score p.1 a else 0 := by
    funext p
    simp
  rw [he]
  apply Finset.measurable_sum
  intro a ha
  exact ((S.continuous_score a).measurable.comp measurable_fst).ite
    (measurable_snd (measurableSet_singleton a)) measurable_const

def oracleSuccess : Set (Input m × A) :=
  {p | S.alpha*scoreOptimum S.score p.1≤S.score p.1 p.2}

theorem measurableSet_oracleSuccess : MeasurableSet S.oracleSuccess :=
  measurableSet_le ((S.continuous_optimum.measurable.comp measurable_fst).const_mul S.alpha)
    S.measurable_joint_score

theorem measurableSet_path_oracleSuccess (n : ℕ) : MeasurableSet
    {Y : ℕ → Round A m | (oracleInput (fun t => (Y t).2) n, (Y n).1)∈S.oracleSuccess} :=
  S.measurableSet_oracleSuccess.preimage
    (((measurable_oracleInput n).comp (by fun_prop)).prodMk (by fun_prop))

end BanditRLProof.CUCB.SourceModel
