import BanditRLProof.Algorithms.MOSSCanonicalHistory
import BanditRLProof.Algorithms.UCBArmStreamConditionalReward

noncomputable section
open MeasureTheory ProbabilityTheory
namespace BanditRLProof.MOSS

def canonicalCondition {k : ℕ} (hk : 0 < k) (n : ℕ) (mean : Fin k → ℝ) (t : ℕ)
    (table : UCB.ArmRewardStream k) :=
  (canonicalHistory hk n mean table t, historyAction hk n t (canonicalHistory hk n mean table t))

def canonicalNextCoordinate {k : ℕ} (hk : 0 < k) (n : ℕ) (mean : Fin k → ℝ) (t : ℕ)
    (table : UCB.ArmRewardStream k) : ℕ × Fin k :=
  let c := canonicalCondition hk n mean t table
  (ETC.realHistoryPullCount t c.1 c.2 + 1, c.2)

theorem canonicalNextCoordinate_count {k : ℕ} (hk : 0 < k) (n : ℕ) (mean : Fin k → ℝ)
    (t : ℕ) (table : UCB.ArmRewardStream k) :
    (canonicalNextCoordinate hk n mean t table).1 =
      pullCount (canonicalAction hk n mean table) (canonicalNextCoordinate hk n mean t table).2 (t+1)+1 :=
  congrArg (fun m => m+1) (canonicalHistory_pullCount hk n mean table t _)

theorem canonicalHistory_eq_of_complement_eq {k : ℕ} (hk : 0 < k) (n : ℕ)
    (mean : Fin k → ℝ) (t : ℕ) (target : ℕ × Fin k) (table table' : UCB.ArmRewardStream k)
    (hc : UCB.armStreamWithoutCoordinate target table = UCB.armStreamWithoutCoordinate target table')
    (hf : pullCount (canonicalAction hk n mean table) target.2 (t+1) < target.1) :
    canonicalHistory hk n mean table t = canonicalHistory hk n mean table' t := by
  apply canonicalHistory_eq_of_eq_consumed
  intro a j hj
  have hne : (j+1,a) ≠ target := by
    intro he
    have ha : a = target.2 := congrArg Prod.snd he
    have hi : j+1 = target.1 := congrArg Prod.fst he
    subst a
    omega
  have h := congrFun hc ⟨(j+1,a), hne⟩
  exact h

theorem canonicalNextCoordinate_eq_iff_insert {k : ℕ} (hk : 0 < k) (n : ℕ)
    (mean : Fin k → ℝ) (t : ℕ) (target : ℕ × Fin k) (v : ℝ) (table : UCB.ArmRewardStream k) :
    canonicalNextCoordinate hk n mean t table = target ↔
      canonicalNextCoordinate hk n mean t
        (UCB.armStreamInsertCoordinate target v (UCB.armStreamWithoutCoordinate target table)) = target := by
  let rebuilt := UCB.armStreamInsertCoordinate target v (UCB.armStreamWithoutCoordinate target table)
  have hc : UCB.armStreamWithoutCoordinate target table = UCB.armStreamWithoutCoordinate target rebuilt := by
    simp [rebuilt]
  constructor
  · intro hnext
    have hn := canonicalNextCoordinate_count hk n mean t table
    rw [hnext] at hn
    have hh := canonicalHistory_eq_of_complement_eq hk n mean t target table rebuilt hc (by omega)
    have heq : canonicalNextCoordinate hk n mean t table = canonicalNextCoordinate hk n mean t rebuilt :=
      congrArg (fun h => (ETC.realHistoryPullCount t h (historyAction hk n t h)+1, historyAction hk n t h)) hh
    exact heq.symm.trans hnext
  · intro hnext
    have hn := canonicalNextCoordinate_count hk n mean t rebuilt
    rw [hnext] at hn
    have hh := canonicalHistory_eq_of_complement_eq hk n mean t target rebuilt table hc.symm (by omega)
    have heq : canonicalNextCoordinate hk n mean t rebuilt = canonicalNextCoordinate hk n mean t table :=
      congrArg (fun h => (ETC.realHistoryPullCount t h (historyAction hk n t h)+1, historyAction hk n t h)) hh
    exact heq.symm.trans hnext

def canonicalConditionWithout {k : ℕ} (hk : 0 < k) (n : ℕ) (mean : Fin k → ℝ) (t : ℕ)
    (target : ℕ × Fin k) (v : ℝ) :=
  canonicalCondition hk n mean t ∘ UCB.armStreamInsertCoordinate target v

theorem canonicalCondition_eq_without {k : ℕ} (hk : 0 < k) (n : ℕ)
    (mean : Fin k → ℝ) (t : ℕ) (target : ℕ × Fin k) (v : ℝ) (table : UCB.ArmRewardStream k)
    (hnext : canonicalNextCoordinate hk n mean t table = target) :
    canonicalCondition hk n mean t table =
      canonicalConditionWithout hk n mean t target v (UCB.armStreamWithoutCoordinate target table) := by
  have hn := canonicalNextCoordinate_count hk n mean t table
  rw [hnext] at hn
  have hh := canonicalHistory_eq_of_complement_eq hk n mean t target table
    (UCB.armStreamInsertCoordinate target v (UCB.armStreamWithoutCoordinate target table))
    (by simp) (by omega)
  exact congrArg (fun h => (h, historyAction hk n t h)) hh

theorem measurable_canonicalCondition {k : ℕ} (hk : 0 < k) (n : ℕ)
    (mean : Fin k → ℝ) (t : ℕ) : Measurable (canonicalCondition hk n mean t) :=
  (measurable_canonicalHistory hk n mean t).prodMk
    ((measurable_historyAction hk n t).comp (measurable_canonicalHistory hk n mean t))

theorem measurable_canonicalConditionWithout {k : ℕ} (hk : 0 < k) (n : ℕ)
    (mean : Fin k → ℝ) (t : ℕ) (target : ℕ × Fin k) (v : ℝ) :
    Measurable (canonicalConditionWithout hk n mean t target v) :=
  (measurable_canonicalCondition hk n mean t).comp (UCB.measurable_armStreamInsertCoordinate target v)

/-- A target reward is independent of the condition reconstructed without it. -/
theorem indepFun_coordinate_canonicalConditionWithout {k : ℕ} (hk : 0 < k) (n : ℕ)
    (mean : Fin k → ℝ) (t : ℕ) (ν : Kernel (Fin k) ℝ) [IsMarkovKernel ν]
    (target : ℕ × Fin k) (v : ℝ) :
    IndepFun (UCB.armStreamCoordinate target)
      (fun table => canonicalConditionWithout hk n mean t target v
        (UCB.armStreamWithoutCoordinate target table)) (UCB.armStreamMeasure ν) := by
  have hi := (UCB.indepFun_armStreamMeasure_coordinate_without ν target).comp measurable_id
    (measurable_canonicalConditionWithout hk n mean t target v)
  exact hi

theorem map_canonicalConditionWithout_coordinate {k : ℕ} (hk : 0 < k) (n : ℕ)
    (mean : Fin k → ℝ) (t : ℕ) (ν : Kernel (Fin k) ℝ) [IsMarkovKernel ν]
    (target : ℕ × Fin k) (v : ℝ) :
    Measure.map (fun table =>
      (canonicalConditionWithout hk n mean t target v (UCB.armStreamWithoutCoordinate target table),
        UCB.armStreamCoordinate target table)) (UCB.armStreamMeasure ν) =
      (Measure.map (fun table => canonicalConditionWithout hk n mean t target v
        (UCB.armStreamWithoutCoordinate target table)) (UCB.armStreamMeasure ν)).prod (ν target.2) := by
  have hc := (measurable_canonicalConditionWithout hk n mean t target v).comp
    (UCB.measurable_armStreamWithoutCoordinate target)
  have hj := (indepFun_iff_map_prod_eq_prod_map_map hc.aemeasurable
    (UCB.measurable_armStreamCoordinate target).aemeasurable).mp
    (indepFun_coordinate_canonicalConditionWithout hk n mean t ν target v).symm
  simp only [Function.comp_def] at hj
  rw [hj]
  congr 1
  exact UCB.armStreamMeasure_map_coord ν target.1 target.2

end BanditRLProof.MOSS
