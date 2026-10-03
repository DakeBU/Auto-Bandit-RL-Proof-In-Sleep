import BanditRLProof.Algorithms.CUCBOracleMeasurable
import Mathlib.Probability.Kernel.CondDistrib

/-! Per-input approximate oracle success lifted to the actual initial and
conditional successor laws, with the actual history-dependent oracle input. -/
namespace BanditRLProof.CUCB.SourceModel
open MeasureTheory ProbabilityTheory
set_option autoImplicit false
variable {A : Type*} [Fintype A] [Nonempty A] [MeasurableSpace A]
  [MeasurableSingletonClass A] {m : ℕ} {M : FeedbackModel A m} (S : SourceModel M)

noncomputable def successIndicator (v : Input m) (z : Round A m) : ℝ := by
  classical
  exact if (v,z.1)∈S.oracleSuccess then 1 else 0

theorem measurable_successIndicator : Measurable
    (fun p : Input m × Round A m => S.successIndicator p.1 p.2) := by
  unfold successIndicator
  exact measurable_const.ite
    (S.measurableSet_oracleSuccess.preimage (by fun_prop)) measurable_const

omit [MeasurableSingletonClass A] in
theorem successIndicator_mem (v : Input m) (z : Round A m) :
    S.successIndicator v z∈Set.Icc (0:ℝ) 1 := by
  unfold successIndicator
  split_ifs <;> norm_num

theorem integrable_successIndicator_comp {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (g : Ω → Input m × Round A m) (hg : Measurable g) :
    Integrable (fun ω => S.successIndicator (g ω).1 (g ω).2) ν := by
  apply (integrable_const (1:ℝ)).mono'
    (S.measurable_successIndicator.comp hg).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro ω
  simp only [Function.comp_apply, Real.norm_eq_abs]
  rw [abs_of_nonneg (S.successIndicator_mem _ _).1]
  exact (S.successIndicator_mem _ _).2

theorem roundKernel_success_lower (v : Input m) :
    S.beta≤∫z, S.successIndicator v z ∂roundKernel S.oracle M.environment v := by
  classical
  let E : Set A := {a | (v,a)∈S.oracleSuccess}
  have hE : MeasurableSet E := S.measurableSet_oracleSuccess.preimage
    (measurable_const.prodMk measurable_id)
  have he := integral_map (μ:=roundKernel S.oracle M.environment v) measurable_fst.aemeasurable
    ((measurable_const.indicator hE : Measurable (E.indicator (fun _ => (1:ℝ))))).aestronglyMeasurable
  rw [roundKernel_action_law, integral_indicator_const 1 hE] at he
  simp only [measureReal_def, smul_eq_mul, mul_one] at he
  have hb : S.beta≤(S.oracle v E).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1 (S.oracle_success v)
  simpa only [measureReal_def, smul_eq_mul, mul_one, Function.comp_def,
    Set.indicator_apply, successIndicator] using (he ▸ hb)

variable [sA : StandardBorelSpace A]
include sA

theorem condExp_oracle_success (n : ℕ) :
    (fun _ => S.beta) ≤ᵐ[cucbTrajectory S.oracle M.environment]
      (cucbTrajectory S.oracle M.environment)[fun Y =>
        S.successIndicator (oracleInput (fun t => (Y t).2) (n+1)) (Y (n+1)) |
        MeasurableSpace.comap (Preorder.frestrictLe n) inferInstance] := by
  let P := fun Y : ℕ → Round A m => (Preorder.frestrictLe n Y, Y (n+1))
  have hP : Measurable P := (Preorder.measurable_frestrictLe n).prodMk (measurable_pi_apply (n+1))
  letI : IsProbabilityMeasure ((cucbTrajectory S.oracle M.environment).map P) :=
    Measure.isProbabilityMeasure_map hP.aemeasurable
  have hg : Measurable (fun p : ((i : Finset.Iic n) → Round A m) × Round A m =>
      (oracleInput (feedbackExtension n p.1) (n+1),p.2)) :=
    (((measurable_oracleInput (n+1)).comp (measurable_feedbackExtension n)).comp
      measurable_fst).prodMk measurable_snd
  have hi := S.integrable_successIndicator_comp ((cucbTrajectory S.oracle M.environment).map P) _ hg
  have hc := condExp_prod_ae_eq_integral_condDistrib' (μ:=cucbTrajectory S.oracle M.environment)
    (f:=fun p => S.successIndicator (oracleInput (feedbackExtension n p.1) (n+1)) p.2)
    (Preorder.measurable_frestrictLe n) (measurable_pi_apply (n+1)).aemeasurable hi
  simp only [oracleInput_feedbackExtension] at hc
  have hk := ae_of_ae_map (Preorder.measurable_frestrictLe n).aemeasurable
    (cucbTrajectory_condDistrib S.oracle M.environment n)
  filter_upwards [hc, hk] with Y hc hk
  rw [hc, hk]
  simp only [cucbStepKernel, Kernel.comap_apply, oracleInput_feedbackExtension]
  exact S.roundKernel_success_lower _

omit sA in
theorem initial_oracle_success :
    S.beta≤∫Y, S.successIndicator (oracleInput (fun t => (Y t).2) 0) (Y 0)
      ∂cucbTrajectory S.oracle M.environment := by
  simp only [oracleInput_zero]
  have he := integral_map (μ:=cucbTrajectory S.oracle M.environment)
    (measurable_pi_apply 0).aemeasurable
    ((S.measurable_successIndicator.comp
      (show Measurable (fun z : Round A m => (initialInput m,z)) by fun_prop))).aestronglyMeasurable
  rw [cucbTrajectory_initial_law] at he
  simp only [Function.comp_def] at he
  rw [← he]
  exact S.roundKernel_success_lower _

theorem expected_oracle_success (n : ℕ) :
    S.beta≤∫Y, S.successIndicator (oracleInput (fun t => (Y t).2) n) (Y n)
      ∂cucbTrajectory S.oracle M.environment := by
  cases n with
  | zero => exact S.initial_oracle_success
  | succ n =>
    have h := integral_mono_ae (integrable_const S.beta) integrable_condExp
      (S.condExp_oracle_success n)
    rw [integral_condExp (Preorder.measurable_frestrictLe n).comap_le] at h
    simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using h

theorem oracle_failure_probability (n : ℕ) :
    (cucbTrajectory S.oracle M.environment)
      {Y | (oracleInput (fun t => (Y t).2) n,(Y n).1)∈S.oracleSuccess}ᶜ ≤
        ENNReal.ofReal (1-S.beta) := by
  classical
  let P := cucbTrajectory S.oracle M.environment
  let E : Set (ℕ → Round A m) :=
    {Y | (oracleInput (fun t => (Y t).2) n,(Y n).1)∈S.oracleSuccess}
  have hE : MeasurableSet E := S.measurableSet_path_oracleSuccess n
  have hi : (∫Y, S.successIndicator (oracleInput (fun t => (Y t).2) n) (Y n) ∂P)=
      (P E).toReal := by
    simpa only [Set.indicator_apply, successIndicator, measureReal_def] using
      (integral_indicator_one (μ:=P) hE)
  have hb := S.expected_oracle_success n
  change S.beta≤∫Y, S.successIndicator (oracleInput (fun t => (Y t).2) n) (Y n) ∂P at hb
  rw [hi] at hb
  have ht := measureReal_add_measureReal_compl (μ:=P) hE
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one] at ht
  change P Eᶜ≤ENNReal.ofReal (1-S.beta)
  rw [← ENNReal.ofReal_toReal (measure_ne_top P Eᶜ)]
  exact ENNReal.ofReal_le_ofReal (by linarith)

end BanditRLProof.CUCB.SourceModel
