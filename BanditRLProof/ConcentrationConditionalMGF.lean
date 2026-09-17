import BanditRLProof.ConcentrationFixedMGF

/-! Constructors connecting conditional expectation bounds to the shared
fixed-tilt conditional MGF interface. -/
namespace BanditRLProof.Concentration
open MeasureTheory ProbabilityTheory

theorem hasCondMGFUpperBoundAt_of_condExp_le
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ) (X : Ω → ℝ) (t ψ : ℝ)
    (hi : ∀ s, Integrable (fun ω => Real.exp (s * X ω)) μ)
    (hc : μ[fun ω => Real.exp (t * X ω) | m] ≤ᵐ[μ] fun _ => Real.exp ψ) :
    HasCondMGFUpperBoundAt m hm X t ψ μ := by
  letI : MeasurableSpace Ω := mΩ
  have hc' : μ[fun ω => Real.exp (t * X ω) | m] ≤ᵐ[μ.trim hm]
      fun _ => Real.exp ψ := by
    rw [Filter.EventuallyLE, ae_iff] at hc ⊢
    have hf : Measurable[m] (μ[fun ω => Real.exp (t * X ω) | m]) :=
      stronglyMeasurable_condExp.measurable
    have hs : @MeasurableSet Ω m {a | ¬μ[fun ω => Real.exp (t * X ω) | m] a ≤
        Real.exp ψ} :=
      (measurableSet_le hf (measurable_const (a := Real.exp ψ))).compl
    rw [trim_measurableSet_eq hm hs]
    exact hc
  constructor
  · intro s
    simpa only [condExpKernel_comp_trim] using hi s
  · have he := condExp_ae_eq_trim_integral_condExpKernel hm (hi t)
    filter_upwards [hc', he] with ω hc' he
    simpa only [he, mgf] using hc'

end BanditRLProof.Concentration
