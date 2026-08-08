import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# Independence through a past-measurable kernel extension

This module records the semidirect-product transport needed by stochastic
bandit trajectory laws.  Sampling from a Markov kernel that only sees a past
summary cannot create dependence between its output and a random variable
already independent of that summary.
-/

open MeasureTheory ProbabilityTheory

namespace BanditRLProof

/-- Pull independence on a pushforward measure back along the measurable map
that produced that pushforward. -/
theorem IndepFun.comp_of_map
    {Omega Sample X Y : Type*}
    [MeasurableSpace Omega] [MeasurableSpace Sample]
    [MeasurableSpace X] [MeasurableSpace Y]
    {mu : Measure Omega} {z : Omega -> Sample}
    {x : Sample -> X} {y : Sample -> Y}
    (hz : Measurable z) (hx : Measurable x) (hy : Measurable y)
    (hindep : IndepFun x y (mu.map z)) :
    IndepFun (x ∘ z) (y ∘ z) mu := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul] at hindep ⊢
  intro s t hs ht
  have hxs : MeasurableSet (x ⁻¹' s) := hx hs
  have hyt : MeasurableSet (y ⁻¹' t) := hy ht
  have h := hindep s t hs ht
  rw [Measure.map_apply hz (hxs.inter hyt),
    Measure.map_apply hz hxs, Measure.map_apply hz hyt] at h
  simpa only [Function.comp_apply, Set.preimage_inter] using h

/-- If `x` is independent of `past`, adjoining a Markov-kernel output whose
law only depends on `past` leaves `x` independent of that output. -/
theorem indepFun_fst_snd_compProd_comap_of_indepFun
    {Omega X Past Output : Type*}
    [MeasurableSpace Omega] [MeasurableSpace X]
    [MeasurableSpace Past] [MeasurableSpace Output]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (x : Omega -> X) (hx : Measurable x)
    (past : Omega -> Past) (hpast : Measurable past)
    (kernel : Kernel Past Output) [IsMarkovKernel kernel]
    (hindep : IndepFun x past mu) :
    IndepFun (x ∘ Prod.fst) Prod.snd
      (mu ⊗ₘ kernel.comap past hpast) := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro s t hs ht
  let liftedKernel := kernel.comap past hpast
  let rho := mu ⊗ₘ liftedKernel
  have hleft : Measurable (fun omega : Omega =>
      s.indicator (fun _ => (1 : ENNReal)) (x omega)) :=
    (measurable_const.indicator hs).comp hx
  have hright : Measurable (fun omega : Omega => kernel (past omega) t) :=
    (kernel.measurable_coe ht).comp hpast
  have hindepValues : IndepFun
      (fun omega : Omega => s.indicator (fun _ => (1 : ENNReal)) (x omega))
      (fun omega : Omega => kernel (past omega) t) mu :=
    hindep.comp (measurable_const.indicator hs) (kernel.measurable_coe ht)
  have hfactor :=
    lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun
      hleft hright hindepValues
  change rho ({sample | x sample.1 ∈ s} ∩ {sample | sample.2 ∈ t}) =
    rho {sample | x sample.1 ∈ s} * rho {sample | sample.2 ∈ t}
  rw [Measure.compProd_apply]
  · rw [Measure.compProd_apply]
    · rw [Measure.compProd_apply]
      · simp only [liftedKernel, Kernel.comap_apply]
        convert hfactor using 1
        · apply lintegral_congr
          intro omega
          by_cases homega : x omega ∈ s <;> simp [homega, Set.indicator]
        · congr 1
          apply lintegral_congr
          intro omega
          by_cases homega : x omega ∈ s <;> simp [homega, Set.indicator]
      · exact measurable_snd ht
    · exact hx.comp measurable_fst hs
  · exact (hx.comp measurable_fst hs).inter (measurable_snd ht)

end BanditRLProof
