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

namespace Measure

/-- Restricting both coordinates of a semidirect product is the semidirect
product of the restricted base measure and restricted fiber kernel. -/
theorem compProd_restrict_prod
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (mu : Measure A) [SFinite mu]
    (kernel : Kernel A B) [IsSFiniteKernel kernel]
    {s : Set A} {t : Set B} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    (mu ⊗ₘ kernel).restrict (s ×ˢ t) =
      mu.restrict s ⊗ₘ kernel.restrict ht := by
  have hprodMk :
      (Kernel.prodMkLeft Unit kernel).restrict ht =
        Kernel.prodMkLeft Unit (kernel.restrict ht) := by
    ext input
    rw [Kernel.restrict_apply, Kernel.prodMkLeft_apply,
      Kernel.prodMkLeft_apply, Kernel.restrict_apply]
  unfold Measure.compProd
  rw [← Kernel.restrict_const (α := Unit) hs, ← hprodMk]
  exact congrArg (fun extendedKernel => extendedKernel ())
    (Kernel.compProd_restrict
      (κ := Kernel.const Unit mu)
      (η := Kernel.prodMkLeft Unit kernel) hs ht).symm

end Measure

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

/-- If `x` is independent of `past`, adjoining an output through a finite
kernel that only sees `past` gives the joint output/`x` law as the output
marginal times the original `x` marginal.  Unlike the preceding `IndepFun`
wrapper, this statement remains valid for subprobability kernels such as a
branch-restricted Markov kernel. -/
theorem map_snd_x_compProd_comap_eq_prod_map_of_indepFun
    {Omega X Past Output : Type*}
    [MeasurableSpace Omega] [MeasurableSpace X]
    [MeasurableSpace Past] [MeasurableSpace Output]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (x : Omega -> X) (hx : Measurable x)
    (past : Omega -> Past) (hpast : Measurable past)
    (kernel : Kernel Past Output) [IsFiniteKernel kernel]
    (hindep : IndepFun x past mu) :
    Measure.map (fun sample : Omega × Output => (sample.2, x sample.1))
        (mu ⊗ₘ kernel.comap past hpast) =
      (Measure.map Prod.snd (mu ⊗ₘ kernel.comap past hpast)).prod
        (Measure.map x mu) := by
  apply Measure.ext_prod
  intro outputEvent xEvent houtputEvent hxEvent
  let liftedKernel := kernel.comap past hpast
  let rho := mu ⊗ₘ liftedKernel
  have hleft : Measurable (fun omega : Omega =>
      xEvent.indicator (fun _ => (1 : ENNReal)) (x omega)) :=
    (measurable_const.indicator hxEvent).comp hx
  have hright : Measurable
      (fun omega : Omega => kernel (past omega) outputEvent) :=
    (kernel.measurable_coe houtputEvent).comp hpast
  have hindepValues : IndepFun
      (fun omega : Omega =>
        xEvent.indicator (fun _ => (1 : ENNReal)) (x omega))
      (fun omega : Omega => kernel (past omega) outputEvent) mu :=
    hindep.comp (measurable_const.indicator hxEvent)
      (kernel.measurable_coe houtputEvent)
  have hfactor :=
    lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun
      hleft hright hindepValues
  have hjoint : Measurable
      (fun sample : Omega × Output => (sample.2, x sample.1)) := by
    fun_prop
  rw [Measure.map_apply
      hjoint (houtputEvent.prod hxEvent),
    Measure.prod_prod outputEvent xEvent,
    Measure.map_apply measurable_snd houtputEvent,
    Measure.map_apply hx hxEvent]
  change rho
      {sample : Omega × Output |
        sample.2 ∈ outputEvent ∧ x sample.1 ∈ xEvent} =
    rho {sample : Omega × Output | sample.2 ∈ outputEvent} *
      mu {omega : Omega | x omega ∈ xEvent}
  rw [Measure.compProd_apply]
  · rw [Measure.compProd_apply]
    · simp only [liftedKernel, Kernel.comap_apply]
      have hjointIntegral :
          (∫⁻ omega,
              kernel (past omega)
                (Prod.mk omega ⁻¹'
                  {sample : Omega × Output |
                    sample.2 ∈ outputEvent ∧ x sample.1 ∈ xEvent}) ∂mu) =
            ∫⁻ omega,
              xEvent.indicator (fun _ => (1 : ENNReal)) (x omega) *
                kernel (past omega) outputEvent ∂mu := by
        apply lintegral_congr
        intro omega
        by_cases homega : x omega ∈ xEvent <;>
          simp [homega, Set.indicator]
      have houtputIntegral :
          (∫⁻ omega,
              kernel (past omega)
                (Prod.mk omega ⁻¹'
                  {sample : Omega × Output |
                    sample.2 ∈ outputEvent}) ∂mu) =
            ∫⁻ omega, kernel (past omega) outputEvent ∂mu := by
        apply lintegral_congr
        intro omega
        rfl
      have hindicator :
          (∫⁻ omega,
              xEvent.indicator (fun _ => (1 : ENNReal)) (x omega) ∂mu) =
            mu {omega : Omega | x omega ∈ xEvent} := by
        have hset : MeasurableSet {omega : Omega | x omega ∈ xEvent} :=
          hx hxEvent
        have hfun :
            (fun omega : Omega =>
              xEvent.indicator (fun _ => (1 : ENNReal)) (x omega)) =
              {omega : Omega | x omega ∈ xEvent}.indicator
                (fun _ => (1 : ENNReal)) := by
          funext omega
          by_cases homega : x omega ∈ xEvent <;>
            simp [homega, Set.indicator]
        rw [hfun]
        simpa only [Pi.one_apply] using
          (MeasureTheory.lintegral_indicator_one (μ := mu) hset)
      have hfactor' :
          (∫⁻ omega,
              xEvent.indicator (fun _ => (1 : ENNReal)) (x omega) *
                kernel (past omega) outputEvent ∂mu) =
            (∫⁻ omega,
              xEvent.indicator (fun _ => (1 : ENNReal)) (x omega) ∂mu) *
              ∫⁻ omega, kernel (past omega) outputEvent ∂mu := by
        simpa only [Pi.mul_apply] using hfactor
      rw [hjointIntegral, houtputIntegral, hfactor', hindicator, mul_comm]
    · exact measurable_snd houtputEvent
  · exact (measurable_snd houtputEvent).inter
      (hx.comp measurable_fst hxEvent)

end BanditRLProof
