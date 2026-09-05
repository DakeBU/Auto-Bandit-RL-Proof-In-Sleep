import BanditRLProof.LowerBounds.InformationTheory
import Mathlib.Probability.Martingale.Convergence

/-! Recovery of relative entropy from a filtration resolving the RN density. -/

namespace BanditRLProof.LowerBounds

open MeasureTheory Set Filter
open scoped ENNReal Topology

noncomputable section

/-- Trimmed KL as the convex lower integral of the conditional RN density. -/
theorem relativeEntropy_trim_eq_lintegral_condExp
    {α : Type*} {m m₀ : MeasurableSpace α} (P Q : @Measure α m₀)
    [IsFiniteMeasure P] [IsFiniteMeasure Q] (hm : m ≤ m₀) (h : P ≪ Q) :
    @relativeEntropy α m (P.trim hm) (Q.trim hm) =
      ∫⁻ x, ENNReal.ofReal (InformationTheory.klFun
        (Q[fun y => (P.rnDeriv Q y).toReal | m] x)) ∂Q := by
  calc
    _ = ∫⁻ x, ENNReal.ofReal (InformationTheory.klFun
        (((P.trim hm).rnDeriv (Q.trim hm)) x).toReal) ∂Q.trim hm :=
      InformationTheory.klDiv_eq_lintegral_klFun_of_ac (h.trim hm)
    _ = ∫⁻ x, ENNReal.ofReal (InformationTheory.klFun
        (Q[fun y => (P.rnDeriv Q y).toReal | m] x)) ∂Q.trim hm := by
      apply lintegral_congr_ae
      filter_upwards [toReal_rnDeriv_trim hm h] with x hx
      rw [hx]
    _ = _ := lintegral_trim hm (by fun_prop)

/-- A measurable observation has the same KL as restriction to its generated sigma-algebra. -/
theorem relativeEntropy_map_eq_trim_of_absolutelyContinuous
    {α β : Type*} [mα : MeasurableSpace α] [mβ : MeasurableSpace β]
    (P Q : Measure α) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (h : P ≪ Q) (f : α → β) (hf : Measurable f) :
    relativeEntropy (P.map f) (Q.map f) =
      @relativeEntropy α (mβ.comap f) (P.trim hf.comap_le) (Q.trim hf.comap_le) := by
  calc
    _ = ∫⁻ y, ENNReal.ofReal (InformationTheory.klFun
        (((P.map f).rnDeriv (Q.map f)) y).toReal) ∂Q.map f :=
      InformationTheory.klDiv_eq_lintegral_klFun_of_ac (h.map hf)
    _ = ∫⁻ x, ENNReal.ofReal (InformationTheory.klFun
        (((P.map f).rnDeriv (Q.map f)) (f x)).toReal) ∂Q :=
      lintegral_map (by fun_prop) hf
    _ = ∫⁻ x, ENNReal.ofReal (InformationTheory.klFun
        (Q[fun y => (P.rnDeriv Q y).toReal | mβ.comap f] x)) ∂Q := by
      apply lintegral_congr_ae
      filter_upwards [toReal_rnDeriv_map h hf] with x hx
      rw [hx]
    _ = _ := (relativeEntropy_trim_eq_lintegral_condExp P Q hf.comap_le h).symm

/-- Resolving the RN density along a filtration recovers KL, including infinite KL. -/
theorem relativeEntropy_eq_iSup_trim_of_density_measurable
    {α : Type*} [m₀ : MeasurableSpace α] (P Q : Measure α)
    [IsFiniteMeasure P] [IsFiniteMeasure Q] (h : P ≪ Q)
    (F : Filtration ℕ m₀)
    (hDensity : StronglyMeasurable[⨆ n, F n] (fun x => (P.rnDeriv Q x).toReal)) :
    relativeEntropy P Q =
      ⨆ n, @relativeEntropy α (F n) (P.trim (F.le n)) (Q.trim (F.le n)) := by
  let d : α → ℝ := fun x => (P.rnDeriv Q x).toReal
  let g : ℕ → α → ENNReal := fun n x =>
    ENNReal.ofReal (InformationTheory.klFun (Q[d | F n] x))
  have hd : Integrable d Q := Measure.integrable_toReal_rnDeriv
  have hc := hd.tendsto_ae_condExp hDensity
  have hlim : ∀ᵐ x ∂Q, Tendsto (fun n => g n x) atTop
      (𝓝 (ENNReal.ofReal (InformationTheory.klFun (d x)))) := by
    filter_upwards [hc] with x hx
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (InformationTheory.continuous_klFun.continuousAt.tendsto.comp hx)
  have hg (n : ℕ) : Measurable (g n) := by
    have hm : Measurable (Q[d | F n]) :=
      (stronglyMeasurable_condExp.mono (F.le n)).measurable
    exact ENNReal.continuous_ofReal.measurable.comp
      (InformationTheory.continuous_klFun.measurable.comp hm)
  have hterm (n : ℕ) : (∫⁻ x, g n x ∂Q) =
      @relativeEntropy α (F n) (P.trim (F.le n)) (Q.trim (F.le n)) :=
    (relativeEntropy_trim_eq_lintegral_condExp P Q (F.le n) h).symm
  apply le_antisymm
  · calc
      relativeEntropy P Q = ∫⁻ x, ENNReal.ofReal (InformationTheory.klFun (d x)) ∂Q :=
        InformationTheory.klDiv_eq_lintegral_klFun_of_ac h
      _ = ∫⁻ x, liminf (fun n => g n x) atTop ∂Q := by
        apply lintegral_congr_ae
        filter_upwards [hlim] with x hx
        exact hx.liminf_eq.symm
      _ ≤ liminf (fun n => ∫⁻ x, g n x ∂Q) atTop := lintegral_liminf_le hg
      _ ≤ _ := liminf_le_of_frequently_le' (Frequently.of_forall fun n =>
        (hterm n).le.trans (le_iSup (fun k =>
          @relativeEntropy α (F k) (P.trim (F.le k)) (Q.trim (F.le k))) n))
  · exact iSup_le fun n => relativeEntropy_trim_le (F.le n)

/-- Natural filtration of the finite-valued lower approximations to a density. -/
def densityApproximationFiltration {α : Type*} [m : MeasurableSpace α]
    (r : α → ENNReal) : Filtration ℕ m :=
  Filtration.natural (fun n => (SimpleFunc.eapprox r n : α → ENNReal))
    (fun n => (SimpleFunc.eapprox r n).measurable.stronglyMeasurable)

/-- The limiting sigma-algebra of the approximation filtration resolves the density. -/
theorem measurable_density_iSup_approximationFiltration
    {α : Type*} [m : MeasurableSpace α] (r : α → ENNReal) (hr : Measurable r) :
    Measurable[⨆ n, densityApproximationFiltration r n] r := by
  have hm (n : ℕ) :
      StronglyMeasurable[densityApproximationFiltration r n]
        (SimpleFunc.eapprox r n : α → ENNReal) :=
    Filtration.stronglyAdapted_natural
      (fun k => (SimpleFunc.eapprox r k).measurable.stronglyMeasurable) n
  have hall (n : ℕ) :
      Measurable[⨆ k, densityApproximationFiltration r k]
        (SimpleFunc.eapprox r n : α → ENNReal) :=
    ((hm n).mono (le_iSup _ n)).measurable
  have hs := Measurable.iSup hall
  simpa only [SimpleFunc.iSup_eapprox_apply hr] using hs

/-- RN KL is recovered along a concretely constructed simple-approximation filtration. -/
theorem relativeEntropy_eq_iSup_densityApproximation_trim
    {α : Type*} [m : MeasurableSpace α] (P Q : Measure α)
    [IsFiniteMeasure P] [IsFiniteMeasure Q] (h : P ≪ Q) :
    relativeEntropy P Q = ⨆ n,
      @relativeEntropy α (densityApproximationFiltration (P.rnDeriv Q) n)
        (P.trim ((densityApproximationFiltration (P.rnDeriv Q)).le n))
        (Q.trim ((densityApproximationFiltration (P.rnDeriv Q)).le n)) := by
  apply relativeEntropy_eq_iSup_trim_of_density_measurable P Q h
  exact (measurable_density_iSup_approximationFiltration (P.rnDeriv Q)
    (Measure.measurable_rnDeriv P Q)).ennreal_toReal.stronglyMeasurable

end
end BanditRLProof.LowerBounds
