import BanditRLProof.UnboundedStoppingTimeL2CoordinateIntegrability
import Mathlib.Analysis.MeanInequalities

/-!
# Square-summable weights at an unbounded stopping time

This module replaces a moment assumption on an a.e.-finite stopping time by a
square-summable deterministic weight.  Uniform L2 control of the deterministic
coordinates and Cauchy--Schwarz over the measurable stopping fibers then give
an integrable weighted stopped value.  This is a countable-fiber argument, not
optional stopping.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal ProbabilityTheory Topology

namespace BanditRLProof

universe u

/-- A stopped value is measurable when the stopping index and every
deterministic coordinate are measurable.  The proof decomposes the dynamic
evaluation into countably many natural-number fibers. -/
theorem measurable_stoppedValue_of_measurable_coordinates
    {Omega : Type u} [MeasurableSpace Omega]
    (tau : Omega -> WithTop Nat) (htau : Measurable tau)
    (process : Nat -> Omega -> Real)
    (hprocess : forall n, Measurable (process n)) :
    Measurable (stoppedValue process tau) := by
  let index : Omega -> Nat := fun omega => (tau omega).untopA
  have hindex : Measurable index := htau.untopA
  intro s hs
  have hpreimage :
      stoppedValue process tau ⁻¹' s =
        ⋃ n : Nat, {omega | index omega = n} ∩ process n ⁻¹' s := by
    ext omega
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_setOf_eq]
    constructor
    · intro homega
      refine ⟨index omega, rfl, ?_⟩
      simpa only [index, stoppedValue] using homega
    · rintro ⟨n, hindexEq, homega⟩
      rw [← hindexEq] at homega
      simpa only [index, stoppedValue] using homega
  rw [hpreimage]
  exact MeasurableSet.iUnion fun n =>
    (measurableSet_eq_fun hindex measurable_const).inter
      ((hprocess n) hs)

/-- Square-summable deterministic weights are summable against the square
roots of the real masses of measurable stopping fibers. -/
theorem
    summable_abs_weight_mul_sqrt_stoppingFiberRealMeasure_and_tsum_le
    {Omega : Type u} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (tau : Omega -> WithTop Nat) (htau : Measurable tau)
    (weight : Nat -> Real)
    (hweightSq : Summable (fun n => weight n ^ 2)) :
    Summable (fun n =>
        |weight n| *
          Real.sqrt (mu.real {omega | tau omega = (n : WithTop Nat)})) /\
      (∑' n : Nat,
          |weight n| *
            Real.sqrt (mu.real {omega | tau omega = (n : WithTop Nat)})) <=
        Real.sqrt (∑' n : Nat, weight n ^ 2) *
          Real.sqrt (mu.real Set.univ) := by
  let fiber : Nat -> Set Omega := fun n =>
    {omega | tau omega = (n : WithTop Nat)}
  have hfiberMeasurable (n : Nat) : MeasurableSet (fiber n) := by
    exact measurableSet_eq_fun htau measurable_const
  have hfiberDisjoint : Pairwise (fun i j => Disjoint (fiber i) (fiber j)) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro omega hi hj
    have hijTop : (i : WithTop Nat) = (j : WithTop Nat) := by
      exact hi.symm.trans hj
    exact hij (WithTop.coe_injective hijTop)
  have hfiberSummable : Summable (fun n => mu.real (fiber n)) :=
    summable_measure_toReal hfiberMeasurable hfiberDisjoint
  have hfiberTsumLe :
      (∑' n : Nat, mu.real (fiber n)) <= mu.real Set.univ := by
    calc
      (∑' n : Nat, mu.real (fiber n)) =
          (∑' n : Nat, mu (fiber n)).toReal := by
        simp only [measureReal_def]
        rw [ENNReal.tsum_toReal_eq (fun n => measure_ne_top mu (fiber n))]
      _ = mu.real (Set.iUnion fiber) := by
        rw [measureReal_def,
          MeasureTheory.measure_iUnion hfiberDisjoint hfiberMeasurable]
      _ <= mu.real Set.univ := measureReal_mono (Set.subset_univ _)
  have hweightAbsSq : Summable (fun n => |weight n| ^ (2 : Real)) := by
    simpa [Real.rpow_two, sq_abs] using hweightSq
  have hfiberSqrtSq : Summable (fun n =>
      (Real.sqrt (mu.real (fiber n))) ^ (2 : Real)) := by
    simpa [Real.rpow_two, Real.sq_sqrt measureReal_nonneg] using
      hfiberSummable
  have hpq : (2 : Real).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hholder :=
    Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg hpq
      (fun n => abs_nonneg (weight n))
      (fun n => Real.sqrt_nonneg _)
      hweightAbsSq hfiberSqrtSq
  refine ⟨?_, ?_⟩
  · simpa only [fiber] using hholder.1
  · have hraw :
        (∑' n : Nat, |weight n| * Real.sqrt (mu.real (fiber n))) <=
          Real.sqrt (∑' n : Nat, weight n ^ 2) *
            Real.sqrt (∑' n : Nat, mu.real (fiber n)) := by
      simpa only [← Real.sqrt_eq_rpow, Real.rpow_two, sq_abs,
        Real.sq_sqrt measureReal_nonneg] using hholder.2
    calc
      (∑' n : Nat,
          |weight n| *
            Real.sqrt (mu.real {omega | tau omega = (n : WithTop Nat)})) =
          (∑' n : Nat,
            |weight n| * Real.sqrt (mu.real (fiber n))) := rfl
      _ <= Real.sqrt (∑' n : Nat, weight n ^ 2) *
          Real.sqrt (∑' n : Nat, mu.real (fiber n)) := hraw
      _ <= Real.sqrt (∑' n : Nat, weight n ^ 2) *
          Real.sqrt (mu.real Set.univ) := by
        exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hfiberTsumLe)
          (Real.sqrt_nonneg _)

/-- Uniform deterministic-coordinate second moments and a square-summable
deterministic weight make the weighted stopped value integrable and bound its
absolute first moment. -/
theorem
    integrable_and_integral_abs_stoppedValue_weight_mul_le
    {Omega : Type u} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (tau : Omega -> WithTop Nat) (htau : Measurable tau)
    (hfinite : ∀ᵐ omega ∂mu, tau omega ≠ ⊤)
    (process : Nat -> Omega -> Real)
    (weight : Nat -> Real)
    (hweightSq : Summable (fun n => weight n ^ 2))
    (hstoppedMeasurable :
      Measurable (stoppedValue (fun n omega => weight n * process n omega) tau))
    (secondMomentEnvelope : Real)
    (hprocessMemLp : forall n, MemLp (process n) 2 mu)
    (hprocessSecondMoment : forall n,
      integral mu (fun omega => process n omega ^ 2) <=
        secondMomentEnvelope) :
    Integrable
        (stoppedValue (fun n omega => weight n * process n omega) tau) mu /\
      integral mu (fun omega =>
          |stoppedValue (fun n omega => weight n * process n omega) tau omega|) <=
        Real.sqrt secondMomentEnvelope *
          (Real.sqrt (∑' n : Nat, weight n ^ 2) *
            Real.sqrt (mu.real Set.univ)) := by
  let fiber : Nat -> Set Omega := fun n =>
    {omega | tau omega = (n : WithTop Nat)}
  let term : Nat -> Omega -> Real := fun n =>
    (fiber n).indicator (fun omega => |weight n * process n omega|)
  let majorant : Nat -> Real := fun n =>
    Real.sqrt secondMomentEnvelope *
      (|weight n| * Real.sqrt (mu.real (fiber n)))
  have hfiberMeasurable (n : Nat) : MeasurableSet (fiber n) := by
    exact measurableSet_eq_fun htau measurable_const
  have hweightedFiber :=
    summable_abs_weight_mul_sqrt_stoppingFiberRealMeasure_and_tsum_le
      mu tau htau weight hweightSq
  have hmajorantSummable : Summable majorant := by
    exact hweightedFiber.1.mul_left (Real.sqrt secondMomentEnvelope)
  have htermIntegrable (n : Nat) : Integrable (term n) mu := by
    dsimp only [term]
    exact (((hprocessMemLp n).const_mul (weight n)).integrable
      (by norm_num)).abs.indicator (hfiberMeasurable n)
  have htermNonneg (n : Nat) (omega : Omega) : 0 <= term n omega := by
    by_cases homega : omega ∈ fiber n
    · simp only [term, Set.indicator_of_mem homega]
      exact abs_nonneg _
    · simp [term, homega]
  have htermIntegral (n : Nat) :
      integral mu (term n) <= majorant n := by
    have hholder :=
      integral_indicator_le_sqrt_secondMoment_mul_sqrt_real_measure
        mu (fun omega => |process n omega|) (fun _ => abs_nonneg _)
          (hprocessMemLp n).abs (fiber n) (hfiberMeasurable n)
    have hsqrtMoment :
        Real.sqrt (integral mu (fun omega => |process n omega| ^ 2)) <=
          Real.sqrt secondMomentEnvelope := by
      apply Real.sqrt_le_sqrt
      simpa only [sq_abs] using hprocessSecondMoment n
    calc
      integral mu (term n) =
          |weight n| *
            integral mu ((fiber n).indicator (fun omega => |process n omega|)) := by
        have htermEq : term n = fun omega =>
            |weight n| *
              (fiber n).indicator (fun omega => |process n omega|) omega := by
          funext omega
          by_cases homega : omega ∈ fiber n <;>
            simp [term, homega, abs_mul]
        rw [htermEq, integral_const_mul]
      _ <= |weight n| *
          (Real.sqrt (integral mu (fun omega => |process n omega| ^ 2)) *
            Real.sqrt (mu.real (fiber n))) :=
        mul_le_mul_of_nonneg_left hholder (abs_nonneg _)
      _ <= |weight n| *
          (Real.sqrt secondMomentEnvelope *
            Real.sqrt (mu.real (fiber n))) := by
        gcongr
      _ = majorant n := by
        simp [majorant]
        ring
  have htermIntegralNormSummable :
      Summable (fun n => integral mu (fun omega => ‖term n omega‖)) := by
    apply hmajorantSummable.of_nonneg_of_le
    · intro n
      exact integral_nonneg fun omega => norm_nonneg (term n omega)
    · intro n
      rw [show integral mu (fun omega => ‖term n omega‖) =
          integral mu (term n) by
        apply integral_congr_ae
        filter_upwards with omega
        rw [Real.norm_eq_abs, abs_of_nonneg (htermNonneg n omega)]]
      exact htermIntegral n
  have htermIntegralSummable :
      Summable (fun n => integral mu (term n)) := by
    apply hmajorantSummable.of_nonneg_of_le
    · intro n
      exact integral_nonneg (htermNonneg n)
    · exact htermIntegral
  have hpoint : ∀ᵐ omega ∂mu,
      |stoppedValue (fun n omega => weight n * process n omega) tau omega| =
        ∑' n : Nat, term n omega := by
    filter_upwards [hfinite] with omega htop
    lift tau omega to Nat using htop with hit hhit
    dsimp only [term, fiber]
    rw [tsum_eq_single hit]
    · rw [Set.indicator_of_mem]
      · simp only [stoppedValue]
        have huntopA : (tau omega).untopA = hit := by
          rw [← hhit]
          rfl
        rw [huntopA]
      · exact hhit.symm
    · intro n hn
      rw [Set.indicator_of_notMem]
      intro hmem
      have heq : hit = n := by
        exact WithTop.coe_injective (hhit.trans hmem)
      exact hn heq.symm
  let ennTerm : Nat -> Omega -> ENNReal := fun n =>
    (fiber n).indicator (fun omega => ENNReal.ofReal |weight n * process n omega|)
  have hennTermMeasurable (n : Nat) : AEMeasurable (ennTerm n) mu := by
    exact (((hprocessMemLp n).const_mul (weight n)).aestronglyMeasurable.norm
      |>.aemeasurable.ennreal_ofReal.indicator (hfiberMeasurable n))
  have hennTermIntegral (n : Nat) :
      ∫⁻ omega, ennTerm n omega ∂mu <= ENNReal.ofReal (majorant n) := by
    have htermIntegralNonneg : 0 <= integral mu (term n) :=
      integral_nonneg (htermNonneg n)
    have heq :
        (∫⁻ omega, ennTerm n omega ∂mu) =
          ENNReal.ofReal (integral mu (term n)) := by
      rw [ofReal_integral_eq_lintegral_ofReal (htermIntegrable n)
        (Filter.Eventually.of_forall (htermNonneg n))]
      apply lintegral_congr
      intro omega
      by_cases homega : omega ∈ fiber n <;>
        simp [ennTerm, term, homega]
    rw [heq]
    exact ENNReal.ofReal_le_ofReal (htermIntegral n)
  have hennPoint : ∀ᵐ omega ∂mu,
      ENNReal.ofReal
          |stoppedValue (fun n omega => weight n * process n omega) tau omega| =
        ∑' n : Nat, ennTerm n omega := by
    filter_upwards [hfinite] with omega htop
    lift tau omega to Nat using htop with hit hhit
    dsimp only [ennTerm, fiber]
    rw [tsum_eq_single hit]
    · rw [Set.indicator_of_mem]
      · simp only [stoppedValue]
        have huntopA : (tau omega).untopA = hit := by
          rw [← hhit]
          rfl
        rw [huntopA]
      · exact hhit.symm
    · intro n hn
      rw [Set.indicator_of_notMem]
      intro hmem
      have heq : hit = n := by
        exact WithTop.coe_injective (hhit.trans hmem)
      exact hn heq.symm
  have hennSumFinite :
      (∑' n : Nat, ∫⁻ omega, ennTerm n omega ∂mu) < ⊤ := by
    apply lt_of_le_of_lt (ENNReal.tsum_le_tsum hennTermIntegral)
    exact lt_top_iff_ne_top.mpr hmajorantSummable.tsum_ofReal_ne_top
  have hstoppedIntegrable :
      Integrable
        (stoppedValue (fun n omega => weight n * process n omega) tau) mu := by
    refine ⟨hstoppedMeasurable.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    calc
      ∫⁻ omega,
          ENNReal.ofReal
            ‖stoppedValue (fun n omega => weight n * process n omega) tau omega‖
          ∂mu =
          ∫⁻ omega, ∑' n : Nat, ennTerm n omega ∂mu := by
        apply lintegral_congr_ae
        filter_upwards [hennPoint] with omega homega
        simpa only [Real.norm_eq_abs] using homega
      _ = ∑' n : Nat, ∫⁻ omega, ennTerm n omega ∂mu := by
        rw [lintegral_tsum hennTermMeasurable]
      _ < ⊤ := hennSumFinite
  refine ⟨hstoppedIntegrable, ?_⟩
  calc
    integral mu (fun omega =>
        |stoppedValue (fun n omega => weight n * process n omega) tau omega|) =
        integral mu (fun omega => ∑' n : Nat, term n omega) :=
      integral_congr_ae hpoint
    _ = ∑' n : Nat, integral mu (term n) :=
      (integral_tsum_of_summable_integral_norm htermIntegrable
        htermIntegralNormSummable).symm
    _ <= ∑' n : Nat, majorant n := by
      exact htermIntegralSummable.tsum_le_tsum htermIntegral
        hmajorantSummable
    _ = Real.sqrt secondMomentEnvelope *
        (∑' n : Nat,
          |weight n| * Real.sqrt (mu.real (fiber n))) := by
      rw [tsum_mul_left]
    _ <= Real.sqrt secondMomentEnvelope *
        (Real.sqrt (∑' n : Nat, weight n ^ 2) *
          Real.sqrt (mu.real Set.univ)) :=
      mul_le_mul_of_nonneg_left hweightedFiber.2 (Real.sqrt_nonneg _)

end BanditRLProof
