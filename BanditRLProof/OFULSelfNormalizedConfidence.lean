import BanditRLProof.ConditionalExpectationReward
import BanditRLProof.ConcentrationSubGaussian
import BanditRLProof.OFULEllipticalPotentialFoundation

/-!
# OFUL self-normalized confidence route

This module starts the probabilistic OFUL route after the deterministic
elliptical-potential theorem.  It first formalizes the predictable-projection
conditional exponential inequality used by the method of mixtures.  The
multivariate Gaussian mixture identity and final self-normalized event bound
remain separate until they are compiled locally.
-/

namespace ProbabilityTheory

open MeasureTheory Real

open scoped ENNReal NNReal ProbabilityTheory

universe u

/--
Freeze a conditioning-measurable multiplier inside the conditional law and
compensate its conditionally sub-Gaussian MGF.

The explicit exponential-integrability premise is the regularity required by
the local fixed-tilt composition API. A bounded-predictable-multiplier wrapper
will discharge it for the OFUL feature process.
-/
theorem HasCondSubgaussianMGF.predictable_mul_compensated_hasCondMGFUpperBoundAt
    {Omega : Type u} {m mOmega : MeasurableSpace Omega}
    [StandardBorelSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {X A : Omega -> Real} {c : NNReal}
    (hm : m <= mOmega)
    (hX : HasCondSubgaussianMGF m hm X c mu)
    (hA : @Measurable Omega Real m inferInstance A)
    (hintegrable : forall s : Real,
      Integrable
        (fun omega =>
          Real.exp
            (s * (A omega * X omega -
              (((c : NNReal) : Real) * A omega ^ 2 / 2))))
        mu) :
    BanditRLProof.Concentration.HasCondMGFUpperBoundAt m hm
      (fun omega =>
        A omega * X omega -
          (((c : NNReal) : Real) * A omega ^ 2 / 2))
      1 0 mu := by
  let kappa := ProbabilityTheory.condExpKernel mu m
  have hAmap :=
    BanditRLProof.ConditionalExpectationReward.condExpKernel_map_eq_dirac_of_measurable
      (mOmega := mOmega) mu m hm A hA
  change BanditRLProof.Concentration.Kernel.HasMGFUpperBoundAt
    (fun omega =>
      A omega * X omega -
        (((c : NNReal) : Real) * A omega ^ 2 / 2))
    1 0 kappa (mu.trim hm)
  refine ⟨?_, ?_⟩
  · intro s
    rw [show kappa ∘ₘ (mu.trim hm) = mu by
      simpa [kappa] using
        (ProbabilityTheory.condExpKernel_comp_trim (μ := mu) hm)]
    exact hintegrable s
  · filter_upwards [hX.mgf_le, hAmap] with omega hmgf hmap
    letI : IsProbabilityMeasure (kappa omega) := by
      dsimp [kappa]
      infer_instance
    have hAeq :
        Filter.EventuallyEq (ae (kappa omega)) A
          (fun _ : Omega => A omega) :=
      BanditRLProof.ConditionalExpectationReward.eventuallyEq_const_of_map_eq_dirac
        (kappa omega) A (A omega) (hA.mono hm le_rfl) hmap
    have hcomp :
        (fun y =>
          A y * X y -
            (((c : NNReal) : Real) * A y ^ 2 / 2)) =ᵐ[kappa omega]
        (fun y =>
          A omega * X y -
            (((c : NNReal) : Real) * A omega ^ 2 / 2)) := by
      filter_upwards [hAeq] with y hy
      rw [hy]
    rw [ProbabilityTheory.mgf_congr hcomp]
    have hmgf_eq :
        ProbabilityTheory.mgf
            (fun y =>
              A omega * X y -
                (((c : NNReal) : Real) * A omega ^ 2 / 2))
            (kappa omega) 1 =
          Real.exp
              (-(((c : NNReal) : Real) * A omega ^ 2 / 2)) *
            ProbabilityTheory.mgf X (kappa omega) (A omega) := by
      rw [ProbabilityTheory.mgf]
      simp_rw [one_mul]
      have hfun :
          (fun y =>
            Real.exp
              (A omega * X y -
                (((c : NNReal) : Real) * A omega ^ 2 / 2))) =
            (fun y =>
              Real.exp
                  (-(((c : NNReal) : Real) * A omega ^ 2 / 2)) *
                Real.exp (A omega * X y)) := by
        funext y
        rw [show
          A omega * X y -
              (((c : NNReal) : Real) * A omega ^ 2 / 2) =
            -(((c : NNReal) : Real) * A omega ^ 2 / 2) +
              A omega * X y by ring,
          Real.exp_add]
      rw [hfun, MeasureTheory.integral_const_mul]
      rfl
    rw [hmgf_eq]
    calc
      Real.exp
            (-(((c : NNReal) : Real) * A omega ^ 2 / 2)) *
          ProbabilityTheory.mgf X (kappa omega) (A omega) <=
          Real.exp
              (-(((c : NNReal) : Real) * A omega ^ 2 / 2)) *
            Real.exp
              (((c : NNReal) : Real) * A omega ^ 2 / 2) := by
        gcongr
        simpa using hmgf (A omega)
      _ = Real.exp 0 := by
        rw [← Real.exp_add]
        congr 1
        ring

/--
Uniform boundedness of a predictable multiplier discharges the exponential
integrability contract of the compensated increment.
-/
theorem HasCondSubgaussianMGF.integrable_exp_mul_predictable_mul_compensated_of_abs_le
    {Omega : Type u} {m mOmega : MeasurableSpace Omega}
    [StandardBorelSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {X A : Omega -> Real} {c : NNReal}
    (hm : m <= mOmega)
    (hX : HasCondSubgaussianMGF m hm X c mu)
    (hA : @Measurable Omega Real m inferInstance A)
    (B : Real) (hB : 0 <= B)
    (hAbound : forall omega, |A omega| <= B) :
    forall s : Real,
      Integrable
        (fun omega =>
          Real.exp
            (s * (A omega * X omega -
              (((c : NNReal) : Real) * A omega ^ 2 / 2))))
        mu := by
  intro s
  let q : Real := ((c : NNReal) : Real) / 2
  let D : Real := |s| * B
  let C : Real := |s| * q * B ^ 2
  have hD : 0 <= D := mul_nonneg (abs_nonneg s) hB
  have hdom0 :
      Integrable (fun omega => Real.exp (D * |X omega|)) mu := by
    exact ProbabilityTheory.integrable_exp_mul_abs
      (hX.integrable_exp_mul D)
      (hX.integrable_exp_mul (-D))
  have hdom :
      Integrable
        (fun omega => Real.exp C * Real.exp (D * |X omega|)) mu :=
    hdom0.const_mul (Real.exp C)
  have hXmeas : AEStronglyMeasurable X mu :=
    (hX.integrable hm).1
  have htargetMeas :
      AEStronglyMeasurable
        (fun omega =>
          Real.exp
            (s * (A omega * X omega -
              (((c : NNReal) : Real) * A omega ^ 2 / 2))))
        mu := by
    have hAambient : Measurable A := hA.mono hm le_rfl
    fun_prop
  refine Integrable.mono' hdom htargetMeas (ae_of_all mu fun omega => ?_)
  have hq : 0 <= q := by
    dsimp [q]
    positivity
  have hAsq : A omega ^ 2 <= B ^ 2 := by
    rw [sq_le_sq]
    simpa [abs_of_nonneg hB] using hAbound omega
  have hAX :
      |A omega * X omega| <= B * |X omega| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hAbound omega) (abs_nonneg (X omega))
  have hqAsq :
      |q * A omega ^ 2| <= q * B ^ 2 := by
    rw [abs_of_nonneg (mul_nonneg hq (sq_nonneg (A omega)))]
    exact mul_le_mul_of_nonneg_left hAsq hq
  have hzabs :
      |A omega * X omega - q * A omega ^ 2| <=
        B * |X omega| + q * B ^ 2 := by
    exact (abs_sub _ _).trans (add_le_add hAX hqAsq)
  have hlog :
      s * (A omega * X omega - q * A omega ^ 2) <=
        C + D * |X omega| := by
    calc
      s * (A omega * X omega - q * A omega ^ 2) <=
          |s * (A omega * X omega - q * A omega ^ 2)| :=
        le_abs_self _
      _ = |s| * |A omega * X omega - q * A omega ^ 2| := by
        rw [abs_mul]
      _ <= |s| * (B * |X omega| + q * B ^ 2) :=
        mul_le_mul_of_nonneg_left hzabs (abs_nonneg s)
      _ = C + D * |X omega| := by
        dsimp [C, D]
        ring
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  convert hlog using 1
  all_goals
    dsimp [q]
    ring

/--
Bounded predictable multipliers satisfy the compensated conditional MGF
contract without a caller-supplied exponential-integrability proof.
-/
theorem HasCondSubgaussianMGF.predictable_mul_compensated_hasCondMGFUpperBoundAt_of_abs_le
    {Omega : Type u} {m mOmega : MeasurableSpace Omega}
    [StandardBorelSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {X A : Omega -> Real} {c : NNReal}
    (hm : m <= mOmega)
    (hX : HasCondSubgaussianMGF m hm X c mu)
    (hA : @Measurable Omega Real m inferInstance A)
    (B : Real) (hB : 0 <= B)
    (hAbound : forall omega, |A omega| <= B) :
    BanditRLProof.Concentration.HasCondMGFUpperBoundAt m hm
      (fun omega =>
        A omega * X omega -
          (((c : NNReal) : Real) * A omega ^ 2 / 2))
      1 0 mu := by
  exact hX.predictable_mul_compensated_hasCondMGFUpperBoundAt hm hA
    (hX.integrable_exp_mul_predictable_mul_compensated_of_abs_le
      hm hA B hB hAbound)

end ProbabilityTheory

namespace BanditRLProof
namespace OFUL

open MeasureTheory ProbabilityTheory Real

open scoped ENNReal NNReal ProbabilityTheory

universe v w

/--
Finite-horizon fixed-direction exponential-supermartingale endpoint for
predictable vector features and conditionally sub-Gaussian scalar noise.

This is the deterministic-horizon local form of Lemma 1 in
Abbasi-Yadkori, Pal, and Szepesvari (2011). It is the input to the Gaussian
mixture step, not yet the vector self-normalized determinant-ratio theorem.
-/
theorem fixedDirectionCompensatedScore_hasMGFUpperBoundAt
    {Omega : Type v} {Feature : Type w}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F : Filtration Nat mOmega)
    (feature : Nat -> Omega -> Feature -> Real)
    (noise : Nat -> Omega -> Real)
    (varianceProxy : Nat -> NNReal)
    (theta : Feature -> Real)
    (projectionBound : Nat -> Real)
    (hprojection : forall i,
      StronglyMeasurable[F i]
        (fun omega => dotProduct theta (feature i omega)))
    (hnoise : StronglyAdapted F (fun t omega =>
      match t with
      | 0 => 0
      | i + 1 => noise i omega))
    (hprojectionBound_nonneg : forall i, 0 <= projectionBound i)
    (hprojectionBound : forall i omega,
      |dotProduct theta (feature i omega)| <= projectionBound i)
    (n : Nat)
    (hsubGaussian : forall i, i < n ->
      HasCondSubgaussianMGF
        (F i) (F.le i) (noise i) (varianceProxy i) mu) :
    Concentration.HasMGFUpperBoundAt
      (fun omega =>
        (Finset.range (n + 1)).sum (fun t =>
          match t with
          | 0 => 0
          | i + 1 =>
              dotProduct theta (feature i omega) * noise i omega -
                (((varianceProxy i : NNReal) : Real) *
                  (dotProduct theta (feature i omega)) ^ 2 / 2)))
      1 0 mu := by
  let Z : Nat -> Omega -> Real := fun t omega =>
    match t with
    | 0 => 0
    | i + 1 =>
        dotProduct theta (feature i omega) * noise i omega -
          (((varianceProxy i : NNReal) : Real) *
            (dotProduct theta (feature i omega)) ^ 2 / 2)
  have hZ : StronglyAdapted F Z := by
    intro t
    cases t with
    | zero =>
        exact stronglyMeasurable_const
    | succ i =>
        have hA :
            StronglyMeasurable[F (i + 1)]
              (fun omega => dotProduct theta (feature i omega)) :=
          (hprojection i).mono (F.mono (Nat.le_succ i))
        have hX :
            StronglyMeasurable[F (i + 1)] (noise i) := by
          simpa using hnoise (i + 1)
        have hprod := hA.measurable.mul hX.measurable
        have hsquare := hA.measurable.pow_const 2
        have hcoeff :
            Measurable[F (i + 1)]
              (fun _ : Omega => (((varianceProxy i : NNReal) : Real))) :=
          measurable_const
        have hcompensator :=
          (hcoeff.mul hsquare).div_const (2 : Real)
        simpa [Z] using (hprod.sub hcompensator).stronglyMeasurable
  have hzero : Concentration.HasMGFUpperBoundAt (Z 0) 1 0 mu := by
    have hzero' :
        Concentration.HasMGFUpperBoundAt
          (fun _ : Omega => (0 : Real)) 1 0 mu := by
      constructor
      · intro s
        simp
      · simp [ProbabilityTheory.mgf]
    simpa [Z] using hzero'
  have hcond : forall i, i < (n + 1) - 1 ->
      Concentration.HasCondMGFUpperBoundAt
        (F i) (F.le i) (Z (i + 1)) 1 0 mu := by
    intro i hi
    have hsg := hsubGaussian i (by omega)
    have h :=
      hsg.predictable_mul_compensated_hasCondMGFUpperBoundAt_of_abs_le
        (F.le i) (hprojection i).measurable
        (projectionBound i) (hprojectionBound_nonneg i)
        (hprojectionBound i)
    simpa [Z] using h
  have hsum :=
    Concentration.HasMGFUpperBoundAt.sum_of_hasCondMGFUpperBoundAt
      (μ := mu) (ℱ := F) (Y := Z) (ψY := fun _ => 0) (t := 1)
      hZ hzero (n + 1) hcond
  simpa [Z] using hsum

end OFUL
end BanditRLProof
