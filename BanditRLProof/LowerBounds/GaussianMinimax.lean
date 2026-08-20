import BanditRLProof.LowerBounds.BanditHistoryKL
import BanditRLProof.LowerBounds.BasicIdeas
import BanditRLProof.LowerBounds.Minimax
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# Finite-armed Gaussian minimax lower bound

This module formalizes the proof of Lattimore--Szepesvari, Theorem 15.2, on
the repository's canonical finite-history law.  The local history index is
inclusive: `lastRound` represents exactly `lastRound + 1` observations.
-/

namespace BanditRLProof
namespace LowerBounds

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

noncomputable section

/-- A realized pull count, converted to `Real` for the source's regret
algebra. -/
noncomputable def finiteHistoryPullCountReal
    {K : Nat} {Reward : Type*}
    (n : Nat) (history : History.FinitePairHistory (Fin K) Reward n)
    (arm : Fin K) : Real :=
  (finiteHistoryPullCountENNReal n history arm).toReal

theorem finiteHistoryPullCountENNReal_ne_top
    {K : Nat} {Reward : Type*}
    (n : Nat) (history : History.FinitePairHistory (Fin K) Reward n)
    (arm : Fin K) :
    finiteHistoryPullCountENNReal n history arm ≠ ∞ := by
  induction n with
  | zero =>
      simp only [finiteHistoryPullCountENNReal]
      split <;> simp
  | succ n ih =>
      simp only [finiteHistoryPullCountENNReal]
      exact ENNReal.add_ne_top.mpr
        ⟨ih (Thompson.pairHistoryPrefix history), by split <;> simp⟩

theorem sum_finiteHistoryPullCountENNReal
    {K : Nat} {Reward : Type*}
    (n : Nat) (history : History.FinitePairHistory (Fin K) Reward n) :
    ∑ arm : Fin K, finiteHistoryPullCountENNReal n history arm = n + 1 := by
  classical
  induction n with
  | zero =>
      simp [finiteHistoryPullCountENNReal]
  | succ n ih =>
      simp only [finiteHistoryPullCountENNReal, Finset.sum_add_distrib, ih]
      have hlast : (Thompson.pairHistoryLast history).1 ∈
          (Finset.univ : Finset (Fin K)) := Finset.mem_univ _
      have hsingle :
          (∑ arm : Fin K,
              if (Thompson.pairHistoryLast history).1 = arm
              then (1 : ENNReal) else 0) = 1 := by
        simp
      rw [hsingle]
      norm_num

@[simp]
theorem sum_finiteHistoryPullCountReal
    {K : Nat} {Reward : Type*}
    (n : Nat) (history : History.FinitePairHistory (Fin K) Reward n) :
    ∑ arm : Fin K, finiteHistoryPullCountReal n history arm = n + 1 := by
  simp only [finiteHistoryPullCountReal]
  rw [← ENNReal.toReal_sum]
  · rw [sum_finiteHistoryPullCountENNReal]
    rw [ENNReal.toReal_add (by simp) (by simp)]
    simp
  · intro arm _harm
    exact finiteHistoryPullCountENNReal_ne_top n history arm

theorem finiteHistoryPullCountReal_nonneg
    {K : Nat} {Reward : Type*}
    (n : Nat) (history : History.FinitePairHistory (Fin K) Reward n)
    (arm : Fin K) :
    0 ≤ finiteHistoryPullCountReal n history arm :=
  ENNReal.toReal_nonneg

theorem measurable_finiteHistoryPullCountReal
    {K : Nat} {Reward : Type*} [MeasurableSpace Reward]
    (n : Nat) (arm : Fin K) :
    Measurable (fun history : History.FinitePairHistory (Fin K) Reward n =>
      finiteHistoryPullCountReal n history arm) :=
  (measurable_finiteHistoryPullCountENNReal n arm).ennreal_toReal

/-- Event integration lower bound in the exact real-probability convention
used by the Bretagnolle--Huber theorem. -/
theorem ofReal_mul_probReal_le_lintegral_of_event
    {alpha : Type*} [MeasurableSpace alpha]
    {mu : Measure alpha} [IsFiniteMeasure mu]
    {A : Set alpha} (hA : MeasurableSet A)
    {c : Real} (hc : 0 ≤ c) {f : alpha -> ENNReal}
    (hf : forall x, x ∈ A -> ENNReal.ofReal c ≤ f x) :
    ENNReal.ofReal (c * mu.real A) ≤ ∫⁻ x, f x ∂mu := by
  rw [ENNReal.ofReal_mul hc, ofReal_measureReal]
  calc
    ENNReal.ofReal c * mu A =
        ∫⁻ x, A.indicator (fun _ => ENNReal.ofReal c) x ∂mu := by
      rw [MeasureTheory.lintegral_indicator hA,
        MeasureTheory.setLIntegral_const]
    _ ≤ ∫⁻ x, f x ∂mu := by
      apply MeasureTheory.lintegral_mono
      intro x
      by_cases hx : x ∈ A
      · simpa [Set.indicator_of_mem hx] using hf x hx
      · simp [Set.indicator, hx]

/-- A rigorous rational lower bound for the testing constant in the source
proof. -/
theorem sixteen_div_twentySeven_le_exp_neg_half :
    (16 / 27 : Real) ≤ Real.exp (-(1 / 2 : Real)) := by
  have hexpOne : Real.exp 1 < (729 / 256 : Real) :=
    Real.exp_one_lt_d9.trans (by norm_num)
  have hpos : 0 < Real.exp (-(1 / 2 : Real)) := Real.exp_pos _
  have hsquare : Real.exp (-(1 / 2 : Real)) ^ 2 = (Real.exp 1)⁻¹ := by
    rw [sq, ← Real.exp_add]
    convert Real.exp_neg 1 using 1
    norm_num
  have hinv : (256 / 729 : Real) < (Real.exp 1)⁻¹ := by
    have h := one_div_lt_one_div_of_lt (by positivity : (0 : Real) < Real.exp 1)
      hexpOne
    norm_num [div_eq_mul_inv] at h ⊢
    exact h
  nlinarith [hsquare]

/-- A unit-cube Gaussian environment together with a certified optimal arm.
The optimal-arm field is proof data; the induced reward kernel depends only on
`mean`. -/
structure UnitGaussianBanditEnvironment (K : Nat) where
  mean : Fin K -> Real
  bestArm : Fin K
  mean_mem_unit : forall arm, mean arm ∈ Set.Icc (0 : Real) 1
  isBest : forall arm, mean arm ≤ mean bestArm

/-- The stationary reward kernel induced by a finite vector of Gaussian
means. -/
noncomputable abbrev unitGaussianKernel {K : Nat} (mean : Fin K -> Real) :
    Kernel (Fin K) Real :=
  Kernel.ofFunOfCountable (unitGaussianBandit mean)

@[simp]
theorem unitGaussianKernel_apply
    {K : Nat} (mean : Fin K -> Real) (arm : Fin K) :
    unitGaussianKernel mean arm = unitGaussianArm (mean arm) := rfl

instance instUnitGaussianKernelIsMarkovKernel
    {K : Nat} (mean : Fin K -> Real) :
    IsMarkovKernel (unitGaussianKernel mean) where
  isProbabilityMeasure arm := by
    change IsProbabilityMeasure (gaussianReal (mean arm) (1 : NNReal))
    infer_instance

/-- Realized pseudo-regret on an inclusive finite history. -/
noncomputable def finiteHistoryGaussianPseudoRegret
    {K : Nat} (environment : UnitGaussianBanditEnvironment K)
    (lastRound : Nat)
    (history : History.FinitePairHistory (Fin K) Real lastRound) : ENNReal :=
  ∑ arm : Fin K,
    ENNReal.ofReal
        (environment.mean environment.bestArm - environment.mean arm) *
      finiteHistoryPullCountENNReal lastRound history arm

/-- Expected pseudo-regret under the canonical history law.  This is the
Lemma 4.5-equivalent gap-times-pull-count form of the source quantity `R_n`,
represented in `ENNReal` to align with Mathlib's measure-KL API.  The separate
reward-sum-regret equality is not asserted by this definition. -/
noncomputable def gaussianExpectedPseudoRegret
    {K : Nat} (algorithm : Thompson.HistoryAlgorithm (Fin K) Real)
    (environment : UnitGaussianBanditEnvironment K)
    (lastRound : Nat) : ENNReal :=
  ∫⁻ history,
    finiteHistoryGaussianPseudoRegret environment lastRound history
    ∂canonicalBanditHistoryMeasure algorithm
      (unitGaussianKernel environment.mean) lastRound

theorem measurable_finiteHistoryGaussianPseudoRegret
    {K : Nat} (environment : UnitGaussianBanditEnvironment K)
    (lastRound : Nat) :
    Measurable (finiteHistoryGaussianPseudoRegret environment lastRound) := by
  classical
  unfold finiteHistoryGaussianPseudoRegret
  exact Finset.measurable_sum Finset.univ fun arm _harm =>
    measurable_const.mul
      (measurable_finiteHistoryPullCountENNReal lastRound arm)

/-- Regrouping expected Gaussian pseudo-regret by arm pulls. -/
theorem gaussianExpectedPseudoRegret_eq_sum_expectedPulls
    {K : Nat} (algorithm : Thompson.HistoryAlgorithm (Fin K) Real)
    (environment : UnitGaussianBanditEnvironment K)
    (lastRound : Nat) :
    gaussianExpectedPseudoRegret algorithm environment lastRound =
      ∑ arm : Fin K,
        ENNReal.ofReal
            (environment.mean environment.bestArm - environment.mean arm) *
          canonicalRealizedExpectedPullCountThrough algorithm
            (unitGaussianKernel environment.mean) lastRound arm := by
  classical
  unfold gaussianExpectedPseudoRegret finiteHistoryGaussianPseudoRegret
  rw [MeasureTheory.lintegral_finset_sum]
  · apply Finset.sum_congr rfl
    intro arm _harm
    rw [MeasureTheory.lintegral_const_mul _
      (measurable_finiteHistoryPullCountENNReal lastRound arm)]
    rfl
  · intro arm _harm
    exact measurable_const.mul
      (measurable_finiteHistoryPullCountENNReal lastRound arm)

/-- Every inclusive history contains exactly `lastRound + 1` pulls, hence so
do the expected realized counts. -/
theorem sum_canonicalRealizedExpectedPullCountThrough
    {K : Nat} (algorithm : Thompson.HistoryAlgorithm (Fin K) Real)
    (mean : Fin K -> Real) (lastRound : Nat) :
    ∑ arm : Fin K,
        canonicalRealizedExpectedPullCountThrough algorithm
          (unitGaussianKernel mean) lastRound arm = lastRound + 1 := by
  classical
  unfold canonicalRealizedExpectedPullCountThrough
  rw [← MeasureTheory.lintegral_finset_sum]
  · simp_rw [sum_finiteHistoryPullCountENNReal]
    simp
  · intro arm _harm
    exact measurable_finiteHistoryPullCountENNReal lastRound arm

/-- Real-valued first-environment expected pull count. -/
noncomputable def gaussianExpectedPullCountReal
    {K : Nat} (algorithm : Thompson.HistoryAlgorithm (Fin K) Real)
    (mean : Fin K -> Real) (lastRound : Nat) (arm : Fin K) : Real :=
  (canonicalRealizedExpectedPullCountThrough algorithm
    (unitGaussianKernel mean) lastRound arm).toReal

theorem gaussianExpectedPullCountReal_nonneg
    {K : Nat} (algorithm : Thompson.HistoryAlgorithm (Fin K) Real)
    (mean : Fin K -> Real) (lastRound : Nat) (arm : Fin K) :
    0 ≤ gaussianExpectedPullCountReal algorithm mean lastRound arm := by
  unfold gaussianExpectedPullCountReal
  exact ENNReal.toReal_nonneg

theorem sum_gaussianExpectedPullCountReal
    {K : Nat} (algorithm : Thompson.HistoryAlgorithm (Fin K) Real)
    (mean : Fin K -> Real) (lastRound : Nat) :
    ∑ arm : Fin K, gaussianExpectedPullCountReal algorithm mean lastRound arm =
      lastRound + 1 := by
  simp only [gaussianExpectedPullCountReal]
  rw [← ENNReal.toReal_sum]
  · rw [sum_canonicalRealizedExpectedPullCountThrough]
    rw [ENNReal.toReal_add (by simp) (by simp)]
    simp
  · intro arm _harm
    have hle : canonicalRealizedExpectedPullCountThrough algorithm
        (unitGaussianKernel mean) lastRound arm ≤ lastRound + 1 := by
      calc
        canonicalRealizedExpectedPullCountThrough algorithm
            (unitGaussianKernel mean) lastRound arm ≤
            ∑ a : Fin K,
              canonicalRealizedExpectedPullCountThrough algorithm
                (unitGaussianKernel mean) lastRound a :=
          Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ arm)
        _ = lastRound + 1 :=
          sum_canonicalRealizedExpectedPullCountThrough algorithm mean lastRound
    exact ne_top_of_le_ne_top (by simp) hle

/-- Base mean vector in the proof of Theorem 15.2: arm zero has mean
`gap`, and every alternative has mean zero. -/
def gaussianMinimaxBaseMean {m : Nat} (gap : Real) : Fin (m + 1) -> Real :=
  fun arm => if arm = 0 then gap else 0

@[simp]
theorem gaussianMinimaxBaseMean_zero {m : Nat} (gap : Real) :
    gaussianMinimaxBaseMean (m := m) gap 0 = gap := by
  simp [gaussianMinimaxBaseMean]

@[simp]
theorem gaussianMinimaxBaseMean_succ {m : Nat} (gap : Real) (i : Fin m) :
    gaussianMinimaxBaseMean (m := m) gap i.succ = 0 := by
  simp [gaussianMinimaxBaseMean, Fin.succ_ne_zero]

/-- Changed mean vector: the selected alternative `i.succ` is raised from
zero to `2*gap`, while arm zero remains at `gap`. -/
def gaussianMinimaxChangedMean {m : Nat} (gap : Real) (i : Fin m) :
    Fin (m + 1) -> Real :=
  fun arm => if arm = i.succ then 2 * gap
    else gaussianMinimaxBaseMean gap arm

@[simp]
theorem gaussianMinimaxChangedMean_selected
    {m : Nat} (gap : Real) (i : Fin m) :
    gaussianMinimaxChangedMean gap i i.succ = 2 * gap := by
  simp [gaussianMinimaxChangedMean]

@[simp]
theorem gaussianMinimaxChangedMean_zero
    {m : Nat} (gap : Real) (i : Fin m) :
    gaussianMinimaxChangedMean gap i 0 = gap := by
  have hne : (0 : Fin (m + 1)) ≠ i.succ := (Fin.succ_ne_zero i).symm
  simp [gaussianMinimaxChangedMean, hne]

@[simp]
theorem gaussianMinimaxChangedMean_other
    {m : Nat} (gap : Real) {i j : Fin m} (hji : j ≠ i) :
    gaussianMinimaxChangedMean gap i j.succ = 0 := by
  simp [gaussianMinimaxChangedMean, Fin.succ_inj, hji]

/-- Certified base environment. -/
noncomputable def gaussianMinimaxBaseEnvironment
    {m : Nat} (gap : Real) (hgap : 0 ≤ gap) (hgap_le : gap ≤ 1 / 2) :
    UnitGaussianBanditEnvironment (m + 1) where
  mean := gaussianMinimaxBaseMean gap
  bestArm := 0
  mean_mem_unit arm := by
    by_cases harm : arm = 0
    · subst arm
      simp only [gaussianMinimaxBaseMean_zero, Set.mem_Icc]
      constructor <;> linarith
    · simp [gaussianMinimaxBaseMean, harm]
  isBest arm := by
    by_cases harm : arm = 0
    · subst arm
      simp
    · simp [gaussianMinimaxBaseMean, harm, hgap]

/-- Certified changed environment with `i.succ` optimal. -/
noncomputable def gaussianMinimaxChangedEnvironment
    {m : Nat} (gap : Real) (i : Fin m)
    (hgap : 0 ≤ gap) (hgap_le : gap ≤ 1 / 2) :
    UnitGaussianBanditEnvironment (m + 1) where
  mean := gaussianMinimaxChangedMean gap i
  bestArm := i.succ
  mean_mem_unit arm := by
    by_cases hselected : arm = i.succ
    · subst arm
      simp only [gaussianMinimaxChangedMean_selected, Set.mem_Icc]
      constructor <;> linarith
    · by_cases hzero : arm = 0
      · subst arm
        simp only [gaussianMinimaxChangedMean_zero, Set.mem_Icc]
        constructor <;> linarith
      · simp [gaussianMinimaxChangedMean, gaussianMinimaxBaseMean,
          hselected, hzero]
  isBest arm := by
    by_cases hselected : arm = i.succ
    · subst arm
      simp
    · by_cases hzero : arm = 0
      · subst arm
        simp only [gaussianMinimaxChangedMean_zero,
          gaussianMinimaxChangedMean_selected]
        linarith
      · simp [gaussianMinimaxChangedMean, gaussianMinimaxBaseMean,
          hselected, hzero, hgap]

theorem finiteHistoryGaussianPseudoRegret_ne_top
    {K : Nat} (environment : UnitGaussianBanditEnvironment K)
    (lastRound : Nat)
    (history : History.FinitePairHistory (Fin K) Real lastRound) :
    finiteHistoryGaussianPseudoRegret environment lastRound history ≠ ∞ := by
  classical
  unfold finiteHistoryGaussianPseudoRegret
  exact ENNReal.sum_ne_top.mpr fun arm _harm =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (finiteHistoryPullCountENNReal_ne_top lastRound history arm)

theorem finiteHistoryGaussianPseudoRegret_toReal
    {K : Nat} (environment : UnitGaussianBanditEnvironment K)
    (lastRound : Nat)
    (history : History.FinitePairHistory (Fin K) Real lastRound) :
    (finiteHistoryGaussianPseudoRegret environment lastRound history).toReal =
      ∑ arm : Fin K,
        (environment.mean environment.bestArm - environment.mean arm) *
          finiteHistoryPullCountReal lastRound history arm := by
  classical
  unfold finiteHistoryGaussianPseudoRegret
  rw [ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro arm _harm
    rw [ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (sub_nonneg.mpr (environment.isBest arm))]
    rfl
  · intro arm _harm
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (finiteHistoryPullCountENNReal_ne_top lastRound history arm)

/-- The source event `A={T_0(n) <= n/2}`, in the repository's inclusive
history convention. -/
def gaussianMinimaxBaseSmallPullEvent
    {m : Nat} (lastRound : Nat) :
    Set (History.FinitePairHistory (Fin (m + 1)) Real lastRound) :=
  {history | 2 * finiteHistoryPullCountReal lastRound history 0 ≤
    (lastRound + 1 : Nat)}

theorem measurableSet_gaussianMinimaxBaseSmallPullEvent
    {m : Nat} (lastRound : Nat) :
    MeasurableSet (gaussianMinimaxBaseSmallPullEvent (m := m) lastRound) := by
  exact measurableSet_le
    (measurable_const.mul
      (measurable_finiteHistoryPullCountReal lastRound 0))
    measurable_const

theorem finiteHistoryGaussianPseudoRegret_base_toReal
    {m : Nat} (gap : Real) (hgap : 0 ≤ gap) (hgap_le : gap ≤ 1 / 2)
    (lastRound : Nat)
    (history : History.FinitePairHistory (Fin (m + 1)) Real lastRound) :
    (finiteHistoryGaussianPseudoRegret
        (gaussianMinimaxBaseEnvironment gap hgap hgap_le)
        lastRound history).toReal =
      gap * ((lastRound + 1 : Nat) -
        finiteHistoryPullCountReal lastRound history 0) := by
  rw [finiteHistoryGaussianPseudoRegret_toReal]
  simp only [gaussianMinimaxBaseEnvironment,
    gaussianMinimaxBaseMean_zero, gaussianMinimaxBaseMean_succ,
    sub_self, zero_mul, Fin.sum_univ_succ, sub_zero]
  have htotal := sum_finiteHistoryPullCountReal lastRound history
  rw [Fin.sum_univ_succ] at htotal
  rw [← Finset.mul_sum]
  have hsum :
      (∑ i : Fin m,
        finiteHistoryPullCountReal lastRound history i.succ) =
      ((lastRound + 1 : Nat) : Real) -
        finiteHistoryPullCountReal lastRound history 0 := by
    norm_num [Nat.cast_add, Nat.cast_one] at htotal ⊢
    linarith
  rw [hsum]
  ring

theorem finiteHistoryGaussianPseudoRegret_changed_toReal_lower
    {m : Nat} (gap : Real) (i : Fin m)
    (hgap : 0 ≤ gap) (hgap_le : gap ≤ 1 / 2)
    (lastRound : Nat)
    (history : History.FinitePairHistory (Fin (m + 1)) Real lastRound) :
    gap * finiteHistoryPullCountReal lastRound history 0 ≤
      (finiteHistoryGaussianPseudoRegret
        (gaussianMinimaxChangedEnvironment gap i hgap hgap_le)
        lastRound history).toReal := by
  rw [finiteHistoryGaussianPseudoRegret_toReal]
  have hterm := Finset.single_le_sum
    (s := (Finset.univ : Finset (Fin (m + 1))))
    (f := fun arm =>
      (gaussianMinimaxChangedMean gap i i.succ -
          gaussianMinimaxChangedMean gap i arm) *
        finiteHistoryPullCountReal lastRound history arm)
    (fun arm _harm => mul_nonneg
      (sub_nonneg.mpr
        ((gaussianMinimaxChangedEnvironment gap i hgap hgap_le).isBest arm))
      (finiteHistoryPullCountReal_nonneg lastRound history arm))
    (Finset.mem_univ (0 : Fin (m + 1)))
  have hgapid : 2 * gap - gap = gap := by ring
  simpa only [gaussianMinimaxChangedEnvironment,
    gaussianMinimaxChangedMean_selected, gaussianMinimaxChangedMean_zero,
    hgapid] using hterm

theorem base_event_forces_gaussianPseudoRegret
    {m : Nat} (gap : Real) (hgap : 0 ≤ gap) (hgap_le : gap ≤ 1 / 2)
    (lastRound : Nat)
    (history : History.FinitePairHistory (Fin (m + 1)) Real lastRound)
    (hA : history ∈ gaussianMinimaxBaseSmallPullEvent (m := m) lastRound) :
    ENNReal.ofReal (((lastRound + 1 : Nat) : Real) * gap / 2) ≤
      finiteHistoryGaussianPseudoRegret
        (gaussianMinimaxBaseEnvironment gap hgap hgap_le)
        lastRound history := by
  apply (ENNReal.ofReal_le_iff_le_toReal
    (finiteHistoryGaussianPseudoRegret_ne_top _ _ _)).mpr
  rw [finiteHistoryGaussianPseudoRegret_base_toReal]
  change 2 * finiteHistoryPullCountReal lastRound history 0 ≤
    ((lastRound + 1 : Nat) : Real) at hA
  nlinarith

theorem changed_complement_forces_gaussianPseudoRegret
    {m : Nat} (gap : Real) (i : Fin m)
    (hgap : 0 ≤ gap) (hgap_le : gap ≤ 1 / 2)
    (lastRound : Nat)
    (history : History.FinitePairHistory (Fin (m + 1)) Real lastRound)
    (hAc : history ∈
      (gaussianMinimaxBaseSmallPullEvent (m := m) lastRound)ᶜ) :
    ENNReal.ofReal (((lastRound + 1 : Nat) : Real) * gap / 2) ≤
      finiteHistoryGaussianPseudoRegret
        (gaussianMinimaxChangedEnvironment gap i hgap hgap_le)
        lastRound history := by
  apply (ENNReal.ofReal_le_iff_le_toReal
    (finiteHistoryGaussianPseudoRegret_ne_top _ _ _)).mpr
  refine le_trans ?_ (finiteHistoryGaussianPseudoRegret_changed_toReal_lower
    gap i hgap hgap_le lastRound history)
  have hnot : ¬ 2 * finiteHistoryPullCountReal lastRound history 0 ≤
      ((lastRound + 1 : Nat) : Real) := by
    simpa [gaussianMinimaxBaseSmallPullEvent] using hAc
  nlinarith

theorem base_event_probability_lower_bound
    {m : Nat} (algorithm : Thompson.HistoryAlgorithm (Fin (m + 1)) Real)
    (gap : Real) (hgap : 0 ≤ gap) (hgap_le : gap ≤ 1 / 2)
    (lastRound : Nat) :
    ENNReal.ofReal
        ((((lastRound + 1 : Nat) : Real) * gap / 2) *
          (canonicalBanditHistoryMeasure algorithm
            (unitGaussianKernel (gaussianMinimaxBaseMean gap)) lastRound).real
              (gaussianMinimaxBaseSmallPullEvent (m := m) lastRound)) ≤
      gaussianExpectedPseudoRegret algorithm
        (gaussianMinimaxBaseEnvironment gap hgap hgap_le) lastRound := by
  unfold gaussianExpectedPseudoRegret
  exact ofReal_mul_probReal_le_lintegral_of_event
    (measurableSet_gaussianMinimaxBaseSmallPullEvent lastRound)
    (by positivity)
    (base_event_forces_gaussianPseudoRegret gap hgap hgap_le lastRound)

theorem changed_complement_probability_lower_bound
    {m : Nat} (algorithm : Thompson.HistoryAlgorithm (Fin (m + 1)) Real)
    (gap : Real) (i : Fin m)
    (hgap : 0 ≤ gap) (hgap_le : gap ≤ 1 / 2)
    (lastRound : Nat) :
    ENNReal.ofReal
        ((((lastRound + 1 : Nat) : Real) * gap / 2) *
          (canonicalBanditHistoryMeasure algorithm
            (unitGaussianKernel (gaussianMinimaxChangedMean gap i))
              lastRound).real
            (gaussianMinimaxBaseSmallPullEvent (m := m) lastRound)ᶜ) ≤
      gaussianExpectedPseudoRegret algorithm
        (gaussianMinimaxChangedEnvironment gap i hgap hgap_le) lastRound := by
  unfold gaussianExpectedPseudoRegret
  exact ofReal_mul_probReal_le_lintegral_of_event
    (measurableSet_gaussianMinimaxBaseSmallPullEvent lastRound).compl
    (by positivity)
    (changed_complement_forces_gaussianPseudoRegret gap i hgap hgap_le lastRound)

theorem klDiv_unitGaussianKernel_base_changed
    {m : Nat} (gap : Real) (i j : Fin m) :
    InformationTheory.klDiv
        (unitGaussianKernel (gaussianMinimaxBaseMean gap) j.succ)
        (unitGaussianKernel (gaussianMinimaxChangedMean gap i) j.succ) =
      if j = i then ENNReal.ofReal (2 * gap ^ 2) else 0 := by
  by_cases hji : j = i
  · subst j
    simp only [unitGaussianKernel_apply, gaussianMinimaxBaseMean_succ,
      gaussianMinimaxChangedMean_selected, if_pos]
    exact klDiv_unitGaussianArm_zero_two_mul gap
  · simp only [unitGaussianKernel_apply]
    rw [if_neg hji, gaussianMinimaxBaseMean_succ,
      gaussianMinimaxChangedMean_other gap hji]
    exact InformationTheory.klDiv_self _

/-- Lemma 15.1 specialized to the source's base/changed Gaussian pair: only
the selected alternative contributes to the directed history KL. -/
theorem klDiv_gaussianMinimax_base_changed_history
    {m : Nat} (algorithm : Thompson.HistoryAlgorithm (Fin (m + 1)) Real)
    (gap : Real) (i : Fin m) (lastRound : Nat) :
    InformationTheory.klDiv
        (canonicalBanditHistoryMeasure algorithm
          (unitGaussianKernel (gaussianMinimaxBaseMean gap)) lastRound)
        (canonicalBanditHistoryMeasure algorithm
          (unitGaussianKernel (gaussianMinimaxChangedMean gap i)) lastRound) =
      canonicalRealizedExpectedPullCountThrough algorithm
          (unitGaussianKernel (gaussianMinimaxBaseMean gap)) lastRound i.succ *
        ENNReal.ofReal (2 * gap ^ 2) := by
  rw [banditHistoryRelativeEntropy_eq_expectedPulls_sum]
  rw [Fin.sum_univ_succ]
  have hzero : InformationTheory.klDiv
      (unitGaussianKernel (gaussianMinimaxBaseMean (m := m) gap) 0)
      (unitGaussianKernel (gaussianMinimaxChangedMean gap i) 0) = 0 := by
    simp only [unitGaussianKernel_apply, gaussianMinimaxBaseMean_zero,
      gaussianMinimaxChangedMean_zero]
    exact InformationTheory.klDiv_self _
  rw [hzero, mul_zero, zero_add]
  simp_rw [klDiv_unitGaussianKernel_base_changed gap i]
  simp only [mul_ite, mul_zero]
  simp

/-- Least-explored alternative under the actual base Gaussian history law. -/
theorem exists_gaussianMinimax_leastExploredAlternative
    {m : Nat} (hm : 0 < m)
    (algorithm : Thompson.HistoryAlgorithm (Fin (m + 1)) Real)
    (gap : Real) (lastRound : Nat) :
    ∃ i : Fin m,
      gaussianExpectedPullCountReal algorithm
          (gaussianMinimaxBaseMean gap) lastRound i.succ ≤
        ((lastRound + 1 : Nat) : Real) / (m : Real) := by
  apply exists_leastExploredAlternative hm
    (fun arm => gaussianExpectedPullCountReal algorithm
      (gaussianMinimaxBaseMean gap) lastRound arm)
    (lastRound + 1)
  · exact gaussianExpectedPullCountReal_nonneg algorithm
      (gaussianMinimaxBaseMean gap) lastRound
  · simpa [Nat.cast_add, Nat.cast_one] using
      (sum_gaussianExpectedPullCountReal algorithm
        (gaussianMinimaxBaseMean gap) lastRound)

/-- The source gap choice makes the selected base-to-changed history KL at
most `1/2`. -/
theorem exists_gaussianMinimax_historyKL_le_half
    {m horizon : Nat} (hm : 0 < m) (hmhorizon : m ≤ horizon)
    (algorithm : Thompson.HistoryAlgorithm (Fin (m + 1)) Real) :
    let gap := gaussianMinimaxGap (m : Real) (horizon : Real)
    ∃ i : Fin m,
      InformationTheory.klDiv
          (canonicalBanditHistoryMeasure algorithm
            (unitGaussianKernel (gaussianMinimaxBaseMean gap)) (horizon - 1))
          (canonicalBanditHistoryMeasure algorithm
            (unitGaussianKernel (gaussianMinimaxChangedMean gap i))
              (horizon - 1)) ≤
        ENNReal.ofReal (1 / 2 : Real) := by
  dsimp only
  have hhorizon : 0 < horizon := lt_of_lt_of_le hm hmhorizon
  have hround : horizon - 1 + 1 = horizon :=
    Nat.sub_add_cancel hhorizon
  obtain ⟨i, hi⟩ := exists_gaussianMinimax_leastExploredAlternative hm algorithm
    (gaussianMinimaxGap (m : Real) (horizon : Real)) (horizon - 1)
  rw [hround] at hi
  refine ⟨i, ?_⟩
  rw [klDiv_gaussianMinimax_base_changed_history]
  let count : ENNReal := canonicalRealizedExpectedPullCountThrough algorithm
    (unitGaussianKernel
      (gaussianMinimaxBaseMean
        (gaussianMinimaxGap (m : Real) (horizon : Real))))
    (horizon - 1) i.succ
  have hcount_le : count ≤ horizon := by
    calc
      count ≤ ∑ arm : Fin (m + 1),
          canonicalRealizedExpectedPullCountThrough algorithm
            (unitGaussianKernel
              (gaussianMinimaxBaseMean
                (gaussianMinimaxGap (m : Real) (horizon : Real))))
            (horizon - 1) arm :=
        by
          change canonicalRealizedExpectedPullCountThrough algorithm
              (unitGaussianKernel
                (gaussianMinimaxBaseMean
                  (gaussianMinimaxGap (m : Real) (horizon : Real))))
              (horizon - 1) i.succ ≤ _
          exact Finset.single_le_sum (fun _ _ => bot_le)
            (Finset.mem_univ i.succ)
      _ = horizon := by
        rw [sum_canonicalRealizedExpectedPullCountThrough]
        exact_mod_cast hround
  have hcount_ne : count ≠ ∞ := ne_top_of_le_ne_top (by simp) hcount_le
  have hcount_real : count.toReal =
      gaussianExpectedPullCountReal algorithm
        (gaussianMinimaxBaseMean
          (gaussianMinimaxGap (m : Real) (horizon : Real)))
        (horizon - 1) i.succ := rfl
  have hgap_sq := gaussianMinimaxGap_sq
    (show (0 : Real) ≤ (m : Real) by positivity)
    (show (0 : Real) ≤ (horizon : Real) by positivity)
  have hexponent := gaussianMinimaxGap_informationExponent_eq_half
    (show (0 : Real) < (m : Real) by positivity)
    (show (0 : Real) < (horizon : Real) by positivity)
  calc
    count * ENNReal.ofReal
        (2 * gaussianMinimaxGap (m : Real) (horizon : Real) ^ 2) =
        ENNReal.ofReal count.toReal * ENNReal.ofReal
          (2 * gaussianMinimaxGap (m : Real) (horizon : Real) ^ 2) := by
      rw [ENNReal.ofReal_toReal hcount_ne]
    _ = ENNReal.ofReal
        (count.toReal *
          (2 * gaussianMinimaxGap (m : Real) (horizon : Real) ^ 2)) := by
      rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg]
    _ ≤ ENNReal.ofReal
        (((horizon : Real) / (m : Real)) *
          (2 * gaussianMinimaxGap (m : Real) (horizon : Real) ^ 2)) := by
      apply ENNReal.ofReal_le_ofReal
      rw [hcount_real]
      exact mul_le_mul_of_nonneg_right hi (by positivity)
    _ = ENNReal.ofReal (1 / 2 : Real) := by
      congr 1
      calc
        ((horizon : Real) / (m : Real)) *
            (2 * gaussianMinimaxGap (m : Real) (horizon : Real) ^ 2) =
            2 * (horizon : Real) *
              gaussianMinimaxGap (m : Real) (horizon : Real) ^ 2 /
                (m : Real) := by ring
        _ = 1 / 2 := hexponent

theorem horizon_mul_gaussianMinimaxGap_eq_half_sqrt
    {alternativeCount horizon : Real}
    (halternatives : 0 ≤ alternativeCount) (hhorizon : 0 < horizon) :
    horizon * gaussianMinimaxGap alternativeCount horizon =
      Real.sqrt (alternativeCount * horizon) / 2 := by
  have hgap_nonneg :
      0 ≤ gaussianMinimaxGap alternativeCount horizon := by
    unfold gaussianMinimaxGap
    positivity
  have hsqrt_nonneg : 0 ≤ Real.sqrt (alternativeCount * horizon) :=
    Real.sqrt_nonneg _
  have hgap_sq := gaussianMinimaxGap_sq halternatives hhorizon.le
  have hsqrt_sq : Real.sqrt (alternativeCount * horizon) ^ 2 =
      alternativeCount * horizon := by
    rw [Real.sq_sqrt]
    positivity
  have hsquares :
      (horizon * gaussianMinimaxGap alternativeCount horizon) ^ 2 =
        (Real.sqrt (alternativeCount * horizon) / 2) ^ 2 := by
    calc
      (horizon * gaussianMinimaxGap alternativeCount horizon) ^ 2 =
          horizon ^ 2 * (alternativeCount / (4 * horizon)) := by
        rw [mul_pow, hgap_sq]
      _ = alternativeCount * horizon / 4 := by
        field_simp
      _ = (Real.sqrt (alternativeCount * horizon) / 2) ^ 2 := by
        rw [div_pow, hsqrt_sq]
        ring
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsquares with heq | heq
  · exact heq
  · nlinarith

/-- Quantitative two-environment conclusion in the exact source constant.
For every policy, one of the source's base/changed unit-Gaussian bandits has
expected pseudo-regret at least `sqrt(m*n)/27`. -/
theorem exists_unitGaussianBandit_expectedPseudoRegret_ge_sqrt_div_twentySeven
    {m horizon : Nat} (hm : 0 < m) (hmhorizon : m ≤ horizon)
    (algorithm : Thompson.HistoryAlgorithm (Fin (m + 1)) Real) :
    let gap := gaussianMinimaxGap (m : Real) (horizon : Real)
    ∃ i : Fin m,
      ENNReal.ofReal
          ((1 / 27 : Real) * Real.sqrt ((m : Real) * (horizon : Real))) ≤
        max
          (gaussianExpectedPseudoRegret algorithm
            (gaussianMinimaxBaseEnvironment gap
              (show 0 ≤ gaussianMinimaxGap (m : Real) (horizon : Real) from
                Real.sqrt_nonneg _)
              (gaussianMinimaxGap_le_half
                (show (0 : Real) < (horizon : Real) by
                  exact_mod_cast lt_of_lt_of_le hm hmhorizon)
                (by exact_mod_cast hmhorizon)))
            (horizon - 1))
          (gaussianExpectedPseudoRegret algorithm
            (gaussianMinimaxChangedEnvironment gap i
              (show 0 ≤ gaussianMinimaxGap (m : Real) (horizon : Real) from
                Real.sqrt_nonneg _)
              (gaussianMinimaxGap_le_half
                (show (0 : Real) < (horizon : Real) by
                  exact_mod_cast lt_of_lt_of_le hm hmhorizon)
                (by exact_mod_cast hmhorizon)))
            (horizon - 1)) := by
  dsimp only
  have hhorizon : 0 < horizon := lt_of_lt_of_le hm hmhorizon
  have hround : horizon - 1 + 1 = horizon := Nat.sub_add_cancel hhorizon
  let gap := gaussianMinimaxGap (m : Real) (horizon : Real)
  have hgap : 0 ≤ gap := by
    dsimp [gap, gaussianMinimaxGap]
    positivity
  have hgap_le : gap ≤ 1 / 2 := by
    exact gaussianMinimaxGap_le_half
      (show (0 : Real) < (horizon : Real) by positivity)
      (by exact_mod_cast hmhorizon)
  obtain ⟨i, hKL⟩ :=
    exists_gaussianMinimax_historyKL_le_half hm hmhorizon algorithm
  refine ⟨i, ?_⟩
  let P := canonicalBanditHistoryMeasure algorithm
    (unitGaussianKernel (gaussianMinimaxBaseMean gap)) (horizon - 1)
  let Q := canonicalBanditHistoryMeasure algorithm
    (unitGaussianKernel (gaussianMinimaxChangedMean gap i)) (horizon - 1)
  let A := gaussianMinimaxBaseSmallPullEvent (m := m) (horizon - 1)
  let c : Real := (horizon : Real) * gap / 2
  have hA : MeasurableSet A :=
    measurableSet_gaussianMinimaxBaseSmallPullEvent (horizon - 1)
  have hBH := bretagnolleHuber (P := P) (Q := Q) hA
  have hscaleToKL := bretagnolleHuberScale_antitone hKL
  have hprobSum :
      bretagnolleHuberScale (ENNReal.ofReal (1 / 2 : Real)) ≤
        P.real A + Q.real Aᶜ := hscaleToKL.trans hBH
  have hscale :
      (1 / 4 : Real) * Real.exp (-(1 / 2 : Real)) ≤
        max (P.real A) (Q.real Aᶜ) := by
    have hscale_eval :
        bretagnolleHuberScale (ENNReal.ofReal (1 / 2 : Real)) =
          (1 / 2 : Real) * Real.exp (-(1 / 2 : Real)) := by
      simp [bretagnolleHuberScale]
    rw [hscale_eval] at hprobSum
    have hp := le_max_left (P.real A) (Q.real Aᶜ)
    have hq := le_max_right (P.real A) (Q.real Aᶜ)
    nlinarith
  have hbase := base_event_probability_lower_bound algorithm gap hgap hgap_le
    (horizon - 1)
  have hchanged := changed_complement_probability_lower_bound algorithm gap i
    hgap hgap_le (horizon - 1)
  rw [hround] at hbase hchanged
  change ENNReal.ofReal (c * P.real A) ≤
      gaussianExpectedPseudoRegret algorithm
        (gaussianMinimaxBaseEnvironment gap hgap hgap_le) (horizon - 1) at hbase
  change ENNReal.ofReal (c * Q.real Aᶜ) ≤
      gaussianExpectedPseudoRegret algorithm
        (gaussianMinimaxChangedEnvironment gap i hgap hgap_le)
          (horizon - 1) at hchanged
  have hprobMaxRegret :
      ENNReal.ofReal (c * max (P.real A) (Q.real Aᶜ)) ≤
        max
          (gaussianExpectedPseudoRegret algorithm
            (gaussianMinimaxBaseEnvironment gap hgap hgap_le) (horizon - 1))
          (gaussianExpectedPseudoRegret algorithm
            (gaussianMinimaxChangedEnvironment gap i hgap hgap_le)
              (horizon - 1)) := by
    by_cases hpq : P.real A ≤ Q.real Aᶜ
    · rw [max_eq_right hpq]
      exact hchanged.trans (le_max_right _ _)
    · rw [max_eq_left (le_of_not_ge hpq)]
      exact hbase.trans (le_max_left _ _)
  refine le_trans ?_ hprobMaxRegret
  apply ENNReal.ofReal_le_ofReal
  have hgap_identity := horizon_mul_gaussianMinimaxGap_eq_half_sqrt
    (show (0 : Real) ≤ (m : Real) by positivity)
    (show (0 : Real) < (horizon : Real) by positivity)
  have hexp := sixteen_div_twentySeven_le_exp_neg_half
  have hsqrt : 0 ≤ Real.sqrt ((m : Real) * (horizon : Real)) :=
    Real.sqrt_nonneg _
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hscaled := mul_le_mul_of_nonneg_left hscale hc
  dsimp [c, gap] at hscaled hgap_identity
  have hexpScaled := mul_le_mul_of_nonneg_left hexp
    (div_nonneg hsqrt (by norm_num : (0 : Real) ≤ 16))
  have hlower :
      (1 / 27 : Real) * Real.sqrt ((m : Real) * (horizon : Real)) ≤
        ((horizon : Real) *
            gaussianMinimaxGap (m : Real) (horizon : Real) / 2) *
          ((1 / 4 : Real) * Real.exp (-(1 / 2 : Real))) := by
    calc
      (1 / 27 : Real) * Real.sqrt ((m : Real) * (horizon : Real)) =
          (Real.sqrt ((m : Real) * (horizon : Real)) / 16) *
            (16 / 27 : Real) := by ring
      _ ≤ (Real.sqrt ((m : Real) * (horizon : Real)) / 16) *
          Real.exp (-(1 / 2 : Real)) := hexpScaled
      _ = ((horizon : Real) *
            gaussianMinimaxGap (m : Real) (horizon : Real) / 2) *
          ((1 / 4 : Real) * Real.exp (-(1 / 2 : Real))) := by
        rw [hgap_identity]
        ring
  dsimp [c, gap]
  exact hlower.trans hscaled

/-- Source-facing existence form of Theorem 15.2 with `m=k-1`.  The returned
environment records both the unit-cube mean vector and a genuinely optimal
arm; its reward law is the corresponding unit-variance Gaussian bandit. -/
theorem exists_unitGaussianBanditEnvironment_expectedPseudoRegret_ge
    {m horizon : Nat} (hm : 0 < m) (hmhorizon : m ≤ horizon)
    (algorithm : Thompson.HistoryAlgorithm (Fin (m + 1)) Real) :
    ∃ environment : UnitGaussianBanditEnvironment (m + 1),
      ENNReal.ofReal
          ((1 / 27 : Real) * Real.sqrt ((m : Real) * (horizon : Real))) ≤
        gaussianExpectedPseudoRegret algorithm environment (horizon - 1) := by
  let gap := gaussianMinimaxGap (m : Real) (horizon : Real)
  have hgap : 0 ≤ gap := by
    dsimp [gap, gaussianMinimaxGap]
    positivity
  have hgap_le : gap ≤ 1 / 2 := by
    exact gaussianMinimaxGap_le_half
      (show (0 : Real) < (horizon : Real) by
        exact_mod_cast lt_of_lt_of_le hm hmhorizon)
      (by exact_mod_cast hmhorizon)
  obtain ⟨i, hi⟩ :=
    exists_unitGaussianBandit_expectedPseudoRegret_ge_sqrt_div_twentySeven
      hm hmhorizon algorithm
  rcases le_max_iff.mp hi with hbase | hchanged
  · exact ⟨gaussianMinimaxBaseEnvironment gap hgap hgap_le, hbase⟩
  · exact ⟨gaussianMinimaxChangedEnvironment gap i hgap hgap_le, hchanged⟩

/-- **Lattimore--Szepesvari, Theorem 15.2.**  For `k>1`, `n≥k-1`, and
every possibly randomized nonanticipating policy, there exists a mean vector
in `[0,1]^k` for which the unit-variance Gaussian bandit has expected
pseudo-regret at least `sqrt((k-1)n)/27`.

The local history parameter is `n-1`, hence contains exactly `n` observations.
-/
theorem finiteArmedGaussianMinimaxLowerBound
    {k horizon : Nat} (hk : 1 < k) (hkhorizon : k - 1 ≤ horizon)
    (algorithm : Thompson.HistoryAlgorithm (Fin k) Real) :
    ∃ environment : UnitGaussianBanditEnvironment k,
      ENNReal.ofReal
          ((1 / 27 : Real) *
            Real.sqrt (((k - 1 : Nat) : Real) * (horizon : Real))) ≤
        gaussianExpectedPseudoRegret algorithm environment (horizon - 1) := by
  cases k with
  | zero => omega
  | succ m =>
      have hm : 0 < m := by omega
      simpa using
        (exists_unitGaussianBanditEnvironment_expectedPseudoRegret_ge
          (m := m) (horizon := horizon) hm (by simpa using hkhorizon) algorithm)

/-- Worst-case expected pseudo-regret over all unit-cube, unit-variance
Gaussian environments. -/
noncomputable def unitGaussianWorstCaseExpectedPseudoRegret
    (K : Nat) (algorithm : Thompson.HistoryAlgorithm (Fin K) Real)
    (lastRound : Nat) : ENNReal :=
  ⨆ environment : UnitGaussianBanditEnvironment K,
    gaussianExpectedPseudoRegret algorithm environment lastRound

/-- Minimax expected pseudo-regret over stochastic finite-history policies. -/
noncomputable def unitGaussianMinimaxExpectedPseudoRegret
    (K lastRound : Nat) : ENNReal :=
  ⨅ algorithm : Thompson.HistoryAlgorithm (Fin K) Real,
    unitGaussianWorstCaseExpectedPseudoRegret K algorithm lastRound

theorem unitGaussianWorstCaseExpectedPseudoRegret_ge
    {k horizon : Nat} (hk : 1 < k) (hkhorizon : k - 1 ≤ horizon)
    (algorithm : Thompson.HistoryAlgorithm (Fin k) Real) :
    ENNReal.ofReal
        ((1 / 27 : Real) *
          Real.sqrt (((k - 1 : Nat) : Real) * (horizon : Real))) ≤
      unitGaussianWorstCaseExpectedPseudoRegret k algorithm (horizon - 1) := by
  obtain ⟨environment, henvironment⟩ :=
    finiteArmedGaussianMinimaxLowerBound hk hkhorizon algorithm
  exact henvironment.trans
    (le_iSup (fun environment : UnitGaussianBanditEnvironment k =>
      gaussianExpectedPseudoRegret algorithm environment (horizon - 1))
      environment)

/-- Minimax form of Theorem 15.2. -/
theorem unitGaussianMinimaxExpectedPseudoRegret_ge
    {k horizon : Nat} (hk : 1 < k) (hkhorizon : k - 1 ≤ horizon) :
    ENNReal.ofReal
        ((1 / 27 : Real) *
          Real.sqrt (((k - 1 : Nat) : Real) * (horizon : Real))) ≤
      unitGaussianMinimaxExpectedPseudoRegret k (horizon - 1) := by
  unfold unitGaussianMinimaxExpectedPseudoRegret
  refine le_iInf fun algorithm => ?_
  exact unitGaussianWorstCaseExpectedPseudoRegret_ge hk hkhorizon algorithm

/-- Chapter 13's coarser `c*sqrt(k*n)` statement, now discharged from the
exact Chapter 15 constant.  The explicit universal choice here is `c=1/54`;
the source only asks for existence of a positive universal constant. -/
theorem unitGaussianMinimaxExpectedPseudoRegret_ge_one_div_fiftyFour_sqrt
    {k horizon : Nat} (hk : 1 < k) (hkhorizon : k ≤ horizon) :
    ENNReal.ofReal
        ((1 / 54 : Real) * Real.sqrt ((k : Real) * (horizon : Real))) ≤
      unitGaussianMinimaxExpectedPseudoRegret k (horizon - 1) := by
  have h15 := unitGaussianMinimaxExpectedPseudoRegret_ge hk
    (le_trans (Nat.sub_le k 1) hkhorizon)
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) h15
  have hkfour : (k : Real) ≤ 4 * ((k - 1 : Nat) : Real) := by
    exact_mod_cast (show k ≤ 4 * (k - 1) by omega)
  have hmul : (k : Real) * (horizon : Real) ≤
      4 * (((k - 1 : Nat) : Real) * (horizon : Real)) := by
    nlinarith [show (0 : Real) ≤ (horizon : Real) by positivity]
  have hsqrt := Real.sqrt_le_sqrt hmul
  have hsqrtFour :
      Real.sqrt (4 * (((k - 1 : Nat) : Real) * (horizon : Real))) =
        2 * Real.sqrt (((k - 1 : Nat) : Real) * (horizon : Real)) := by
    rw [Real.sqrt_mul (by norm_num : (0 : Real) ≤ 4)]
    norm_num
  rw [hsqrtFour] at hsqrt
  nlinarith

end

end LowerBounds
end BanditRLProof
