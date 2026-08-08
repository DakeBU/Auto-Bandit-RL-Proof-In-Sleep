import BanditRLProof.RL.FiniteHorizonNaturalCausalInverseSqrtThresholdUnboundedHittingAfterAEFiniteEventualImmediateStoppingAndInMeasureConsistency
import BanditRLProof.RL.FiniteHorizonNaturalCausalRealizedBehaviorRegretHighProbabilityExplicitSchedule
import BanditRLProof.RL.FiniteHorizonNaturalCausalGrowingWindowGridStoppingTimeL1AverageRealizedBehaviorRegretConsistency
import BanditRLProof.OFULScheduledUnboundedStoppingTimeExpectedRegret
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# First moment of the uncapped inverse-sqrt hitting time

This module upgrades each fixed-index genuine `hittingAfter` first passage
from almost-sure finiteness to first-moment integrability.  The proof uses the
compiled fourth-power burn-in checkpoints.  A cubic block-width envelope is
summable against both the infinite model-tail budget and the exponentially
small return share.  Once the deterministic checkpoint regret rate lies below
the fixed positive threshold, delayed checkpoints are contained in the
compiled violation events.

This is a first-moment result.  It does not prove a second moment, uniform
integrability of stopped rewards, L1 convergence of the stopped process, or an
optional-stopping identity.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal ProbabilityTheory Topology

namespace BanditRLProof.FiniteHorizonRL

universe u v

variable {State : Type u} {Action : Type v}
    [MeasurableSpace State] [MeasurableSpace Action]
    [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action]

namespace AdaptiveStochasticSampledEmpiricalOptimisticSource

/-- Cubic envelope for the width of one consecutive fourth-power checkpoint block. -/
def explicitHighProbabilityQuarticBlockWeight (n : Nat) : Nat :=
  4 * (n + 2) ^ 3

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- A consecutive fourth-power checkpoint gap is bounded by the cubic block weight. -/
theorem explicitHighProbabilityRounds_succ_sub_le_quarticBlockWeight
    (n : Nat) :
    explicitHighProbabilityRounds (n + 1) - explicitHighProbabilityRounds n <=
      explicitHighProbabilityQuarticBlockWeight n := by
  unfold explicitHighProbabilityRounds explicitHighProbabilityScale
    explicitHighProbabilityQuarticBlockWeight
  have hmono : (n + 1) ^ 4 <= (n + 2) ^ 4 :=
    Nat.pow_le_pow_left (by omega) 4
  rw [Nat.sub_le_iff_le_add]
  nlinarith [sq_nonneg ((n : Int) + 1), sq_nonneg ((n : Int) + 2)]

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- Positive horizon makes every local confidence share no larger than a shifted inverse sixth power. -/
theorem selfConsistentScheduledLocalDelta_le_inv_pow_six
    (mdp : MDP State Action) (hhorizon : 0 < mdp.horizon) (t : Nat) :
    AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledLocalDelta mdp t <=
      1 / (((t + 2 : Nat) : Real) ^ 6) := by
  rw [selfConsistentScheduledLocalDelta_eq_inv_pow mdp t]
  exact one_div_pow_le_one_div_pow_of_le
    (by exact_mod_cast (show 1 <= t + 2 by omega) :
      (1 : Real) <= ((t + 2 : Nat) : Real))
    (by omega : 6 <= mdp.horizon + 5)

/-- Shifted inverse-cube envelope used after the cubic block width cancels three powers. -/
noncomputable def quarticBlockShiftedInverseCubePairEnvelope
    (p : Nat × Nat) : ENNReal :=
  ENNReal.ofReal
    (8 / (((p.1 + p.2 + 3 : Nat) : Real) ^ 3))

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The shifted inverse-cube envelope is summable over checkpoint/tail-offset pairs. -/
theorem tsum_quarticBlockShiftedInverseCubePairEnvelope_ne_top :
    Ne (∑' p : Nat × Nat,
      quarticBlockShiftedInverseCubePairEnvelope p) ∞ := by
  let diagonalEnvelope : Nat -> Real := fun n =>
    8 / (((n + 1 : Nat) : Real) ^ 2)
  have hdiagonalSummable : Summable diagonalEnvelope := by
    unfold diagonalEnvelope
    have hp : Summable (fun n : Nat =>
        1 / (((n + 1 : Nat) : Real) ^ 2)) := by
      have hbase :=
        (Real.summable_one_div_nat_add_rpow 1 2).2 (by norm_num)
      convert hbase using 1
      funext n
      rw [abs_of_nonneg (by positivity : (0 : Real) <= (n : Real) + 1)]
      norm_num
    simpa [diagonalEnvelope, div_eq_mul_inv, mul_assoc] using hp.mul_left 8
  have hdiagonalFinite :
      Ne (∑' n : Nat, ENNReal.ofReal (diagonalEnvelope n)) ∞ :=
    hdiagonalSummable.tsum_ofReal_ne_top
  have hdiag (n : Nat) :
      (∑' p : (Finset.antidiagonal n),
        quarticBlockShiftedInverseCubePairEnvelope p) <=
        ENNReal.ofReal (diagonalEnvelope n) := by
    have hconstant :
        (∑' p : (Finset.antidiagonal n),
          quarticBlockShiftedInverseCubePairEnvelope p) =
          (n + 1 : ENNReal) *
            ENNReal.ofReal
              (8 / (((n + 3 : Nat) : Real) ^ 3)) := by
      calc
        (∑' p : (Finset.antidiagonal n),
            quarticBlockShiftedInverseCubePairEnvelope p) =
            ∑' _p : (Finset.antidiagonal n),
              ENNReal.ofReal
                (8 / (((n + 3 : Nat) : Real) ^ 3)) := by
          apply tsum_congr
          intro p
          unfold quarticBlockShiftedInverseCubePairEnvelope
          have hp : p.1.1 + p.1.2 = n := by
            simpa only [Finset.mem_antidiagonal] using p.2
          rw [hp]
        _ = (n + 1 : ENNReal) *
              ENNReal.ofReal
                (8 / (((n + 3 : Nat) : Real) ^ 3)) := by
          rw [tsum_fintype]
          simp
    rw [hconstant]
    unfold diagonalEnvelope
    rw [← ENNReal.ofReal_natCast n, ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_add (Nat.cast_nonneg n) (by norm_num),
      ← ENNReal.ofReal_mul (by positivity : (0 : Real) <= (n : Real) + 1)]
    apply ENNReal.ofReal_le_ofReal
    have hx : (0 : Real) < ((n + 1 : Nat) : Real) := by positivity
    have hy : (0 : Real) < ((n + 3 : Nat) : Real) := by positivity
    have hxy : ((n + 1 : Nat) : Real) <= ((n + 3 : Nat) : Real) := by
      exact_mod_cast (show n + 1 <= n + 3 by omega)
    show
      ((n : Real) + 1) *
          (8 / (((n + 3 : Nat) : Real) ^ 3)) <=
        8 / (((n + 1 : Nat) : Real) ^ 2)
    exact
      calc
        ((n : Real) + 1) *
              (8 / (((n + 3 : Nat) : Real) ^ 3)) <=
            ((n + 3 : Nat) : Real) *
              (8 / (((n + 3 : Nat) : Real) ^ 3)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          norm_num at hxy ⊢
        _ = 8 / (((n + 3 : Nat) : Real) ^ 2) := by
          field_simp [ne_of_gt hy]
        _ <= 8 / (((n + 1 : Nat) : Real) ^ 2) := by
          have hsquares :
              (((n + 1 : Nat) : Real) ^ 2) <=
                (((n + 3 : Nat) : Real) ^ 2) := by
            simpa only [pow_two] using mul_self_le_mul_self hx.le hxy
          exact div_le_div_of_nonneg_left (by norm_num) (pow_pos hx 2)
            hsquares
  have hsigma :
      (∑' q : Σ n : Nat, (Finset.antidiagonal n),
          quarticBlockShiftedInverseCubePairEnvelope
            (Finset.sigmaAntidiagonalEquivProd q)) <=
        ∑' n : Nat, ENNReal.ofReal (diagonalEnvelope n) := by
    rw [ENNReal.tsum_sigma']
    exact ENNReal.tsum_le_tsum hdiag
  have hreindex :
      (∑' p : Nat × Nat, quarticBlockShiftedInverseCubePairEnvelope p) =
        ∑' q : Σ n : Nat, (Finset.antidiagonal n),
          quarticBlockShiftedInverseCubePairEnvelope
            (Finset.sigmaAntidiagonalEquivProd q) := by
    exact (Finset.sigmaAntidiagonalEquivProd.tsum_eq
      quarticBlockShiftedInverseCubePairEnvelope).symm
  rw [hreindex]
  exact ne_top_of_le_ne_top hdiagonalFinite hsigma

/-- One checkpoint block weight times one shifted coordinate model-failure charge. -/
noncomputable def quarticBlockShiftedCoordinateModelFailureCharge
    (mdp : MDP State Action) (p : Nat × Nat) : ENNReal :=
  (explicitHighProbabilityQuarticBlockWeight p.1 : ENNReal) *
    selfConsistentScheduledCausalCoordinateModelFailureBudget mdp
      (p.1 + p.2 + 1)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- Positive horizon makes the actual weighted coordinate charge fit the inverse-cube pair envelope. -/
theorem quarticBlockShiftedCoordinateModelFailureCharge_le_pairEnvelope
    (mdp : MDP State Action) (hhorizon : 0 < mdp.horizon)
    (p : Nat × Nat) :
    quarticBlockShiftedCoordinateModelFailureCharge mdp p <=
      quarticBlockShiftedInverseCubePairEnvelope p := by
  let n := p.1
  let j := p.2
  let s : Real := ((n + j + 3 : Nat) : Real)
  let delta :=
    AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledLocalDelta
      mdp (n + j + 1)
  have hs : 0 < s := by
    dsimp [s]
    positivity
  have hdeltaNonneg : 0 <= delta := by
    dsimp [delta]
    rw [selfConsistentScheduledLocalDelta_eq_inv_pow]
    positivity
  have hdelta : delta <= 1 / s ^ 6 := by
    dsimp [delta, s, n, j]
    convert selfConsistentScheduledLocalDelta_le_inv_pow_six mdp hhorizon
      (p.1 + p.2 + 1) using 1
  have hnle : ((n + 2 : Nat) : Real) <= s := by
    dsimp [s, n, j]
    exact_mod_cast (show p.1 + 2 <= p.1 + p.2 + 3 by omega)
  have hcube : (((n + 2 : Nat) : Real) ^ 3) <= s ^ 3 := by
    have hnnonneg : (0 : Real) <= ((n + 2 : Nat) : Real) := by positivity
    have hsnonneg : (0 : Real) <= s := hs.le
    nlinarith [mul_self_le_mul_self hnnonneg hnle]
  have hreal :
      ((explicitHighProbabilityQuarticBlockWeight n : Nat) : Real) *
          (delta + delta) <=
        8 / s ^ 3 := by
    have hweight :
        ((explicitHighProbabilityQuarticBlockWeight n : Nat) : Real) <=
          4 * s ^ 3 := by
      unfold explicitHighProbabilityQuarticBlockWeight
      push_cast
      norm_num at hcube ⊢
      nlinarith
    calc
      ((explicitHighProbabilityQuarticBlockWeight n : Nat) : Real) *
            (delta + delta) <=
          ((explicitHighProbabilityQuarticBlockWeight n : Nat) : Real) *
            (1 / s ^ 6 + 1 / s ^ 6) := by
        gcongr
      _ <= (4 * s ^ 3) * (1 / s ^ 6 + 1 / s ^ 6) := by
        gcongr
      _ = 8 / s ^ 3 := by
        field_simp [ne_of_gt hs]
        norm_num
  unfold quarticBlockShiftedCoordinateModelFailureCharge
    quarticBlockShiftedInverseCubePairEnvelope
    selfConsistentScheduledCausalCoordinateModelFailureBudget
  change
    (explicitHighProbabilityQuarticBlockWeight n : ENNReal) *
        (ENNReal.ofReal delta + ENNReal.ofReal delta) <=
      ENNReal.ofReal (8 / s ^ 3)
  rw [← ENNReal.ofReal_natCast
      (explicitHighProbabilityQuarticBlockWeight n),
    ← ENNReal.ofReal_add hdeltaNonneg hdeltaNonneg,
    ← ENNReal.ofReal_mul (by positivity :
      (0 : Real) <=
        ((explicitHighProbabilityQuarticBlockWeight n : Nat) : Real))]
  exact ENNReal.ofReal_le_ofReal hreal

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The actual weighted shifted coordinate charges have finite total ENNReal mass. -/
theorem tsum_quarticBlockShiftedCoordinateModelFailureCharge_ne_top
    (mdp : MDP State Action) (hhorizon : 0 < mdp.horizon) :
    Ne (∑' p : Nat × Nat,
      quarticBlockShiftedCoordinateModelFailureCharge mdp p) ∞ := by
  exact ne_top_of_le_ne_top
    tsum_quarticBlockShiftedInverseCubePairEnvelope_ne_top
    (ENNReal.tsum_le_tsum
      (quarticBlockShiftedCoordinateModelFailureCharge_le_pairEnvelope
        mdp hhorizon))

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- A model tail after `n+1`, charged by one quartic block weight, is the shifted coordinate row. -/
theorem quarticBlockWeight_mul_tailModelFailureBudget_eq_tsum_shiftedCoordinateCharge
    (mdp : MDP State Action) (n : Nat) :
    (explicitHighProbabilityQuarticBlockWeight n : ENNReal) *
        selfConsistentScheduledCausalTailModelFailureBudget mdp (n + 1) =
      ∑' j : Nat,
        quarticBlockShiftedCoordinateModelFailureCharge mdp (n, j) := by
  have htail :
      selfConsistentScheduledCausalTailModelFailureBudget mdp (n + 1) =
        ∑' j : Nat,
          selfConsistentScheduledCausalCoordinateModelFailureBudget mdp
            (j + (n + 1)) := by
    unfold selfConsistentScheduledCausalTailModelFailureBudget
    exact ((notMemRangeEquiv (n + 1)).symm.tsum_eq
      (fun t : {t // t ∉ Finset.range (n + 1)} =>
        selfConsistentScheduledCausalCoordinateModelFailureBudget mdp t)).symm
  rw [htail, ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro j
  unfold quarticBlockShiftedCoordinateModelFailureCharge
  congr 2
  omega

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The fourth-power block weights are summable against the exact infinite model-tail budgets. -/
theorem tsum_quarticBlockWeight_mul_tailModelFailureBudget_ne_top
    (mdp : MDP State Action) (hhorizon : 0 < mdp.horizon) :
    Ne (∑' n : Nat,
      (explicitHighProbabilityQuarticBlockWeight n : ENNReal) *
        selfConsistentScheduledCausalTailModelFailureBudget mdp (n + 1)) ∞ := by
  rw [show (fun n : Nat =>
      (explicitHighProbabilityQuarticBlockWeight n : ENNReal) *
        selfConsistentScheduledCausalTailModelFailureBudget mdp (n + 1)) =
      fun n => ∑' j : Nat,
        quarticBlockShiftedCoordinateModelFailureCharge mdp (n, j) by
    funext n
    exact
      quarticBlockWeight_mul_tailModelFailureBudget_eq_tsum_shiftedCoordinateCharge
        mdp n]
  rw [← ENNReal.tsum_prod']
  exact tsum_quarticBlockShiftedCoordinateModelFailureCharge_ne_top
    mdp hhorizon

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- A cubic fourth-power block weight times the explicit exponential return share is summable. -/
theorem summable_quarticBlockWeight_mul_explicitHighProbabilityReturnDelta :
    Summable (fun n : Nat =>
      ((explicitHighProbabilityQuarticBlockWeight n : Nat) : Real) *
        explicitHighProbabilityReturnDelta n) := by
  let base : Nat -> Real := fun n =>
    (n : Real) ^ 3 * Real.exp (-(1 : Real) * (n : Real))
  have hbase : Summable base := by
    simpa [base] using
      (Real.summable_pow_mul_exp_neg_nat_mul 3
        (by norm_num : (0 : Real) < 1))
  have hshift : Summable (fun n : Nat => base (n + 2)) :=
    (summable_nat_add_iff (f := base) 2).2 hbase
  have hscaled := hshift.mul_left (4 * Real.exp 1)
  apply hscaled.congr
  intro n
  unfold base explicitHighProbabilityQuarticBlockWeight
    explicitHighProbabilityReturnDelta explicitHighProbabilityScale
  push_cast
  calc
    (4 * Real.exp 1) *
          (((n : Real) + 2) ^ 3 *
            Real.exp (-(1 : Real) * ((n : Real) + 2))) =
        4 * ((n : Real) + 2) ^ 3 *
          (Real.exp 1 *
            Real.exp (-(1 : Real) * ((n : Real) + 2))) := by ring
    _ = 4 * ((n : Real) + 2) ^ 3 *
          Real.exp (-(n : Real) - 1) := by
      rw [← Real.exp_add 1 (-(1 : Real) * ((n : Real) + 2))]
      congr 2
      ring
    _ = 4 * ((n : Real) + 2) ^ 3 *
          Real.exp (-((n : Real) + 1)) := by ring

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The exact exponential return shares have finite total mass after quartic block charging. -/
theorem tsum_quarticBlockWeight_mul_explicitHighProbabilityReturnDelta_ne_top :
    Ne (∑' n : Nat,
      (explicitHighProbabilityQuarticBlockWeight n : ENNReal) *
        ENNReal.ofReal (explicitHighProbabilityReturnDelta n)) ∞ := by
  have hfinite :=
    summable_quarticBlockWeight_mul_explicitHighProbabilityReturnDelta.tsum_ofReal_ne_top
  convert hfinite using 1
  apply tsum_congr
  intro n
  rw [← ENNReal.ofReal_natCast
      (explicitHighProbabilityQuarticBlockWeight n),
    ← ENNReal.ofReal_mul (by positivity :
      (0 : Real) <=
        ((explicitHighProbabilityQuarticBlockWeight n : Nat) : Real))]

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The exact checkpoint violation budgets remain summable after paying every quartic block width. -/
theorem tsum_quarticBlockWeight_mul_explicitPolynomialPrefixTailModelReturnFailureBudget_ne_top
    (mdp : MDP State Action) (hhorizon : 0 < mdp.horizon) :
    Ne (∑' n : Nat,
      (explicitHighProbabilityQuarticBlockWeight n : ENNReal) *
        explicitPolynomialPrefixTailModelReturnFailureBudget mdp n) ∞ := by
  have hmodel :=
    tsum_quarticBlockWeight_mul_tailModelFailureBudget_ne_top mdp hhorizon
  have hreturn :=
    tsum_quarticBlockWeight_mul_explicitHighProbabilityReturnDelta_ne_top
  unfold explicitPolynomialPrefixTailModelReturnFailureBudget
    selfConsistentScheduledNaturalCausalBurninTailModelReturnFailureBudget
    explicitHighProbabilityBurnin
  simp_rw [mul_add]
  rw [ENNReal.tsum_add]
  exact ENNReal.add_ne_top.mpr ⟨hmodel, hreturn⟩

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- Cubic block weights dominate every finite telescope of the fourth-power checkpoint grid. -/
theorem explicitHighProbabilityRounds_add_le_add_sum_Ico_quarticBlockWeight
    (start width : Nat) :
    explicitHighProbabilityRounds (start + width) <=
      explicitHighProbabilityRounds start +
        (Finset.Ico start (start + width)).sum
          explicitHighProbabilityQuarticBlockWeight := by
  induction width with
  | zero => simp
  | succ width ih =>
      have hmono :
          explicitHighProbabilityRounds (start + width) <=
            explicitHighProbabilityRounds (start + width + 1) :=
        explicitHighProbabilityRounds_mono (by omega)
      have hstep :
          explicitHighProbabilityRounds (start + width + 1) <=
            explicitHighProbabilityRounds (start + width) +
              explicitHighProbabilityQuarticBlockWeight (start + width) := by
        have hgap :=
          explicitHighProbabilityRounds_succ_sub_le_quarticBlockWeight
            (start + width)
        omega
      rw [show start + (width + 1) = start + width + 1 by omega,
        Finset.sum_Ico_succ_top (by omega : start <= start + width)]
      calc
        explicitHighProbabilityRounds (start + width + 1) <=
            explicitHighProbabilityRounds (start + width) +
              explicitHighProbabilityQuarticBlockWeight (start + width) :=
          hstep
        _ <= (explicitHighProbabilityRounds start +
              (Finset.Ico start (start + width)).sum
                explicitHighProbabilityQuarticBlockWeight) +
              explicitHighProbabilityQuarticBlockWeight (start + width) :=
          Nat.add_le_add_right ih _
        _ = explicitHighProbabilityRounds start +
            ((Finset.Ico start (start + width)).sum
                explicitHighProbabilityQuarticBlockWeight +
              explicitHighProbabilityQuarticBlockWeight (start + width)) := by
          omega

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- A finite natural time is paid for by an initial checkpoint plus all preceding delayed blocks. -/
theorem natCast_succ_le_checkpoint_add_tsum_quarticBlockWeight_of_delayed
    (start time : Nat) :
    (time + 1 : ENNReal) <=
      (explicitHighProbabilityRounds start + 1 : ENNReal) +
        ∑' n : Nat,
          if start <= n ∧ explicitHighProbabilityRounds n < time then
            (explicitHighProbabilityQuarticBlockWeight n : ENNReal)
          else 0 := by
  have hexists : exists width : Nat,
      time <= explicitHighProbabilityRounds (start + width) := by
    refine ⟨time, ?_⟩
    calc
      time <= explicitHighProbabilityRounds (time + start) :=
        scheduleIndex_le_explicitHighProbabilityRounds_add time start
      _ = explicitHighProbabilityRounds (start + time) := by
        rw [Nat.add_comm]
  let width := Nat.find hexists
  have hcover : time <= explicitHighProbabilityRounds (start + width) :=
    Nat.find_spec hexists
  by_cases hwidth : width = 0
  · rw [hwidth, Nat.add_zero] at hcover
    exact le_trans (by exact_mod_cast Nat.succ_le_succ hcover)
      (le_add_right (le_refl
        (explicitHighProbabilityRounds start + 1 : ENNReal)))
  · obtain ⟨previous, hprevious⟩ : exists previous, width = previous + 1 := by
      exact ⟨width - 1, by omega⟩
    have hnotCover :
        ¬ time <= explicitHighProbabilityRounds (start + previous) := by
      apply Nat.find_min hexists
      omega
    have hpreviousDelayed :
        explicitHighProbabilityRounds (start + previous) < time := by
      omega
    have hdelayed : (n : Nat) -> n ∈ Finset.Ico start (start + width) ->
        start <= n ∧ explicitHighProbabilityRounds n < time := by
      intro n hn
      refine ⟨(Finset.mem_Ico.mp hn).1, ?_⟩
      have hnle : n <= start + previous := by
        have hnlt := (Finset.mem_Ico.mp hn).2
        omega
      exact lt_of_le_of_lt (explicitHighProbabilityRounds_mono hnle)
        hpreviousDelayed
    have hsum :
        (((Finset.Ico start (start + width)).sum
            explicitHighProbabilityQuarticBlockWeight : Nat) : ENNReal) <=
          ∑' n : Nat,
            if start <= n ∧ explicitHighProbabilityRounds n < time then
              (explicitHighProbabilityQuarticBlockWeight n : ENNReal)
            else 0 := by
      calc
        (((Finset.Ico start (start + width)).sum
              explicitHighProbabilityQuarticBlockWeight : Nat) : ENNReal) =
            ∑ n ∈ Finset.Ico start (start + width),
              (if start <= n ∧ explicitHighProbabilityRounds n < time then
                (explicitHighProbabilityQuarticBlockWeight n : ENNReal)
              else 0) := by
          calc
            (((Finset.Ico start (start + width)).sum
                explicitHighProbabilityQuarticBlockWeight : Nat) : ENNReal) =
                ∑ n ∈ Finset.Ico start (start + width),
                  (explicitHighProbabilityQuarticBlockWeight n : ENNReal) := by
              exact_mod_cast rfl
            _ = ∑ n ∈ Finset.Ico start (start + width),
                (if start <= n ∧ explicitHighProbabilityRounds n < time then
                  (explicitHighProbabilityQuarticBlockWeight n : ENNReal)
                else 0) := by
              apply Finset.sum_congr rfl
              intro n hn
              simp [hdelayed n hn]
        _ <= ∑' n : Nat,
              if start <= n ∧ explicitHighProbabilityRounds n < time then
                (explicitHighProbabilityQuarticBlockWeight n : ENNReal)
              else 0 := ENNReal.sum_le_tsum _
    have htelescope :=
      explicitHighProbabilityRounds_add_le_add_sum_Ico_quarticBlockWeight
        start width
    calc
      (time + 1 : ENNReal) <=
          (explicitHighProbabilityRounds (start + width) + 1 : Nat) := by
        exact_mod_cast Nat.succ_le_succ hcover
      _ <= (explicitHighProbabilityRounds start +
            (Finset.Ico start (start + width)).sum
              explicitHighProbabilityQuarticBlockWeight + 1 : Nat) := by
        exact_mod_cast Nat.succ_le_succ htelescope
      _ = (explicitHighProbabilityRounds start + 1 : ENNReal) +
          (((Finset.Ico start (start + width)).sum
            explicitHighProbabilityQuarticBlockWeight : Nat) : ENNReal) := by
        push_cast
        ring
      _ <= (explicitHighProbabilityRounds start + 1 : ENNReal) +
          ∑' n : Nat,
            if start <= n ∧ explicitHighProbabilityRounds n < time then
              (explicitHighProbabilityQuarticBlockWeight n : ENNReal)
            else 0 := add_le_add le_rfl hsum

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- Eventually summable fourth-power checkpoint crossing tails imply a finite first moment. -/
theorem integrable_untopA_add_one_of_eventually_quarticCheckpointTail
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (tau : Omega -> WithTop Nat) (htau : Measurable tau)
    (budget : Nat -> ENNReal)
    (hbudget : Ne (∑' n : Nat,
      (explicitHighProbabilityQuarticBlockWeight n : ENNReal) * budget n) ∞)
    (htail : ∀ᶠ n : Nat in atTop,
      mu {omega |
        (explicitHighProbabilityRounds n : WithTop Nat) < tau omega} <=
          budget n) :
    Integrable
      (fun omega => (((tau omega).untopA + 1 : Nat) : Real)) mu := by
  obtain ⟨start, htailStart⟩ := Filter.eventually_atTop.1 htail
  let delayed : Nat -> Set Omega := fun n =>
    {omega | (explicitHighProbabilityRounds n : WithTop Nat) < tau omega}
  have hdelayedMeasurable (n : Nat) : MeasurableSet (delayed n) := by
    exact measurableSet_lt measurable_const htau
  let term : Nat -> Omega -> ENNReal := fun n =>
    if start <= n then
      (delayed n).indicator
        (fun _ => (explicitHighProbabilityQuarticBlockWeight n : ENNReal))
    else fun _ => 0
  have htermMeasurable (n : Nat) : AEMeasurable (term n) mu := by
    by_cases hn : start <= n
    · simp only [term, hn, if_true]
      exact (Measurable.indicator measurable_const
        (hdelayedMeasurable n)).aemeasurable
    · simp only [term, hn, if_false]
      exact measurable_const.aemeasurable
  have hpoint (omega : Omega) :
      ENNReal.ofReal ((((tau omega).untopA + 1 : Nat) : Real)) <=
        (explicitHighProbabilityRounds start + 1 : ENNReal) +
          ∑' n : Nat, term n omega := by
    have hnat :=
      natCast_succ_le_checkpoint_add_tsum_quarticBlockWeight_of_delayed
        start (tau omega).untopA
    calc
      ENNReal.ofReal ((((tau omega).untopA + 1 : Nat) : Real)) =
          ((tau omega).untopA : ENNReal) + 1 := by
        push_cast
        rw [ENNReal.ofReal_add (Nat.cast_nonneg _) (by norm_num),
          ENNReal.ofReal_natCast, ENNReal.ofReal_one]
      _ <= (explicitHighProbabilityRounds start + 1 : ENNReal) +
          ∑' n : Nat,
            if start <= n ∧
                explicitHighProbabilityRounds n < (tau omega).untopA then
              (explicitHighProbabilityQuarticBlockWeight n : ENNReal)
            else 0 := hnat
      _ <= (explicitHighProbabilityRounds start + 1 : ENNReal) +
          ∑' n : Nat, term n omega := by
        apply add_le_add le_rfl
        apply ENNReal.tsum_le_tsum
        intro n
        by_cases hn : start <= n
        · by_cases htime :
              explicitHighProbabilityRounds n < (tau omega).untopA
          · have hmem : omega ∈ delayed n := by
              unfold delayed
              by_cases htop : tau omega = (⊤ : WithTop Nat)
              · simp [htop]
              · exact (WithTop.lt_untopA_iff htop).mp htime
            simp [term, hn, htime, hmem]
          · simp [term, hn, htime]
        · simp [term, hn]
  have htermIntegral (n : Nat) :
      ∫⁻ omega, term n omega ∂mu <=
        (explicitHighProbabilityQuarticBlockWeight n : ENNReal) * budget n := by
    by_cases hn : start <= n
    · have htailN : mu (delayed n) <= budget n := by
        simpa [delayed] using htailStart n hn
      simp only [term, hn, if_true]
      rw [lintegral_indicator_const (hdelayedMeasurable n)]
      gcongr
    · simp [term, hn]
  have hdomIntegral :
      ∫⁻ omega,
          ((explicitHighProbabilityRounds start + 1 : ENNReal) +
            ∑' n : Nat, term n omega) ∂mu <=
        (explicitHighProbabilityRounds start + 1 : ENNReal) +
          ∑' n : Nat,
            (explicitHighProbabilityQuarticBlockWeight n : ENNReal) *
              budget n := by
    rw [lintegral_add_left measurable_const, lintegral_const,
      lintegral_tsum htermMeasurable]
    simp only [IsProbabilityMeasure.measure_univ, mul_one]
    exact add_le_add le_rfl (ENNReal.tsum_le_tsum htermIntegral)
  have hrhsFinite :
      (explicitHighProbabilityRounds start + 1 : ENNReal) +
          ∑' n : Nat,
            (explicitHighProbabilityQuarticBlockWeight n : ENNReal) *
              budget n < ∞ := by
    rw [ENNReal.add_lt_top]
    exact ⟨by simp, lt_top_iff_ne_top.mpr hbudget⟩
  have hmeasurable : Measurable
      (fun omega => (((tau omega).untopA + 1 : Nat) : Real)) :=
    (measurable_of_countable
      (fun count : Nat => (((count + 1 : Nat) : Nat) : Real))).comp
        htau.untopA
  refine ⟨hmeasurable.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall fun _ => by positivity)]
  exact lt_of_le_of_lt
    (lintegral_mono hpoint |>.trans hdomIntegral) hrhsFinite

/-- Checkpoint trajectories whose fixed-index uncapped first passage has not
yet occurred. -/
noncomputable def
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterDelayedCheckpointSet
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (scheduleIndex checkpointIndex : Nat) :
    Set (HeterogeneousStochasticEpisodeBatchTrajectory mdp
      (fun t =>
        AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledEpisodes
          mdp varianceProxy baseVisitFloor t)) :=
  {trajectory |
    (explicitHighProbabilityRounds checkpointIndex : WithTop Nat) <
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor scheduleIndex trajectory}

/-- Every fixed delayed-checkpoint event is measurable. -/
theorem
    measurableSet_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterDelayedCheckpointSet
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (scheduleIndex checkpointIndex : Nat) :
    MeasurableSet
      (selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterDelayedCheckpointSet
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor scheduleIndex checkpointIndex) := by
  unfold
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterDelayedCheckpointSet
  exact measurableSet_lt measurable_const
    (selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix_isStoppingTime
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor scheduleIndex).measurable'

/-- Once a checkpoint lies beyond the fixed base and its deterministic rate is
below the fixed threshold, every delayed first passage violates the compiled
checkpoint regret bound. -/
theorem
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterDelayedCheckpointSet_subset_explicitPolynomialPrefixAverageRealizedBehaviorRegretViolationSet
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State) (varianceProxy : NNReal)
    (baseVisitFloor : Real) {scheduleIndex checkpointIndex : Nat}
    (hindex : scheduleIndex <= checkpointIndex)
    (hrate :
      explicitPolynomialPrefixAverageRealizedBehaviorRegretRate
          mdp varianceProxy baseVisitFloor checkpointIndex <=
        selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold
          scheduleIndex) :
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterDelayedCheckpointSet
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor scheduleIndex checkpointIndex ⊆
      explicitPolynomialPrefixAverageRealizedBehaviorRegretViolationSet mdp
        initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor checkpointIndex := by
  intro trajectory hdelayed
  unfold explicitPolynomialPrefixAverageRealizedBehaviorRegretViolationSet
    selfConsistentScheduledNaturalCausalBurninAverageRealizedBehaviorRegretLogarithmicViolationSet
  change
    explicitPolynomialPrefixAverageRealizedBehaviorRegretRate
        mdp varianceProxy baseVisitFloor checkpointIndex <
      selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor (explicitHighProbabilityRounds checkpointIndex)
            trajectory
  by_contra hnotViolation
  have hprocess :
      selfConsistentScheduledNaturalCausalAverageRealizedBehaviorRegretProcess
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor (explicitHighProbabilityRounds checkpointIndex)
              trajectory <=
        selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold
          scheduleIndex :=
    (le_of_not_gt hnotViolation).trans hrate
  have hstopLe :
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor scheduleIndex trajectory <=
        (explicitHighProbabilityRounds checkpointIndex : WithTop Nat) := by
    unfold
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
    exact MeasureTheory.hittingAfter_le_of_mem
      (by
        exact_mod_cast explicitHighProbabilityRounds_mono hindex)
      hprocess
  exact (not_lt_of_ge hstopLe) hdelayed

/-- For each fixed threshold index, checkpoint crossing tails are eventually
bounded by the explicit summable burn-in-tail/model-return budget. -/
theorem
    eventually_selfConsistentScheduledCausalSource_trajectoryMeasure_inverseSqrtThresholdUnboundedHittingAfterDelayedCheckpointSet_le
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (varianceProxy : NNReal) (hvarianceProxy : 0 < varianceProxy)
    (law : rewardSource.UniformSubgaussianRewardLaw varianceProxy)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State)
    (support : ExploratoryPathSupport mdp initialState)
    (baseVisitFloor : Real)
    (hbaseFloor : ExploratoryPathUniformVisitFloor support 1 baseVisitFloor)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (hhorizon : 0 < mdp.horizon) (hbaseVisitFloor : 0 < baseVisitFloor)
    (scheduleIndex : Nat) :
    let source := selfConsistentScheduledCausalSource mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
    ∀ᶠ checkpointIndex in atTop,
      source.trajectoryMeasure
          (selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterDelayedCheckpointSet
            mdp initialState rewardSource initialTable defaultState
              varianceProxy baseVisitFloor scheduleIndex checkpointIndex) <=
        explicitPolynomialPrefixTailModelReturnFailureBudget mdp
          checkpointIndex := by
  dsimp only
  have hcert :=
    selfConsistentScheduledCausalSource_explicitPolynomialPrefixHighProbabilityAverageRealizedBehaviorRegretConsistency
      mdp initialState rewardSource varianceProxy hvarianceProxy law
        initialTable defaultState support baseVisitFloor hbaseFloor
          hrewardBound hhorizon hbaseVisitFloor
  dsimp only at hcert
  rcases hcert with
    ⟨_hbudgetTendsto, hrateTendsto, _hbudgetEventually, hcheckpoint⟩
  have hrateEventually := hrateTendsto.eventually_lt_const
    (selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold_pos
      scheduleIndex)
  filter_upwards [eventually_ge_atTop scheduleIndex, hrateEventually] with
    checkpointIndex hindex hrate
  have hsubset :=
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterDelayedCheckpointSet_subset_explicitPolynomialPrefixAverageRealizedBehaviorRegretViolationSet
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor hindex hrate.le
  rcases hcheckpoint checkpointIndex with
    ⟨_heventMeasurable, _hviolationMeasurable, _heventMeasure,
      _hviolationSubset, hviolationMeasure, _hstrict, _hpath⟩
  exact (measure_mono hsubset).trans hviolationMeasure

/-- Each fixed-index genuine uncapped inverse-square-root first passage is
finite almost surely and has an integrable random horizon. -/
theorem
    selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_integrableFiniteStoppingTime
    (mdp : MDP State Action) (initialState : Measure State)
    [IsProbabilityMeasure initialState]
    [StandardBorelSpace State] [StandardBorelSpace Action]
    (rewardSource : mdp.MeanCompatibleRewardKernel)
    (varianceProxy : NNReal) (hvarianceProxy : 0 < varianceProxy)
    (law : rewardSource.UniformSubgaussianRewardLaw varianceProxy)
    (initialTable : DeterministicMarkovPolicyTable mdp)
    (defaultState : State)
    (support : ExploratoryPathSupport mdp initialState)
    (baseVisitFloor : Real)
    (hbaseFloor : ExploratoryPathUniformVisitFloor support 1 baseVisitFloor)
    (hrewardBound : forall state action, |mdp.reward state action| <= 1)
    (hhorizon : 0 < mdp.horizon) (hbaseVisitFloor : 0 < baseVisitFloor)
    (scheduleIndex : Nat) :
    let source := selfConsistentScheduledCausalSource mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
    BanditRLProof.OFUL.IntegrableFiniteStoppingTime source.trajectoryMeasure
      (selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor scheduleIndex) := by
  dsimp only
  let tau :=
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor scheduleIndex
  refine ⟨?_, ?_⟩
  · exact
      ae_ne_top_selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
        mdp initialState rewardSource varianceProxy hvarianceProxy law
          initialTable defaultState support baseVisitFloor hbaseFloor
            hrewardBound hhorizon hbaseVisitFloor scheduleIndex
  · apply integrable_untopA_add_one_of_eventually_quarticCheckpointTail
      (selfConsistentScheduledCausalSource mdp initialState rewardSource
        initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure
      tau
      (selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix_isStoppingTime
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor scheduleIndex).measurable'
      (explicitPolynomialPrefixTailModelReturnFailureBudget mdp)
      (tsum_quarticBlockWeight_mul_explicitPolynomialPrefixTailModelReturnFailureBudget_ne_top
        mdp hhorizon)
    exact
      eventually_selfConsistentScheduledCausalSource_trajectoryMeasure_inverseSqrtThresholdUnboundedHittingAfterDelayedCheckpointSet_le
        mdp initialState rewardSource varianceProxy hvarianceProxy law
          initialTable defaultState support baseVisitFloor hbaseFloor
            hrewardBound hhorizon hbaseVisitFloor scheduleIndex

end AdaptiveStochasticSampledEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
