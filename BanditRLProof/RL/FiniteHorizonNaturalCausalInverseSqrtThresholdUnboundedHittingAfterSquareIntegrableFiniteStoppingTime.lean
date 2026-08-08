import BanditRLProof.RL.FiniteHorizonNaturalCausalInverseSqrtThresholdUnboundedHittingAfterIntegrableFiniteStoppingTime
import BanditRLProof.OFULScheduledUnboundedStoppingTimeExpectedRegretRate

/-!
# Second moment of the uncapped inverse-sqrt hitting time

This module upgrades each fixed-index genuine `hittingAfter` first passage
from a first moment to `OFUL.SquareIntegrableFiniteStoppingTime` when
`4 < mdp.horizon`. Squaring the fourth-power checkpoint values produces a
seventh-degree block weight. The stronger horizon contract supplies an
inverse-tenth local confidence share, leaving a summable inverse-square
diagonal after shifted-tail reindexing.

The result is fixed-index L2 regularity. It does not prove a uniform moment
rate, a stopped-process L1 theorem, an exponential crossing tail, or an
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

/-- Seventh-degree envelope for one consecutive squared fourth-power checkpoint block. -/
def explicitHighProbabilityQuarticSquareBlockWeight (n : Nat) : Nat :=
  16 * (n + 2) ^ 7

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- A consecutive squared fourth-power checkpoint gap is bounded by the seventh-degree weight. -/
theorem explicitHighProbabilityRounds_succ_square_sub_le_quarticSquareBlockWeight
    (n : Nat) :
    (explicitHighProbabilityRounds (n + 1) + 1) ^ 2 -
        (explicitHighProbabilityRounds n + 1) ^ 2 <=
      explicitHighProbabilityQuarticSquareBlockWeight n := by
  unfold explicitHighProbabilityRounds explicitHighProbabilityScale
    explicitHighProbabilityQuarticSquareBlockWeight
  rw [Nat.sub_le_iff_le_add]
  ring_nf
  omega

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- Horizon at least five makes every local confidence share no larger than a shifted inverse tenth power. -/
theorem selfConsistentScheduledLocalDelta_le_inv_pow_ten
    (mdp : MDP State Action) (hhorizon : 4 < mdp.horizon) (t : Nat) :
    AdaptiveStochasticEpisodeBatchSource.selfConsistentScheduledLocalDelta mdp t <=
      1 / (((t + 2 : Nat) : Real) ^ 10) := by
  rw [selfConsistentScheduledLocalDelta_eq_inv_pow mdp t]
  exact one_div_pow_le_one_div_pow_of_le
    (by exact_mod_cast (show 1 <= t + 2 by omega) :
      (1 : Real) <= ((t + 2 : Nat) : Real))
    (by omega : 10 <= mdp.horizon + 5)

/-- Inverse-cube pair envelope after a seventh-degree weight cancels seven inverse powers. -/
noncomputable def quarticSquareBlockShiftedInverseCubePairEnvelope
    (p : Nat × Nat) : ENNReal :=
  4 * quarticBlockShiftedInverseCubePairEnvelope p

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The square-block shifted pair envelope has finite total ENNReal mass. -/
theorem tsum_quarticSquareBlockShiftedInverseCubePairEnvelope_ne_top :
    Ne (∑' p : Nat × Nat,
      quarticSquareBlockShiftedInverseCubePairEnvelope p) ∞ := by
  rw [show (fun p : Nat × Nat =>
      quarticSquareBlockShiftedInverseCubePairEnvelope p) =
      fun p => 4 * quarticBlockShiftedInverseCubePairEnvelope p by rfl]
  rw [ENNReal.tsum_mul_left]
  exact ENNReal.mul_ne_top ENNReal.ofNat_ne_top
    tsum_quarticBlockShiftedInverseCubePairEnvelope_ne_top

/-- One squared-checkpoint block weight times one shifted coordinate model-failure charge. -/
noncomputable def quarticSquareBlockShiftedCoordinateModelFailureCharge
    (mdp : MDP State Action) (p : Nat × Nat) : ENNReal :=
  (explicitHighProbabilityQuarticSquareBlockWeight p.1 : ENNReal) *
    selfConsistentScheduledCausalCoordinateModelFailureBudget mdp
      (p.1 + p.2 + 1)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The inverse-tenth local share puts every seventh-weighted coordinate charge below the pair envelope. -/
theorem quarticSquareBlockShiftedCoordinateModelFailureCharge_le_pairEnvelope
    (mdp : MDP State Action) (hhorizon : 4 < mdp.horizon)
    (p : Nat × Nat) :
    quarticSquareBlockShiftedCoordinateModelFailureCharge mdp p <=
      quarticSquareBlockShiftedInverseCubePairEnvelope p := by
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
  have hdelta : delta <= 1 / s ^ 10 := by
    dsimp [delta, s, n, j]
    convert selfConsistentScheduledLocalDelta_le_inv_pow_ten mdp hhorizon
      (p.1 + p.2 + 1) using 1
  have hnle : ((n + 2 : Nat) : Real) <= s := by
    dsimp [s, n, j]
    exact_mod_cast (show p.1 + 2 <= p.1 + p.2 + 3 by omega)
  have hseventh : (((n + 2 : Nat) : Real) ^ 7) <= s ^ 7 := by
    exact pow_le_pow_left₀ (by positivity) hnle 7
  have hreal :
      ((explicitHighProbabilityQuarticSquareBlockWeight n : Nat) : Real) *
          (delta + delta) <=
        32 / s ^ 3 := by
    have hweight :
        ((explicitHighProbabilityQuarticSquareBlockWeight n : Nat) : Real) <=
          16 * s ^ 7 := by
      unfold explicitHighProbabilityQuarticSquareBlockWeight
      push_cast
      norm_num at hseventh ⊢
      nlinarith
    calc
      ((explicitHighProbabilityQuarticSquareBlockWeight n : Nat) : Real) *
            (delta + delta) <=
          ((explicitHighProbabilityQuarticSquareBlockWeight n : Nat) : Real) *
            (1 / s ^ 10 + 1 / s ^ 10) := by
        gcongr
      _ <= (16 * s ^ 7) * (1 / s ^ 10 + 1 / s ^ 10) := by
        gcongr
      _ = 32 / s ^ 3 := by
        field_simp [ne_of_gt hs]
        norm_num
  unfold quarticSquareBlockShiftedCoordinateModelFailureCharge
    quarticSquareBlockShiftedInverseCubePairEnvelope
    quarticBlockShiftedInverseCubePairEnvelope
    selfConsistentScheduledCausalCoordinateModelFailureBudget
  change
    (explicitHighProbabilityQuarticSquareBlockWeight n : ENNReal) *
        (ENNReal.ofReal delta + ENNReal.ofReal delta) <=
      4 * ENNReal.ofReal (8 / s ^ 3)
  rw [← ENNReal.ofReal_natCast
      (explicitHighProbabilityQuarticSquareBlockWeight n),
    ← ENNReal.ofReal_add hdeltaNonneg hdeltaNonneg,
    ← ENNReal.ofReal_mul (by positivity :
      (0 : Real) <=
        ((explicitHighProbabilityQuarticSquareBlockWeight n : Nat) : Real)),
    ← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num : (0 : Real) <= 4)]
  apply ENNReal.ofReal_le_ofReal
  convert hreal using 1
  ring_nf

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The seventh-weighted shifted coordinate charges have finite total ENNReal mass. -/
theorem tsum_quarticSquareBlockShiftedCoordinateModelFailureCharge_ne_top
    (mdp : MDP State Action) (hhorizon : 4 < mdp.horizon) :
    Ne (∑' p : Nat × Nat,
      quarticSquareBlockShiftedCoordinateModelFailureCharge mdp p) ∞ := by
  exact ne_top_of_le_ne_top
    tsum_quarticSquareBlockShiftedInverseCubePairEnvelope_ne_top
    (ENNReal.tsum_le_tsum
      (quarticSquareBlockShiftedCoordinateModelFailureCharge_le_pairEnvelope
        mdp hhorizon))

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- A model tail after `n+1`, charged by one squared-checkpoint block, is the shifted coordinate row. -/
theorem quarticSquareBlockWeight_mul_tailModelFailureBudget_eq_tsum_shiftedCoordinateCharge
    (mdp : MDP State Action) (n : Nat) :
    (explicitHighProbabilityQuarticSquareBlockWeight n : ENNReal) *
        selfConsistentScheduledCausalTailModelFailureBudget mdp (n + 1) =
      ∑' j : Nat,
        quarticSquareBlockShiftedCoordinateModelFailureCharge mdp (n, j) := by
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
  unfold quarticSquareBlockShiftedCoordinateModelFailureCharge
  congr 2
  omega

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- Squared-checkpoint block weights are summable against the exact infinite model-tail budgets. -/
theorem tsum_quarticSquareBlockWeight_mul_tailModelFailureBudget_ne_top
    (mdp : MDP State Action) (hhorizon : 4 < mdp.horizon) :
    Ne (∑' n : Nat,
      (explicitHighProbabilityQuarticSquareBlockWeight n : ENNReal) *
        selfConsistentScheduledCausalTailModelFailureBudget mdp (n + 1)) ∞ := by
  rw [show (fun n : Nat =>
      (explicitHighProbabilityQuarticSquareBlockWeight n : ENNReal) *
        selfConsistentScheduledCausalTailModelFailureBudget mdp (n + 1)) =
      fun n => ∑' j : Nat,
        quarticSquareBlockShiftedCoordinateModelFailureCharge mdp (n, j) by
    funext n
    exact
      quarticSquareBlockWeight_mul_tailModelFailureBudget_eq_tsum_shiftedCoordinateCharge
        mdp n]
  rw [← ENNReal.tsum_prod']
  exact tsum_quarticSquareBlockShiftedCoordinateModelFailureCharge_ne_top
    mdp hhorizon

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- A seventh-degree squared-checkpoint weight times the exponential return share is summable. -/
theorem summable_quarticSquareBlockWeight_mul_explicitHighProbabilityReturnDelta :
    Summable (fun n : Nat =>
      ((explicitHighProbabilityQuarticSquareBlockWeight n : Nat) : Real) *
        explicitHighProbabilityReturnDelta n) := by
  let base : Nat -> Real := fun n =>
    (n : Real) ^ 7 * Real.exp (-(1 : Real) * (n : Real))
  have hbase : Summable base := by
    simpa [base] using
      (Real.summable_pow_mul_exp_neg_nat_mul 7
        (by norm_num : (0 : Real) < 1))
  have hshift : Summable (fun n : Nat => base (n + 2)) :=
    (summable_nat_add_iff (f := base) 2).2 hbase
  have hscaled := hshift.mul_left (16 * Real.exp 1)
  apply hscaled.congr
  intro n
  unfold base explicitHighProbabilityQuarticSquareBlockWeight
    explicitHighProbabilityReturnDelta explicitHighProbabilityScale
  push_cast
  calc
    (16 * Real.exp 1) *
          (((n : Real) + 2) ^ 7 *
            Real.exp (-(1 : Real) * ((n : Real) + 2))) =
        16 * ((n : Real) + 2) ^ 7 *
          (Real.exp 1 *
            Real.exp (-(1 : Real) * ((n : Real) + 2))) := by ring
    _ = 16 * ((n : Real) + 2) ^ 7 *
          Real.exp (-(n : Real) - 1) := by
      rw [← Real.exp_add 1 (-(1 : Real) * ((n : Real) + 2))]
      congr 2
      ring
    _ = 16 * ((n : Real) + 2) ^ 7 *
          Real.exp (-((n : Real) + 1)) := by ring

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The exact return shares have finite total mass after squared-checkpoint charging. -/
theorem tsum_quarticSquareBlockWeight_mul_explicitHighProbabilityReturnDelta_ne_top :
    Ne (∑' n : Nat,
      (explicitHighProbabilityQuarticSquareBlockWeight n : ENNReal) *
        ENNReal.ofReal (explicitHighProbabilityReturnDelta n)) ∞ := by
  have hfinite :=
    summable_quarticSquareBlockWeight_mul_explicitHighProbabilityReturnDelta.tsum_ofReal_ne_top
  convert hfinite using 1
  apply tsum_congr
  intro n
  rw [← ENNReal.ofReal_natCast
      (explicitHighProbabilityQuarticSquareBlockWeight n),
    ← ENNReal.ofReal_mul (by positivity :
      (0 : Real) <=
        ((explicitHighProbabilityQuarticSquareBlockWeight n : Nat) : Real))]

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The exact checkpoint violation budgets remain summable after squared-checkpoint charging. -/
theorem tsum_quarticSquareBlockWeight_mul_explicitPolynomialPrefixTailModelReturnFailureBudget_ne_top
    (mdp : MDP State Action) (hhorizon : 4 < mdp.horizon) :
    Ne (∑' n : Nat,
      (explicitHighProbabilityQuarticSquareBlockWeight n : ENNReal) *
        explicitPolynomialPrefixTailModelReturnFailureBudget mdp n) ∞ := by
  have hmodel :=
    tsum_quarticSquareBlockWeight_mul_tailModelFailureBudget_ne_top
      mdp hhorizon
  have hreturn :=
    tsum_quarticSquareBlockWeight_mul_explicitHighProbabilityReturnDelta_ne_top
  unfold explicitPolynomialPrefixTailModelReturnFailureBudget
    selfConsistentScheduledNaturalCausalBurninTailModelReturnFailureBudget
    explicitHighProbabilityBurnin
  simp_rw [mul_add]
  rw [ENNReal.tsum_add]
  exact ENNReal.add_ne_top.mpr ⟨hmodel, hreturn⟩

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- Seventh-degree weights dominate every finite telescope of squared checkpoint values. -/
theorem explicitHighProbabilityRounds_add_square_le_add_sum_Ico_quarticSquareBlockWeight
    (start width : Nat) :
    (explicitHighProbabilityRounds (start + width) + 1) ^ 2 <=
      (explicitHighProbabilityRounds start + 1) ^ 2 +
        (Finset.Ico start (start + width)).sum
          explicitHighProbabilityQuarticSquareBlockWeight := by
  induction width with
  | zero => simp
  | succ width ih =>
      have hmonoBase :
          explicitHighProbabilityRounds (start + width) + 1 <=
            explicitHighProbabilityRounds (start + width + 1) + 1 := by
        exact Nat.succ_le_succ
          (explicitHighProbabilityRounds_mono (by omega))
      have hmonoSquare :
          (explicitHighProbabilityRounds (start + width) + 1) ^ 2 <=
            (explicitHighProbabilityRounds (start + width + 1) + 1) ^ 2 :=
        Nat.pow_le_pow_left hmonoBase 2
      have hstep :
          (explicitHighProbabilityRounds (start + width + 1) + 1) ^ 2 <=
            (explicitHighProbabilityRounds (start + width) + 1) ^ 2 +
              explicitHighProbabilityQuarticSquareBlockWeight
                (start + width) := by
        have hgap :=
          explicitHighProbabilityRounds_succ_square_sub_le_quarticSquareBlockWeight
            (start + width)
        omega
      rw [show start + (width + 1) = start + width + 1 by omega,
        Finset.sum_Ico_succ_top (by omega : start <= start + width)]
      calc
        (explicitHighProbabilityRounds (start + width + 1) + 1) ^ 2 <=
            (explicitHighProbabilityRounds (start + width) + 1) ^ 2 +
              explicitHighProbabilityQuarticSquareBlockWeight
                (start + width) := hstep
        _ <= ((explicitHighProbabilityRounds start + 1) ^ 2 +
              (Finset.Ico start (start + width)).sum
                explicitHighProbabilityQuarticSquareBlockWeight) +
              explicitHighProbabilityQuarticSquareBlockWeight
                (start + width) := Nat.add_le_add_right ih _
        _ = (explicitHighProbabilityRounds start + 1) ^ 2 +
            ((Finset.Ico start (start + width)).sum
                explicitHighProbabilityQuarticSquareBlockWeight +
              explicitHighProbabilityQuarticSquareBlockWeight
                (start + width)) := by omega

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- The square of a finite natural time is paid for by an initial squared checkpoint plus preceding delayed blocks. -/
theorem natCast_succ_square_le_checkpoint_square_add_tsum_quarticSquareBlockWeight_of_delayed
    (start time : Nat) :
    (((time + 1) ^ 2 : Nat) : ENNReal) <=
      (((explicitHighProbabilityRounds start + 1) ^ 2 : Nat) : ENNReal) +
        ∑' n : Nat,
          if start <= n ∧ explicitHighProbabilityRounds n < time then
            (explicitHighProbabilityQuarticSquareBlockWeight n : ENNReal)
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
  have hsquareCover :
      (time + 1) ^ 2 <=
        (explicitHighProbabilityRounds (start + width) + 1) ^ 2 :=
    Nat.pow_le_pow_left (Nat.succ_le_succ hcover) 2
  by_cases hwidth : width = 0
  · rw [hwidth, Nat.add_zero] at hsquareCover
    have hcast :
        (((time + 1) ^ 2 : Nat) : ENNReal) <=
          (((explicitHighProbabilityRounds start + 1) ^ 2 : Nat) : ENNReal) := by
      exact_mod_cast hsquareCover
    calc
      (((time + 1) ^ 2 : Nat) : ENNReal) <=
          (((explicitHighProbabilityRounds start + 1) ^ 2 : Nat) : ENNReal) :=
        hcast
      _ <= (((explicitHighProbabilityRounds start + 1) ^ 2 : Nat) : ENNReal) +
          ∑' n : Nat,
            if start <= n ∧ explicitHighProbabilityRounds n < time then
              (explicitHighProbabilityQuarticSquareBlockWeight n : ENNReal)
            else 0 := le_add_right le_rfl
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
            explicitHighProbabilityQuarticSquareBlockWeight : Nat) : ENNReal) <=
          ∑' n : Nat,
            if start <= n ∧ explicitHighProbabilityRounds n < time then
              (explicitHighProbabilityQuarticSquareBlockWeight n : ENNReal)
            else 0 := by
      calc
        (((Finset.Ico start (start + width)).sum
              explicitHighProbabilityQuarticSquareBlockWeight : Nat) : ENNReal) =
            ∑ n ∈ Finset.Ico start (start + width),
              (if start <= n ∧ explicitHighProbabilityRounds n < time then
                (explicitHighProbabilityQuarticSquareBlockWeight n : ENNReal)
              else 0) := by
          calc
            (((Finset.Ico start (start + width)).sum
                explicitHighProbabilityQuarticSquareBlockWeight : Nat) : ENNReal) =
                ∑ n ∈ Finset.Ico start (start + width),
                  (explicitHighProbabilityQuarticSquareBlockWeight n : ENNReal) := by
              exact_mod_cast rfl
            _ = ∑ n ∈ Finset.Ico start (start + width),
                (if start <= n ∧ explicitHighProbabilityRounds n < time then
                  (explicitHighProbabilityQuarticSquareBlockWeight n : ENNReal)
                else 0) := by
              apply Finset.sum_congr rfl
              intro n hn
              simp [hdelayed n hn]
        _ <= ∑' n : Nat,
              if start <= n ∧ explicitHighProbabilityRounds n < time then
                (explicitHighProbabilityQuarticSquareBlockWeight n : ENNReal)
              else 0 := ENNReal.sum_le_tsum _
    have htelescope :=
      explicitHighProbabilityRounds_add_square_le_add_sum_Ico_quarticSquareBlockWeight
        start width
    calc
      (((time + 1) ^ 2 : Nat) : ENNReal) <=
          (((explicitHighProbabilityRounds (start + width) + 1) ^ 2 : Nat) : ENNReal) := by
        exact_mod_cast hsquareCover
      _ <= (((explicitHighProbabilityRounds start + 1) ^ 2 +
            (Finset.Ico start (start + width)).sum
              explicitHighProbabilityQuarticSquareBlockWeight : Nat) : ENNReal) := by
        exact_mod_cast htelescope
      _ = (((explicitHighProbabilityRounds start + 1) ^ 2 : Nat) : ENNReal) +
          (((Finset.Ico start (start + width)).sum
            explicitHighProbabilityQuarticSquareBlockWeight : Nat) : ENNReal) := by
        rw [Nat.cast_add]
      _ <= (((explicitHighProbabilityRounds start + 1) ^ 2 : Nat) : ENNReal) +
          ∑' n : Nat,
            if start <= n ∧ explicitHighProbabilityRounds n < time then
              (explicitHighProbabilityQuarticSquareBlockWeight n : ENNReal)
            else 0 := add_le_add le_rfl hsum

/-- A deterministic checkpoint after which the scheduled regret envelope is
below the fixed inverse-square-root first-passage threshold. -/
theorem exists_inverseSqrtThresholdUnboundedHittingAfterTailStart
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (scheduleIndex : Nat) :
    ∃ start : Nat,
      scheduleIndex <= start ∧
        ∀ n, start <= n ->
          explicitPolynomialPrefixAverageRealizedBehaviorRegretRate
              mdp varianceProxy baseVisitFloor n <=
            selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold
              scheduleIndex := by
  have hrateEventually :=
    (explicitPolynomialPrefixAverageRealizedBehaviorRegretRate_tendsto_zero
      mdp varianceProxy baseVisitFloor).eventually_lt_const
        (selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold_pos
          scheduleIndex)
  obtain ⟨rateStart, hrateStart⟩ := Filter.eventually_atTop.1 hrateEventually
  refine ⟨max scheduleIndex rateStart, le_max_left _ _, ?_⟩
  intro n hn
  exact (hrateStart n ((le_max_right _ _).trans hn)).le

/-- Canonical deterministic witness for the eventual delayed-checkpoint tail
bound at a fixed inverse-square-root threshold index. -/
noncomputable def inverseSqrtThresholdUnboundedHittingAfterTailStart
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (scheduleIndex : Nat) : Nat := by
  classical
  exact Nat.find
    (exists_inverseSqrtThresholdUnboundedHittingAfterTailStart
      mdp varianceProxy baseVisitFloor scheduleIndex)

/-- The canonical tail start is beyond the threshold index and validates the
scheduled regret-rate comparison at every later checkpoint. -/
theorem inverseSqrtThresholdUnboundedHittingAfterTailStart_spec
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (scheduleIndex : Nat) :
    scheduleIndex <=
        inverseSqrtThresholdUnboundedHittingAfterTailStart
          mdp varianceProxy baseVisitFloor scheduleIndex ∧
      ∀ n,
        inverseSqrtThresholdUnboundedHittingAfterTailStart
              mdp varianceProxy baseVisitFloor scheduleIndex <= n ->
          explicitPolynomialPrefixAverageRealizedBehaviorRegretRate
              mdp varianceProxy baseVisitFloor n <=
            selfConsistentScheduledNaturalCausalInverseSqrtFirstPassageThreshold
              scheduleIndex := by
  classical
  exact Nat.find_spec
    (exists_inverseSqrtThresholdUnboundedHittingAfterTailStart
      mdp varianceProxy baseVisitFloor scheduleIndex)

/-- Explicit deterministic ENNReal budget for the second moment of the
successor round count at the uncapped inverse-square-root hitting time. -/
noncomputable def
    inverseSqrtThresholdUnboundedHittingAfterStoppingRoundSecondMomentENNRealBudget
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (scheduleIndex : Nat) : ENNReal :=
  let start := inverseSqrtThresholdUnboundedHittingAfterTailStart
    mdp varianceProxy baseVisitFloor scheduleIndex
  (((explicitHighProbabilityRounds start + 1) ^ 2 : Nat) : ENNReal) +
    ∑' n : Nat,
      (explicitHighProbabilityQuarticSquareBlockWeight n : ENNReal) *
        explicitPolynomialPrefixTailModelReturnFailureBudget mdp n

/-- The deterministic stopping-round second-moment budget is finite whenever
the horizon supplies the inverse-tenth confidence exponent. -/
theorem
    inverseSqrtThresholdUnboundedHittingAfterStoppingRoundSecondMomentENNRealBudget_ne_top
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (scheduleIndex : Nat)
    (hhorizon : 4 < mdp.horizon) :
    inverseSqrtThresholdUnboundedHittingAfterStoppingRoundSecondMomentENNRealBudget
        mdp varianceProxy baseVisitFloor scheduleIndex ≠ ∞ := by
  unfold
    inverseSqrtThresholdUnboundedHittingAfterStoppingRoundSecondMomentENNRealBudget
  rw [ENNReal.add_ne_top]
  exact ⟨by simp,
    tsum_quarticSquareBlockWeight_mul_explicitPolynomialPrefixTailModelReturnFailureBudget_ne_top
      mdp hhorizon⟩

/-- Real-valued form of the deterministic stopping-round second-moment
budget. -/
noncomputable def
    inverseSqrtThresholdUnboundedHittingAfterStoppingRoundSecondMomentBudget
    (mdp : MDP State Action) (varianceProxy : NNReal)
    (baseVisitFloor : Real) (scheduleIndex : Nat) : Real :=
  (inverseSqrtThresholdUnboundedHittingAfterStoppingRoundSecondMomentENNRealBudget
    mdp varianceProxy baseVisitFloor scheduleIndex).toReal

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- A pointwise delayed-checkpoint tail budget gives an explicit ENNReal
upper bound for the successor stopping-round second moment. -/
theorem lintegral_sq_untopA_add_one_le_quarticSquareCheckpointBudget
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (tau : Omega -> WithTop Nat) (htau : Measurable tau)
    (budget : Nat -> ENNReal) (start : Nat)
    (htailStart : ∀ n, start <= n ->
      mu {omega |
        (explicitHighProbabilityRounds n : WithTop Nat) < tau omega} <=
          budget n) :
    ∫⁻ omega,
        ENNReal.ofReal (((((tau omega).untopA + 1 : Nat) : Real)) ^ 2) ∂mu <=
      (((explicitHighProbabilityRounds start + 1) ^ 2 : Nat) : ENNReal) +
        ∑' n : Nat,
          (explicitHighProbabilityQuarticSquareBlockWeight n : ENNReal) *
            budget n := by
  let delayed : Nat -> Set Omega := fun n =>
    {omega | (explicitHighProbabilityRounds n : WithTop Nat) < tau omega}
  have hdelayedMeasurable (n : Nat) : MeasurableSet (delayed n) := by
    exact measurableSet_lt measurable_const htau
  let term : Nat -> Omega -> ENNReal := fun n =>
    if start <= n then
      (delayed n).indicator
        (fun _ =>
          (explicitHighProbabilityQuarticSquareBlockWeight n : ENNReal))
    else fun _ => 0
  have htermMeasurable (n : Nat) : AEMeasurable (term n) mu := by
    by_cases hn : start <= n
    · simp only [term, hn, if_true]
      exact (Measurable.indicator measurable_const
        (hdelayedMeasurable n)).aemeasurable
    · simp only [term, hn, if_false]
      exact measurable_const.aemeasurable
  have hpoint (omega : Omega) :
      ENNReal.ofReal
          (((((tau omega).untopA + 1 : Nat) : Real)) ^ 2) <=
        (((explicitHighProbabilityRounds start + 1) ^ 2 : Nat) : ENNReal) +
          ∑' n : Nat, term n omega := by
    have hnat :=
      natCast_succ_square_le_checkpoint_square_add_tsum_quarticSquareBlockWeight_of_delayed
        start (tau omega).untopA
    calc
      ENNReal.ofReal
          (((((tau omega).untopA + 1 : Nat) : Real)) ^ 2) =
          ((((tau omega).untopA + 1) ^ 2 : Nat) : ENNReal) := by
        rw [ENNReal.ofReal_pow (by positivity) 2,
          ENNReal.ofReal_natCast]
        norm_cast
      _ <= (((explicitHighProbabilityRounds start + 1) ^ 2 : Nat) : ENNReal) +
          ∑' n : Nat,
            if start <= n ∧
                explicitHighProbabilityRounds n < (tau omega).untopA then
              (explicitHighProbabilityQuarticSquareBlockWeight n : ENNReal)
            else 0 := hnat
      _ <= (((explicitHighProbabilityRounds start + 1) ^ 2 : Nat) : ENNReal) +
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
        (explicitHighProbabilityQuarticSquareBlockWeight n : ENNReal) *
          budget n := by
    by_cases hn : start <= n
    · have htailN : mu (delayed n) <= budget n := by
        simpa [delayed] using htailStart n hn
      simp only [term, hn, if_true]
      rw [lintegral_indicator_const (hdelayedMeasurable n)]
      gcongr
    · simp [term, hn]
  calc
    ∫⁻ omega,
        ENNReal.ofReal (((((tau omega).untopA + 1 : Nat) : Real)) ^ 2) ∂mu <=
        ∫⁻ omega,
          ((((explicitHighProbabilityRounds start + 1) ^ 2 : Nat) : ENNReal) +
            ∑' n : Nat, term n omega) ∂mu := lintegral_mono hpoint
    _ <= (((explicitHighProbabilityRounds start + 1) ^ 2 : Nat) : ENNReal) +
          ∑' n : Nat,
            (explicitHighProbabilityQuarticSquareBlockWeight n : ENNReal) *
              budget n := by
      rw [lintegral_add_left measurable_const, lintegral_const,
        lintegral_tsum htermMeasurable]
      simp only [IsProbabilityMeasure.measure_univ, mul_one]
      exact add_le_add le_rfl (ENNReal.tsum_le_tsum htermIntegral)

omit [DecidableEq State] [DecidableEq Action]
    [MeasurableSingletonClass State] [MeasurableSingletonClass Action]
    [Nonempty State] [Nonempty Action] in
/-- Eventually summable squared fourth-power checkpoint crossing tails imply a finite second moment. -/
theorem memLp_two_untopA_add_one_of_eventually_quarticSquareCheckpointTail
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (tau : Omega -> WithTop Nat) (htau : Measurable tau)
    (budget : Nat -> ENNReal)
    (hbudget : Ne (∑' n : Nat,
      (explicitHighProbabilityQuarticSquareBlockWeight n : ENNReal) *
        budget n) ∞)
    (htail : ∀ᶠ n : Nat in atTop,
      mu {omega |
        (explicitHighProbabilityRounds n : WithTop Nat) < tau omega} <=
          budget n) :
    MemLp (fun omega => (((tau omega).untopA + 1 : Nat) : Real)) 2 mu := by
  obtain ⟨start, htailStart⟩ := Filter.eventually_atTop.1 htail
  let delayed : Nat -> Set Omega := fun n =>
    {omega | (explicitHighProbabilityRounds n : WithTop Nat) < tau omega}
  have hdelayedMeasurable (n : Nat) : MeasurableSet (delayed n) := by
    exact measurableSet_lt measurable_const htau
  let term : Nat -> Omega -> ENNReal := fun n =>
    if start <= n then
      (delayed n).indicator
        (fun _ =>
          (explicitHighProbabilityQuarticSquareBlockWeight n : ENNReal))
    else fun _ => 0
  have htermMeasurable (n : Nat) : AEMeasurable (term n) mu := by
    by_cases hn : start <= n
    · simp only [term, hn, if_true]
      exact (Measurable.indicator measurable_const
        (hdelayedMeasurable n)).aemeasurable
    · simp only [term, hn, if_false]
      exact measurable_const.aemeasurable
  have hpoint (omega : Omega) :
      ENNReal.ofReal
          (((((tau omega).untopA + 1 : Nat) : Real)) ^ 2) <=
        (((explicitHighProbabilityRounds start + 1) ^ 2 : Nat) : ENNReal) +
          ∑' n : Nat, term n omega := by
    have hnat :=
      natCast_succ_square_le_checkpoint_square_add_tsum_quarticSquareBlockWeight_of_delayed
        start (tau omega).untopA
    calc
      ENNReal.ofReal
          (((((tau omega).untopA + 1 : Nat) : Real)) ^ 2) =
          ((((tau omega).untopA + 1) ^ 2 : Nat) : ENNReal) := by
        rw [ENNReal.ofReal_pow (by positivity) 2,
          ENNReal.ofReal_natCast]
        norm_cast
      _ <= (((explicitHighProbabilityRounds start + 1) ^ 2 : Nat) : ENNReal) +
          ∑' n : Nat,
            if start <= n ∧
                explicitHighProbabilityRounds n < (tau omega).untopA then
              (explicitHighProbabilityQuarticSquareBlockWeight n : ENNReal)
            else 0 := hnat
      _ <= (((explicitHighProbabilityRounds start + 1) ^ 2 : Nat) : ENNReal) +
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
        (explicitHighProbabilityQuarticSquareBlockWeight n : ENNReal) *
          budget n := by
    by_cases hn : start <= n
    · have htailN : mu (delayed n) <= budget n := by
        simpa [delayed] using htailStart n hn
      simp only [term, hn, if_true]
      rw [lintegral_indicator_const (hdelayedMeasurable n)]
      gcongr
    · simp [term, hn]
  have hdomIntegral :
      ∫⁻ omega,
          ((((explicitHighProbabilityRounds start + 1) ^ 2 : Nat) :
              ENNReal) + ∑' n : Nat, term n omega) ∂mu <=
        (((explicitHighProbabilityRounds start + 1) ^ 2 : Nat) : ENNReal) +
          ∑' n : Nat,
            (explicitHighProbabilityQuarticSquareBlockWeight n : ENNReal) *
              budget n := by
    rw [lintegral_add_left measurable_const, lintegral_const,
      lintegral_tsum htermMeasurable]
    simp only [IsProbabilityMeasure.measure_univ, mul_one]
    exact add_le_add le_rfl (ENNReal.tsum_le_tsum htermIntegral)
  have hrhsFinite :
      (((explicitHighProbabilityRounds start + 1) ^ 2 : Nat) : ENNReal) +
          ∑' n : Nat,
            (explicitHighProbabilityQuarticSquareBlockWeight n : ENNReal) *
              budget n < ∞ := by
    rw [ENNReal.add_lt_top]
    exact ⟨by simp, lt_top_iff_ne_top.mpr hbudget⟩
  have hmeasurable : Measurable
      (fun omega => (((tau omega).untopA + 1 : Nat) : Real)) :=
    (measurable_of_countable
      (fun count : Nat => (((count + 1 : Nat) : Nat) : Real))).comp
        htau.untopA
  apply (memLp_two_iff_integrable_sq
    hmeasurable.aestronglyMeasurable).2
  refine ⟨(hmeasurable.pow_const 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall fun _ => by positivity)]
  exact lt_of_le_of_lt
    (lintegral_mono hpoint |>.trans hdomIntegral) hrhsFinite

/-- From the canonical tail start onward, every delayed uncapped first-passage
checkpoint has the exact compiled model/return failure budget. -/
theorem
    selfConsistentScheduledCausalSource_trajectoryMeasure_inverseSqrtThresholdUnboundedHittingAfterDelayedCheckpointSet_le_of_tailStart
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
    (scheduleIndex checkpointIndex : Nat)
    (hcheckpointIndex :
      inverseSqrtThresholdUnboundedHittingAfterTailStart
          mdp varianceProxy baseVisitFloor scheduleIndex <= checkpointIndex) :
    let source := selfConsistentScheduledCausalSource mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
    source.trajectoryMeasure
        (selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterDelayedCheckpointSet
          mdp initialState rewardSource initialTable defaultState varianceProxy
            baseVisitFloor scheduleIndex checkpointIndex) <=
      explicitPolynomialPrefixTailModelReturnFailureBudget mdp
        checkpointIndex := by
  dsimp only
  have hstart :=
    inverseSqrtThresholdUnboundedHittingAfterTailStart_spec
      mdp varianceProxy baseVisitFloor scheduleIndex
  have hindex : scheduleIndex <= checkpointIndex :=
    hstart.1.trans hcheckpointIndex
  have hrate := hstart.2 checkpointIndex hcheckpointIndex
  have hsubset :=
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterDelayedCheckpointSet_subset_explicitPolynomialPrefixAverageRealizedBehaviorRegretViolationSet
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor hindex hrate
  have hcert :=
    selfConsistentScheduledCausalSource_explicitPolynomialPrefixHighProbabilityAverageRealizedBehaviorRegretConsistency
      mdp initialState rewardSource varianceProxy hvarianceProxy law
        initialTable defaultState support baseVisitFloor hbaseFloor
          hrewardBound hhorizon hbaseVisitFloor
  dsimp only at hcert
  rcases hcert with
    ⟨_hbudgetTendsto, _hrateTendsto, _hbudgetEventually, hcheckpoint⟩
  rcases hcheckpoint checkpointIndex with
    ⟨_heventMeasurable, _hviolationMeasurable, _heventMeasure,
      _hviolationSubset, hviolationMeasure, _hstrict, _hpath⟩
  exact (measure_mono hsubset).trans hviolationMeasure

/-- The actual successor stopping-round square has an explicit deterministic
ENNReal upper bound at every fixed inverse-square-root threshold index. -/
theorem
    selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_lintegral_stoppingRound_sq_le_ENNRealBudget
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
    let tau :=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor scheduleIndex
    ∫⁻ trajectory,
        ENNReal.ofReal (((((tau trajectory).untopA + 1 : Nat) : Real)) ^ 2)
          ∂source.trajectoryMeasure <=
      inverseSqrtThresholdUnboundedHittingAfterStoppingRoundSecondMomentENNRealBudget
        mdp varianceProxy baseVisitFloor scheduleIndex := by
  dsimp only
  apply lintegral_sq_untopA_add_one_le_quarticSquareCheckpointBudget
    (selfConsistentScheduledCausalSource mdp initialState rewardSource
      initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure
    (selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor scheduleIndex)
    (selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix_isStoppingTime
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor scheduleIndex).measurable'
    (explicitPolynomialPrefixTailModelReturnFailureBudget mdp)
    (inverseSqrtThresholdUnboundedHittingAfterTailStart
      mdp varianceProxy baseVisitFloor scheduleIndex)
  intro checkpointIndex hcheckpointIndex
  exact
    selfConsistentScheduledCausalSource_trajectoryMeasure_inverseSqrtThresholdUnboundedHittingAfterDelayedCheckpointSet_le_of_tailStart
      mdp initialState rewardSource varianceProxy hvarianceProxy law
        initialTable defaultState support baseVisitFloor hbaseFloor
          hrewardBound hhorizon hbaseVisitFloor scheduleIndex checkpointIndex
            hcheckpointIndex

/-- Each fixed-index genuine uncapped inverse-square-root first passage has a
finite second moment when the finite-horizon confidence exponent is at least ten. -/
theorem
    selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_squareIntegrableFiniteStoppingTime
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
    (hhorizon : 4 < mdp.horizon) (hbaseVisitFloor : 0 < baseVisitFloor)
    (scheduleIndex : Nat) :
    let source := selfConsistentScheduledCausalSource mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
    BanditRLProof.OFUL.SquareIntegrableFiniteStoppingTime
      source.trajectoryMeasure
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
            hrewardBound (by omega) hbaseVisitFloor scheduleIndex
  · apply memLp_two_untopA_add_one_of_eventually_quarticSquareCheckpointTail
      (selfConsistentScheduledCausalSource mdp initialState rewardSource
        initialTable defaultState varianceProxy baseVisitFloor).trajectoryMeasure
      tau
      (selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix_isStoppingTime
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor scheduleIndex).measurable'
      (explicitPolynomialPrefixTailModelReturnFailureBudget mdp)
      (tsum_quarticSquareBlockWeight_mul_explicitPolynomialPrefixTailModelReturnFailureBudget_ne_top
        mdp hhorizon)
    exact
      eventually_selfConsistentScheduledCausalSource_trajectoryMeasure_inverseSqrtThresholdUnboundedHittingAfterDelayedCheckpointSet_le
        mdp initialState rewardSource varianceProxy hvarianceProxy law
          initialTable defaultState support baseVisitFloor hbaseFloor
            hrewardBound (by omega) hbaseVisitFloor scheduleIndex

/-- The Bochner second moment of the actual successor stopping-round count is
bounded by the canonical deterministic checkpoint/failure budget. -/
theorem
    selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_integral_stoppingRound_sq_le_budget
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
    (hhorizon : 4 < mdp.horizon) (hbaseVisitFloor : 0 < baseVisitFloor)
    (scheduleIndex : Nat) :
    let source := selfConsistentScheduledCausalSource mdp initialState
      rewardSource initialTable defaultState varianceProxy baseVisitFloor
    let tau :=
      selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
        mdp initialState rewardSource initialTable defaultState varianceProxy
          baseVisitFloor scheduleIndex
    integral source.trajectoryMeasure
        (fun trajectory =>
          ((((tau trajectory).untopA + 1 : Nat) : Real)) ^ 2) <=
      inverseSqrtThresholdUnboundedHittingAfterStoppingRoundSecondMomentBudget
        mdp varianceProxy baseVisitFloor scheduleIndex := by
  dsimp only
  let source := selfConsistentScheduledCausalSource mdp initialState
    rewardSource initialTable defaultState varianceProxy baseVisitFloor
  let tau :=
    selfConsistentScheduledNaturalCausalInverseSqrtThresholdUnboundedHittingAfterStoppingPrefix
      mdp initialState rewardSource initialTable defaultState varianceProxy
        baseVisitFloor scheduleIndex
  change integral source.trajectoryMeasure
      (fun trajectory =>
        ((((tau trajectory).untopA + 1 : Nat) : Real)) ^ 2) <=
    inverseSqrtThresholdUnboundedHittingAfterStoppingRoundSecondMomentBudget
      mdp varianceProxy baseVisitFloor scheduleIndex
  have hstop : BanditRLProof.OFUL.SquareIntegrableFiniteStoppingTime
      source.trajectoryMeasure tau := by
    simpa [source, tau] using
      (selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_squareIntegrableFiniteStoppingTime
        mdp initialState rewardSource varianceProxy hvarianceProxy law
          initialTable defaultState support baseVisitFloor hbaseFloor
            hrewardBound hhorizon hbaseVisitFloor scheduleIndex)
  have hlin :
      ∫⁻ trajectory,
          ENNReal.ofReal
            (((((tau trajectory).untopA + 1 : Nat) : Real)) ^ 2)
          ∂source.trajectoryMeasure <=
        inverseSqrtThresholdUnboundedHittingAfterStoppingRoundSecondMomentENNRealBudget
          mdp varianceProxy baseVisitFloor scheduleIndex := by
    simpa [source, tau] using
      (selfConsistentScheduledCausalSource_inverseSqrtThresholdUnboundedHittingAfter_lintegral_stoppingRound_sq_le_ENNRealBudget
        mdp initialState rewardSource varianceProxy hvarianceProxy law
          initialTable defaultState support baseVisitFloor hbaseFloor
            hrewardBound (by omega) hbaseVisitFloor scheduleIndex)
  unfold
    inverseSqrtThresholdUnboundedHittingAfterStoppingRoundSecondMomentBudget
  calc
    integral source.trajectoryMeasure
        (fun trajectory =>
          ((((tau trajectory).untopA + 1 : Nat) : Real)) ^ 2) =
      (∫⁻ trajectory,
          ENNReal.ofReal
            (((((tau trajectory).untopA + 1 : Nat) : Real)) ^ 2)
          ∂source.trajectoryMeasure).toReal := by
        exact integral_eq_lintegral_of_nonneg_ae
          (Filter.Eventually.of_forall fun _ => sq_nonneg _)
          hstop.memLp_rounds.integrable_sq.aestronglyMeasurable
    _ <=
      (inverseSqrtThresholdUnboundedHittingAfterStoppingRoundSecondMomentENNRealBudget
        mdp varianceProxy baseVisitFloor scheduleIndex).toReal := by
      exact ENNReal.toReal_mono
        (inverseSqrtThresholdUnboundedHittingAfterStoppingRoundSecondMomentENNRealBudget_ne_top
          mdp varianceProxy baseVisitFloor scheduleIndex hhorizon)
        hlin

end AdaptiveStochasticSampledEmpiricalOptimisticSource

end BanditRLProof.FiniteHorizonRL
