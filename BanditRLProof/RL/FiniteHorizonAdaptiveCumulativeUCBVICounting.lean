import BanditRLProof.RL.FiniteHorizonAdaptiveCumulativeUCBVIRegretDecomposition
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Batched visit-count summation for recurrent UCBVI-CH

The policy is frozen within each length-`H` episode, so every visit in that
episode uses the same strict-prefix count.  These lemmas retain that batching
exactly: low-count overshoot costs at most one batch, while positive-count
terms telescope through square-root and logarithmic potentials.
-/

open scoped BigOperators

namespace BanditRLProof.FiniteHorizonRL.AdaptiveCumulativeHoeffdingUCBVI

/-- Strict-prefix cumulative mass of a batched nonnegative increment stream. -/
def batchedPrefixCount (increment : Nat -> Nat) (round : Nat) : Nat :=
  ∑ i ∈ Finset.range round, increment i

@[simp] theorem batchedPrefixCount_zero (increment : Nat -> Nat) :
    batchedPrefixCount increment 0 = 0 := by
  simp [batchedPrefixCount]

theorem batchedPrefixCount_succ (increment : Nat -> Nat) (round : Nat) :
    batchedPrefixCount increment (round + 1) =
      batchedPrefixCount increment round + increment round := by
  simp [batchedPrefixCount, Finset.sum_range_succ]

theorem batchedPrefixCount_mono (increment : Nat -> Nat) :
    Monotone (batchedPrefixCount increment) := by
  intro a b hab
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hab)
    (fun _ _ _ => Nat.zero_le _)

private theorem sum_range_forwardDifference (f : Nat -> Real) (rounds : Nat) :
    (∑ round ∈ Finset.range rounds, (f (round + 1) - f round)) =
      f rounds - f 0 := by
  induction rounds with
  | zero => simp
  | succ rounds ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-- All increments whose strict-prefix mass is below a threshold occupy at
most the threshold plus one batch. -/
theorem sum_low_batchedIncrement_le
    (increment : Nat -> Nat) (batch threshold rounds : Nat)
    (hincrement : forall round, increment round <= batch) :
    (∑ round ∈ Finset.range rounds,
      if batchedPrefixCount increment round < threshold then increment round
      else 0) <= threshold + batch := by
  induction rounds with
  | zero => simp
  | succ rounds ih =>
      rw [Finset.sum_range_succ]
      by_cases hlow : batchedPrefixCount increment rounds < threshold
      · rw [if_pos hlow]
        have hprevious :
            (∑ round ∈ Finset.range rounds,
              if batchedPrefixCount increment round < threshold then
                increment round else 0) <= batchedPrefixCount increment rounds := by
          unfold batchedPrefixCount
          apply Finset.sum_le_sum
          intro i hi
          split_ifs
          · exact le_rfl
          · exact Nat.zero_le _
        exact (Nat.add_le_add hprevious (hincrement rounds)).trans
          (Nat.add_le_add_right (Nat.le_of_lt hlow) batch)
      · rw [if_neg hlow]
        exact ih

private theorem batched_ratio_le_two_log_increment
    {mass increment : Nat} (hmass : 0 < mass) (hincrement : increment <= mass) :
    (increment : Real) / mass <=
      2 * (Real.log (mass + increment : Nat) - Real.log mass) := by
  have hmassReal : 0 < (mass : Real) := by exact_mod_cast hmass
  have hnewReal : 0 < ((mass + increment : Nat) : Real) := by positivity
  have hratio : (0 : Real) < ((mass + increment : Nat) : Real) / mass :=
    div_pos hnewReal hmassReal
  have hlog := Real.one_sub_inv_le_log_of_pos hratio
  rw [Real.log_div hnewReal.ne' hmassReal.ne'] at hlog
  have htwice : (increment : Real) / mass <=
      2 * ((increment : Real) / (mass + increment : Nat)) := by
    rw [show 2 * ((increment : Real) / (mass + increment : Nat)) =
        (2 * increment : Real) / (mass + increment : Nat) by ring]
    apply (div_le_div_iff₀ hmassReal hnewReal).2
    norm_num only [Nat.cast_add, Nat.cast_ofNat]
    have hcast : (increment : Real) <= mass := by exact_mod_cast hincrement
    nlinarith
  have hone : 1 - (((mass + increment : Nat) : Real) / mass)⁻¹ =
      (increment : Real) / (mass + increment : Nat) := by
    field_simp
    norm_num
  rw [hone] at hlog
  linarith

/-- High-prefix reciprocal masses telescope into one logarithm. -/
theorem sum_high_batchedRatio_le_log
    (increment : Nat -> Nat) (batch threshold rounds : Nat)
    (hbatch : 0 < batch) (hthreshold : batch <= threshold)
    (hincrement : forall round, increment round <= batch) :
    (∑ round ∈ Finset.range rounds,
      if threshold <= batchedPrefixCount increment round then
        (increment round : Real) / batchedPrefixCount increment round else 0) <=
      2 * Real.log (max 1 (batchedPrefixCount increment rounds) : Nat) := by
  induction rounds with
  | zero => simp
  | succ rounds ih =>
      rw [Finset.sum_range_succ, batchedPrefixCount_succ]
      by_cases hhigh : threshold <= batchedPrefixCount increment rounds
      · rw [if_pos hhigh]
        have hmass : 0 < batchedPrefixCount increment rounds := by omega
        have hincLeMass : increment rounds <= batchedPrefixCount increment rounds :=
          (hincrement rounds).trans (hthreshold.trans hhigh)
        have hstep := batched_ratio_le_two_log_increment hmass hincLeMass
        have hmaxOld : max 1 (batchedPrefixCount increment rounds) =
            batchedPrefixCount increment rounds := max_eq_right (by omega)
        have hmaxNew : max 1
            (batchedPrefixCount increment rounds + increment rounds) =
            batchedPrefixCount increment rounds + increment rounds :=
          max_eq_right (by omega)
        rw [hmaxOld] at ih
        rw [hmaxNew]
        linarith
      · rw [if_neg hhigh]
        have hmaxMono : (max 1 (batchedPrefixCount increment rounds) : Nat) <=
            max 1 (batchedPrefixCount increment rounds + increment rounds) := by
          exact max_le_max_left 1 (Nat.le_add_right _ _)
        have hmaxPos : (0 : Real) <
            (max 1 (batchedPrefixCount increment rounds) : Nat) := by
          positivity
        have hmaxMonoReal :
            ((max 1 (batchedPrefixCount increment rounds) : Nat) : Real) <=
              (max 1 (batchedPrefixCount increment rounds + increment rounds) : Nat) := by
          exact_mod_cast hmaxMono
        have hlogMono := Real.log_le_log
          hmaxPos hmaxMonoReal
        linarith

private theorem batched_inverseSqrt_step
    {mass increment batch : Nat} (hmass : 0 < mass)
    (hincrement : increment <= batch) :
    (increment : Real) / Real.sqrt mass <=
      2 * (Real.sqrt (mass + increment : Nat) - Real.sqrt mass) +
        (batch : Real) * ((increment : Real) / mass) := by
  have hx : 0 < Real.sqrt mass := Real.sqrt_pos.2 (by exact_mod_cast hmass)
  have hxOne : 1 <= Real.sqrt mass := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hmass)
  have hy : 0 <= Real.sqrt (mass + increment : Nat) := Real.sqrt_nonneg _
  have hxy : Real.sqrt mass <= Real.sqrt (mass + increment : Nat) :=
    Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_add_right mass increment)
  have hxsq : Real.sqrt mass ^ 2 = (mass : Real) :=
    Real.sq_sqrt (Nat.cast_nonneg mass)
  have hysq : Real.sqrt (mass + increment : Nat) ^ 2 =
      ((mass + increment : Nat) : Real) :=
    Real.sq_sqrt (Nat.cast_nonneg (mass + increment))
  have hinc : (increment : Real) <= batch := by exact_mod_cast hincrement
  have hprodGlobal :
      (Real.sqrt (mass + increment : Nat) - Real.sqrt mass) *
        (Real.sqrt (mass + increment : Nat) + Real.sqrt mass) =
          (increment : Real) := by
    calc
      _ = Real.sqrt (mass + increment : Nat) ^ 2 -
            Real.sqrt mass ^ 2 := by ring
      _ = (increment : Real) := by
        rw [hysq, hxsq]
        norm_num
  have hfactor : Real.sqrt (mass + increment : Nat) - Real.sqrt mass <=
      (increment : Real) / Real.sqrt mass := by
    apply (le_div_iff₀ hx).2
    have hdiff : 0 <= Real.sqrt (mass + increment : Nat) - Real.sqrt mass :=
      sub_nonneg.mpr hxy
    have hsum : Real.sqrt mass <=
        Real.sqrt (mass + increment : Nat) + Real.sqrt mass := by
      linarith
    have hmul := mul_le_mul_of_nonneg_left hsum hdiff
    rw [hprodGlobal] at hmul
    simpa [mul_comm] using hmul
  have hfactorBatch : Real.sqrt (mass + increment : Nat) - Real.sqrt mass <=
      (batch : Real) := by
    calc
      _ <= (increment : Real) / Real.sqrt mass := hfactor
      _ <= (increment : Real) := by
        exact div_le_self (Nat.cast_nonneg increment) hxOne
      _ <= (batch : Real) := hinc
  let d := Real.sqrt (mass + increment : Nat) - Real.sqrt mass
  have hd : 0 <= d := sub_nonneg.mpr hxy
  have hfactorDiv : d / Real.sqrt mass <=
      (increment : Real) / mass := by
    calc
      d / Real.sqrt mass <=
          ((increment : Real) / Real.sqrt mass) / Real.sqrt mass :=
        (div_le_div_iff_of_pos_right hx).2 (by simpa [d] using hfactor)
      _ = (increment : Real) / mass := by
        rw [div_div, ← pow_two, hxsq]
  have hremainder : d * (d / Real.sqrt mass) <=
      (batch : Real) * ((increment : Real) / mass) :=
    mul_le_mul hfactorBatch hfactorDiv (by positivity) (Nat.cast_nonneg batch)
  have hid : (increment : Real) / Real.sqrt mass =
      2 * d + d * (d / Real.sqrt mass) := by
    apply (div_eq_iff hx.ne').2
    calc
      (increment : Real) = d *
          (Real.sqrt (mass + increment : Nat) + Real.sqrt mass) := by
        simpa [d] using hprodGlobal.symm
      _ = (2 * d + d * (d / Real.sqrt mass)) * Real.sqrt mass := by
        rw [add_mul, mul_assoc d, div_mul_cancel₀ _ hx.ne']
        dsimp [d]
        ring
  rw [hid]
  simpa [d] using add_le_add_left hremainder (2 * d)

/-- Batched inverse-square-root masses retain the leading constant two; all
within-episode staleness is isolated in one low-count batch and one logarithm. -/
theorem sum_positive_batchedInvSqrt_le
    (increment : Nat -> Nat) (batch rounds : Nat)
    (hbatch : 0 < batch)
    (hincrement : forall round, increment round <= batch) :
    (∑ round ∈ Finset.range rounds,
      if batchedPrefixCount increment round = 0 then 0 else
        (increment round : Real) /
          Real.sqrt (batchedPrefixCount increment round)) <=
      2 * Real.sqrt (batchedPrefixCount increment rounds) +
        2 * batch + 2 * batch *
          Real.log ((max 1 (batchedPrefixCount increment rounds) : Nat) : Real) := by
  let low := fun round => batchedPrefixCount increment round < batch
  have hsplit : (∑ round ∈ Finset.range rounds,
      if batchedPrefixCount increment round = 0 then 0 else
        (increment round : Real) / Real.sqrt (batchedPrefixCount increment round)) =
      (∑ round ∈ Finset.range rounds,
        if low round then
          (if batchedPrefixCount increment round = 0 then 0 else
            (increment round : Real) /
              Real.sqrt (batchedPrefixCount increment round)) else 0) +
      (∑ round ∈ Finset.range rounds,
        if batch <= batchedPrefixCount increment round then
          (increment round : Real) /
            Real.sqrt (batchedPrefixCount increment round) else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro round _
    by_cases h : batchedPrefixCount increment round < batch
    · have hnle : ¬ batch <= batchedPrefixCount increment round :=
        Nat.not_le.mpr h
      simp [low, h, hnle]
    · have hge : batch <= batchedPrefixCount increment round :=
        Nat.le_of_not_gt h
      have hne : batchedPrefixCount increment round ≠ 0 := by omega
      simp [low, h, hge, hne]
  rw [hsplit]
  have hlowNat := sum_low_batchedIncrement_le increment batch batch rounds hincrement
  have hlow : (∑ round ∈ Finset.range rounds,
        if low round then
          (if batchedPrefixCount increment round = 0 then 0 else
            (increment round : Real) /
              Real.sqrt (batchedPrefixCount increment round)) else 0) <=
      (2 * batch : Nat) := by
    calc
      _ <= ∑ round ∈ Finset.range rounds,
          if low round then (increment round : Real) else 0 := by
        apply Finset.sum_le_sum
        intro round _
        by_cases hl : low round
        · rw [if_pos hl]
          by_cases hz : batchedPrefixCount increment round = 0
          · simp [hl, hz]
          · rw [if_neg hz]
            have hsqrt : 1 <= Real.sqrt (batchedPrefixCount increment round) := by
              rw [← Real.sqrt_one]
              exact Real.sqrt_le_sqrt (by exact_mod_cast Nat.pos_of_ne_zero hz)
            simpa [hl] using div_le_self (Nat.cast_nonneg (increment round)) hsqrt
        · simp [hl]
      _ <= (2 * batch : Nat) := by
        exact_mod_cast (by simpa [low, two_mul] using hlowNat)
  have hhighStep : (∑ round ∈ Finset.range rounds,
        if batch <= batchedPrefixCount increment round then
          (increment round : Real) /
            Real.sqrt (batchedPrefixCount increment round) else 0) <=
      2 * Real.sqrt (batchedPrefixCount increment rounds) +
        (batch : Real) *
        (∑ round ∈ Finset.range rounds,
            if batch <= batchedPrefixCount increment round then
              (increment round : Real) /
                batchedPrefixCount increment round else 0) := by
    calc
      _ <= ∑ round ∈ Finset.range rounds,
          if batch <= batchedPrefixCount increment round then
            (2 * (Real.sqrt (batchedPrefixCount increment (round + 1)) -
                Real.sqrt (batchedPrefixCount increment round)) +
              (batch : Real) * ((increment round : Real) /
                batchedPrefixCount increment round)) else 0 := by
          apply Finset.sum_le_sum
          intro round _
          by_cases hh : batch <= batchedPrefixCount increment round
          · simp only [if_pos hh]
            rw [batchedPrefixCount_succ]
            exact batched_inverseSqrt_step
              (mass := batchedPrefixCount increment round) (batch := batch)
              (by omega) (hincrement round)
          · simp [hh]
      _ <= 2 * Real.sqrt (batchedPrefixCount increment rounds) +
          (batch : Real) *
            (∑ round ∈ Finset.range rounds,
              if batch <= batchedPrefixCount increment round then
                (increment round : Real) /
                  batchedPrefixCount increment round else 0) := by
          have hdiff : (∑ round ∈ Finset.range rounds,
              if batch <= batchedPrefixCount increment round then
                2 * (Real.sqrt (batchedPrefixCount increment (round + 1)) -
                  Real.sqrt (batchedPrefixCount increment round)) else 0) <=
              2 * Real.sqrt (batchedPrefixCount increment rounds) := by
            calc
              _ <= ∑ round ∈ Finset.range rounds,
                  2 * (Real.sqrt (batchedPrefixCount increment (round + 1)) -
                    Real.sqrt (batchedPrefixCount increment round)) := by
                apply Finset.sum_le_sum
                intro round _
                split_ifs
                · exact le_rfl
                · have hm := batchedPrefixCount_mono increment
                  have hnat := hm (Nat.le_succ round)
                  have hreal : (batchedPrefixCount increment round : Real) <=
                      batchedPrefixCount increment (round + 1) := by
                    exact_mod_cast hnat
                  have hsqrt := Real.sqrt_le_sqrt hreal
                  linarith
              _ = 2 * Real.sqrt (batchedPrefixCount increment rounds) := by
                rw [← Finset.mul_sum]
                have ht := sum_range_forwardDifference
                  (fun round => Real.sqrt (batchedPrefixCount increment round)) rounds
                rw [ht]
                simp
          have hpoint : (∑ round ∈ Finset.range rounds,
              if batch <= batchedPrefixCount increment round then
                (2 * (Real.sqrt (batchedPrefixCount increment (round + 1)) -
                    Real.sqrt (batchedPrefixCount increment round)) +
                  (batch : Real) * ((increment round : Real) /
                    batchedPrefixCount increment round)) else 0) =
              (∑ round ∈ Finset.range rounds,
                if batch <= batchedPrefixCount increment round then
                  2 * (Real.sqrt (batchedPrefixCount increment (round + 1)) -
                    Real.sqrt (batchedPrefixCount increment round)) else 0) +
              (∑ round ∈ Finset.range rounds,
                if batch <= batchedPrefixCount increment round then
                  (batch : Real) * ((increment round : Real) /
                    batchedPrefixCount increment round) else 0) := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro round _
            split_ifs <;> simp
          rw [hpoint]
          have hsecond : (∑ round ∈ Finset.range rounds,
                if batch <= batchedPrefixCount increment round then
                  (batch : Real) * ((increment round : Real) /
                    batchedPrefixCount increment round) else 0) =
              (batch : Real) *
                (∑ round ∈ Finset.range rounds,
                  if batch <= batchedPrefixCount increment round then
                    (increment round : Real) /
                      batchedPrefixCount increment round else 0) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro round _
            split_ifs <;> simp
          rw [hsecond]
          simpa [add_comm, add_left_comm] using
            add_le_add_right hdiff
              ((batch : Real) *
                (∑ round ∈ Finset.range rounds,
                  if batch <= batchedPrefixCount increment round then
                    (increment round : Real) /
                      batchedPrefixCount increment round else 0))
  have hratio := sum_high_batchedRatio_le_log increment batch batch rounds
    hbatch le_rfl hincrement
  have hbatchNonneg : (0 : Real) <= batch := Nat.cast_nonneg batch
  calc
    _ <= (2 * batch : Nat) +
        (2 * Real.sqrt (batchedPrefixCount increment rounds) +
          (batch : Real) *
            (∑ round ∈ Finset.range rounds,
              if batch <= batchedPrefixCount increment round then
                (increment round : Real) /
                  batchedPrefixCount increment round else 0)) :=
      add_le_add hlow hhighStep
    _ <= _ := by
      have := mul_le_mul_of_nonneg_left hratio hbatchNonneg
      push_cast at this
      push_cast
      linarith

/-- A reciprocal correction clipped at one horizon pays the threshold region
once (plus one stale batch) and then telescopes logarithmically. -/
theorem sum_positive_batchedMinReciprocal_le
    (increment : Nat -> Nat) (batch threshold rounds : Nat)
    (cap coefficient : Real)
    (hbatch : 0 < batch) (hthreshold : batch <= threshold)
    (hincrement : forall round, increment round <= batch)
    (hcap : 0 <= cap) (hcoefficient : 0 <= coefficient) :
    (∑ round ∈ Finset.range rounds,
      if batchedPrefixCount increment round = 0 then 0 else
        (increment round : Real) *
          min cap (coefficient / batchedPrefixCount increment round)) <=
      cap * (threshold + batch) +
        2 * coefficient *
          Real.log ((max 1 (batchedPrefixCount increment rounds) : Nat) : Real) := by
  have hlowNat := sum_low_batchedIncrement_le increment batch threshold rounds
    hincrement
  have hlow : (∑ round ∈ Finset.range rounds,
      if batchedPrefixCount increment round < threshold then
        (increment round : Real) *
          min cap (coefficient / batchedPrefixCount increment round) else 0) <=
      cap * (threshold + batch) := by
    calc
      _ <= ∑ round ∈ Finset.range rounds,
          (if batchedPrefixCount increment round < threshold then
            (increment round : Real) else 0) * cap := by
        apply Finset.sum_le_sum
        intro round _
        by_cases hlow : batchedPrefixCount increment round < threshold
        · simp only [if_pos hlow]
          exact mul_le_mul_of_nonneg_left (min_le_left _ _) (Nat.cast_nonneg _)
        · simp [hlow, hcap]
      _ = cap *
          (∑ round ∈ Finset.range rounds,
            if batchedPrefixCount increment round < threshold then
              (increment round : Real) else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro round _
        ring
      _ <= cap * (threshold + batch) := by
        apply mul_le_mul_of_nonneg_left _ hcap
        exact_mod_cast hlowNat
  have hhigh : (∑ round ∈ Finset.range rounds,
      if threshold <= batchedPrefixCount increment round then
        (increment round : Real) *
          min cap (coefficient / batchedPrefixCount increment round) else 0) <=
      2 * coefficient *
        Real.log ((max 1 (batchedPrefixCount increment rounds) : Nat) : Real) := by
    have hratio := sum_high_batchedRatio_le_log increment batch threshold rounds
      hbatch hthreshold hincrement
    calc
      _ <= coefficient *
          (∑ round ∈ Finset.range rounds,
            if threshold <= batchedPrefixCount increment round then
              (increment round : Real) /
                batchedPrefixCount increment round else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro round _
        by_cases hhigh : threshold <= batchedPrefixCount increment round
        · simp only [if_pos hhigh]
          calc
            (increment round : Real) *
                min cap (coefficient / batchedPrefixCount increment round) <=
              (increment round : Real) *
                (coefficient / batchedPrefixCount increment round) :=
              mul_le_mul_of_nonneg_left (min_le_right _ _) (Nat.cast_nonneg _)
            _ = coefficient *
                ((increment round : Real) /
                  batchedPrefixCount increment round) := by ring
        · simp [hhigh, hcoefficient]
      _ <= coefficient *
          (2 * Real.log ((max 1
            (batchedPrefixCount increment rounds) : Nat) : Real)) :=
        mul_le_mul_of_nonneg_left hratio hcoefficient
      _ = _ := by ring
  have hsplit : (∑ round ∈ Finset.range rounds,
      if batchedPrefixCount increment round = 0 then 0 else
        (increment round : Real) *
          min cap (coefficient / batchedPrefixCount increment round)) <=
      (∑ round ∈ Finset.range rounds,
        if batchedPrefixCount increment round < threshold then
          (increment round : Real) *
            min cap (coefficient / batchedPrefixCount increment round) else 0) +
      (∑ round ∈ Finset.range rounds,
        if threshold <= batchedPrefixCount increment round then
          (increment round : Real) *
            min cap (coefficient / batchedPrefixCount increment round) else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro round _
    by_cases hz : batchedPrefixCount increment round = 0
    · simp [hz, hcap]
    · by_cases hl : batchedPrefixCount increment round < threshold
      · simp [hz, hl, Nat.not_le.mpr hl]
      · simp [hz, hl, Nat.le_of_not_gt hl]
  exact hsplit.trans (add_le_add hlow hhigh)

end BanditRLProof.FiniteHorizonRL.AdaptiveCumulativeHoeffdingUCBVI
