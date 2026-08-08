import BanditRLProof.Algorithms.UCBArmStreamProcess
import BanditRLProof.IndependenceFoundation
import BanditRLProof.ConcentrationSubGaussian

/-!
# Fixed-arm and adaptive-count tails for the UCB arm-stream process

The stationary product arm-stream measure makes each fixed arm an independent
reward trace with its prescribed kernel law. This module transports centered
sub-Gaussian witnesses to that stream space and combines the resulting fixed
prefix tails with the compiled UCB fixed-count peeling theorem.
-/

namespace BanditRLProof

open MeasureTheory ProbabilityTheory

namespace UCB

/-- Every time/arm coordinate has its prescribed stationary kernel law. -/
theorem armStreamMeasure_map_coord
    {K : Nat} (nu : Kernel (Fin K) Real) [IsMarkovKernel nu]
    (i : Nat) (arm : Fin K) :
    Measure.map (fun stream : ArmRewardStream K => stream i arm)
        (armStreamMeasure nu) =
      nu arm := by
  calc
    Measure.map (fun stream : ArmRewardStream K => stream i arm)
        (armStreamMeasure nu) =
        Measure.map
          (fun row : Fin K -> Real => row arm)
          (Measure.map
            (fun stream : ArmRewardStream K => stream i)
            (armStreamMeasure nu)) := by
      rw [Measure.map_map (measurable_pi_apply arm) (measurable_pi_apply i)]
      rfl
    _ = Measure.map
          (fun row : Fin K -> Real => row arm)
          (Measure.infinitePi fun candidate : Fin K => nu candidate) := by
      rw [armStreamMeasure, Measure.infinitePi_map_eval]
    _ = nu arm := by
      exact Measure.infinitePi_map_eval (fun candidate : Fin K => nu candidate) arm

/-- Centered coordinates of one fixed arm are independent across time. -/
theorem iIndepFun_armStreamMeasure_coord_sub
    {K : Nat} (nu : Kernel (Fin K) Real) [IsMarkovKernel nu]
    (arm : Fin K) (mean : Real) :
    iIndepFun
      (fun i (stream : ArmRewardStream K) => stream i arm - mean)
      (armStreamMeasure nu) := by
  simpa [armStreamMeasure] using
    (IndependenceFoundation.iIndepFun_infinitePi_coord
      (coordLaw := fun _ : Nat =>
        Measure.infinitePi fun candidate : Fin K => nu candidate)
      (X := fun _ (row : Fin K -> Real) => row arm - mean)
      (hX := fun _ => (measurable_pi_apply arm).sub measurable_const))

/-- Lower-tail centered coordinates are also independent across time. -/
theorem iIndepFun_armStreamMeasure_sub_coord
    {K : Nat} (nu : Kernel (Fin K) Real) [IsMarkovKernel nu]
    (arm : Fin K) (mean : Real) :
    iIndepFun
      (fun i (stream : ArmRewardStream K) => mean - stream i arm)
      (armStreamMeasure nu) := by
  simpa [armStreamMeasure] using
    (IndependenceFoundation.iIndepFun_infinitePi_coord
      (coordLaw := fun _ : Nat =>
        Measure.infinitePi fun candidate : Fin K => nu candidate)
      (X := fun _ (row : Fin K -> Real) => mean - row arm)
      (hX := fun _ => measurable_const.sub (measurable_pi_apply arm)))

/-- A fixed arm's centered one-coordinate MGF transports to stream space. -/
theorem hasSubgaussianMGF_armStreamMeasure_coord_sub
    {K : Nat} (nu : Kernel (Fin K) Real) [IsMarkovKernel nu]
    (arm : Fin K) (mean : Real) (sigma2 : NNReal)
    (hsubG : HasSubgaussianMGF
      (fun reward => reward - mean) sigma2 (nu arm))
    (i : Nat) :
    HasSubgaussianMGF
      (fun stream : ArmRewardStream K => stream i arm - mean)
      sigma2 (armStreamMeasure nu) := by
  have h := HasSubgaussianMGF.of_map
    (Y := fun stream : ArmRewardStream K => stream i arm)
    (X := fun reward : Real => reward - mean)
    ((measurable_pi_apply arm).comp (measurable_pi_apply i)).aemeasurable
    (by
      rw [armStreamMeasure_map_coord nu i arm]
      exact hsubG)
  simpa [Function.comp_apply] using h

/-- The corresponding lower-tail coordinate has the same variance proxy. -/
theorem hasSubgaussianMGF_armStreamMeasure_sub_coord
    {K : Nat} (nu : Kernel (Fin K) Real) [IsMarkovKernel nu]
    (arm : Fin K) (mean : Real) (sigma2 : NNReal)
    (hsubG : HasSubgaussianMGF
      (fun reward => reward - mean) sigma2 (nu arm))
    (i : Nat) :
    HasSubgaussianMGF
      (fun stream : ArmRewardStream K => mean - stream i arm)
      sigma2 (armStreamMeasure nu) := by
  have h := (hasSubgaussianMGF_armStreamMeasure_coord_sub
    nu arm mean sigma2 hsubG i).neg
  refine h.congr (Filter.Eventually.of_forall ?_)
  intro stream
  change -(stream i arm - mean) = mean - stream i arm
  ring

theorem sum_coord_sub_eq_armPrefixSum_sub
    {K : Nat} (stream : ArmRewardStream K) (arm : Fin K)
    (mean : Real) (k : Nat) :
    (Finset.range k).sum (fun i => stream i arm - mean) =
      armPrefixSum arm k stream - (k : Real) * mean := by
  simp [armPrefixSum, Finset.sum_sub_distrib, nsmul_eq_mul]

theorem sum_sub_coord_eq_mul_sub_armPrefixSum
    {K : Nat} (stream : ArmRewardStream K) (arm : Fin K)
    (mean : Real) (k : Nat) :
    (Finset.range k).sum (fun i => mean - stream i arm) =
      (k : Real) * mean - armPrefixSum arm k stream := by
  simp [armPrefixSum, Finset.sum_sub_distrib, nsmul_eq_mul]

/-- ENNReal upper tail for one fixed arm prefix. -/
theorem measure_armPrefixSum_sub_mul_ge_le
    {K : Nat} (nu : Kernel (Fin K) Real) [IsMarkovKernel nu]
    (arm : Fin K) (mean : Real) (sigma2 : NNReal)
    (hsubG : HasSubgaussianMGF
      (fun reward => reward - mean) sigma2 (nu arm))
    (k : Nat) {eps : Real} (heps : 0 <= eps) :
    armStreamMeasure nu {stream : ArmRewardStream K |
        eps <= armPrefixSum arm k stream - (k : Real) * mean} <=
      ENNReal.ofReal
        (Real.exp (-eps ^ 2 / (2 * (k : Real) * (sigma2 : Real)))) := by
  have htail := Concentration.subGaussian_sum_tail_ennreal_of_iIndepFun
    (armStreamMeasure nu)
    (iIndepFun_armStreamMeasure_coord_sub nu arm mean)
    (s := Finset.range k)
    (c := fun _ => sigma2)
    (fun i _hi =>
      hasSubgaussianMGF_armStreamMeasure_coord_sub
        nu arm mean sigma2 hsubG i)
    heps
  simpa [sum_coord_sub_eq_armPrefixSum_sub, nsmul_eq_mul,
    mul_assoc] using htail

/-- ENNReal lower tail for one fixed arm prefix. -/
theorem measure_mul_sub_armPrefixSum_ge_le
    {K : Nat} (nu : Kernel (Fin K) Real) [IsMarkovKernel nu]
    (arm : Fin K) (mean : Real) (sigma2 : NNReal)
    (hsubG : HasSubgaussianMGF
      (fun reward => reward - mean) sigma2 (nu arm))
    (k : Nat) {eps : Real} (heps : 0 <= eps) :
    armStreamMeasure nu {stream : ArmRewardStream K |
        eps <= (k : Real) * mean - armPrefixSum arm k stream} <=
      ENNReal.ofReal
        (Real.exp (-eps ^ 2 / (2 * (k : Real) * (sigma2 : Real)))) := by
  have htail := Concentration.subGaussian_sum_tail_ennreal_of_iIndepFun
    (armStreamMeasure nu)
    (iIndepFun_armStreamMeasure_sub_coord nu arm mean)
    (s := Finset.range k)
    (c := fun _ => sigma2)
    (fun i _hi =>
      hasSubgaussianMGF_armStreamMeasure_sub_coord
        nu arm mean sigma2 hsubG i)
    heps
  simpa [sum_sub_coord_eq_mul_sub_armPrefixSum, nsmul_eq_mul,
    mul_assoc] using htail

/-- Empirical mean of the first `k` latent rewards of one fixed arm. -/
noncomputable def armPrefixEmpiricalMean
    {K : Nat} (arm : Fin K) (k : Nat) (stream : ArmRewardStream K) : Real :=
  armPrefixSum arm k stream / (k : Real)

/--
Two-sided fixed-sample confidence radius for one arm with per-reward proxy
variance `sigma2`.
-/
noncomputable def armPrefixAverageConfidenceRadius
    (sigma2 : NNReal) (k : Nat) (delta : Real) : Real :=
  Concentration.subGaussianAverageConfidenceRadius (k • sigma2) k delta

/--
Two-sided `delta` confidence theorem for the empirical mean of exactly `k`
latent rewards of one arm under the stationary product arm-stream law.

The theorem derives positivity of the total proxy variance from `0 < k` and
`sigma2 ≠ 0`; callers do not supply a separate aggregate-variance contract.
-/
theorem measure_armPrefixAverageConfidenceRadius_le_abs_empiricalMean_sub
    {K : Nat}
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu]
    (arm : Fin K) (mean : Real) (sigma2 : NNReal)
    (hsubG : HasSubgaussianMGF
      (fun reward => reward - mean) sigma2 (nu arm))
    (k : Nat) (hk : 0 < k) (hsigma2 : sigma2 ≠ 0)
    (delta : Real) (hdelta : 0 < delta) (hdelta_le_one : delta <= 1) :
    armStreamMeasure nu {stream : ArmRewardStream K |
        armPrefixAverageConfidenceRadius sigma2 k delta <=
          |armPrefixEmpiricalMean arm k stream - mean|} <=
      ENNReal.ofReal delta := by
  have hkReal : 0 < (k : Real) := by exact_mod_cast hk
  have hkReal_ne : (k : Real) ≠ 0 := ne_of_gt hkReal
  have hsigma2Real : 0 < (sigma2 : Real) := by
    exact_mod_cast (pos_iff_ne_zero.mpr hsigma2)
  have hvariance :
      0 < (((Finset.range k).sum (fun _ => sigma2) : NNReal) : Real) := by
    simpa [nsmul_eq_mul] using mul_pos hkReal hsigma2Real
  have htail :=
    Concentration.subGaussian_average_abs_tail_ennreal_delta_of_iIndepFun
      (armStreamMeasure nu)
      (iIndepFun_armStreamMeasure_coord_sub nu arm mean)
      (c := fun _ => sigma2)
      k hk
      (fun i _hi =>
        hasSubgaussianMGF_armStreamMeasure_coord_sub
          nu arm mean sigma2 hsubG i)
      hvariance delta hdelta hdelta_le_one
  have hcenter : forall stream : ArmRewardStream K,
      ((Finset.range k).sum (fun i => stream i arm - mean)) / (k : Real) =
        armPrefixEmpiricalMean arm k stream - mean := by
    intro stream
    rw [sum_coord_sub_eq_armPrefixSum_sub]
    unfold armPrefixEmpiricalMean
    field_simp [hkReal_ne]
  have hvariance_eq :
      (Finset.range k).sum (fun _ => sigma2) = k • sigma2 := by
    simp
  calc
    armStreamMeasure nu {stream : ArmRewardStream K |
        armPrefixAverageConfidenceRadius sigma2 k delta <=
          |armPrefixEmpiricalMean arm k stream - mean|} =
        armStreamMeasure nu {stream : ArmRewardStream K |
          Concentration.subGaussianAverageConfidenceRadius
              ((Finset.range k).sum (fun _ => sigma2)) k delta <=
            |((Finset.range k).sum (fun i => stream i arm - mean)) /
              (k : Real)|} := by
      congr 1
      ext stream
      simp only [Set.mem_setOf_eq, armPrefixAverageConfidenceRadius]
      rw [hvariance_eq, hcenter stream]
    _ <= ENNReal.ofReal delta := htail

/-- Pair event used to peel an upper selected-reward deviation by pull count. -/
def upperDeviationPairs (mean : Real) (threshold : Nat -> Real) :
    Set (Nat × Real) :=
  {pair | threshold pair.1 <= pair.2 - (pair.1 : Real) * mean}

/-- Pair event used to peel a lower selected-reward deviation by pull count. -/
def lowerDeviationPairs (mean : Real) (threshold : Nat -> Real) :
    Set (Nat × Real) :=
  {pair | threshold pair.1 <= (pair.1 : Real) * mean - pair.2}

/-- Positive-count upper deviation pair event used by UCB index tails. -/
def positiveUpperDeviationPairs (mean : Real) (threshold : Nat -> Real) :
    Set (Nat × Real) :=
  {pair | 0 < pair.1 ∧
    threshold pair.1 <= pair.2 - (pair.1 : Real) * mean}

/-- Positive-count lower deviation pair event used by UCB index tails. -/
def positiveLowerDeviationPairs (mean : Real) (threshold : Nat -> Real) :
    Set (Nat × Real) :=
  {pair | 0 < pair.1 ∧
    threshold pair.1 <= (pair.1 : Real) * mean - pair.2}

@[simp]
theorem mem_fst_image_upperDeviationPairs
    (mean : Real) (threshold : Nat -> Real) (k : Nat) :
    k ∈ Prod.fst '' upperDeviationPairs mean threshold := by
  refine ⟨(k, threshold k + (k : Real) * mean), ?_, rfl⟩
  change threshold k <=
    threshold k + (k : Real) * mean - (k : Real) * mean
  linarith

@[simp]
theorem mem_fst_image_lowerDeviationPairs
    (mean : Real) (threshold : Nat -> Real) (k : Nat) :
    k ∈ Prod.fst '' lowerDeviationPairs mean threshold := by
  refine ⟨(k, (k : Real) * mean - threshold k), ?_, rfl⟩
  change threshold k <=
    (k : Real) * mean - ((k : Real) * mean - threshold k)
  linarith

@[simp]
theorem mem_fst_image_positiveUpperDeviationPairs_iff
    (mean : Real) (threshold : Nat -> Real) (k : Nat) :
    k ∈ Prod.fst '' positiveUpperDeviationPairs mean threshold ↔ 0 < k := by
  constructor
  · rintro ⟨pair, hpair, rfl⟩
    exact hpair.1
  · intro hk
    refine ⟨(k, threshold k + (k : Real) * mean), ?_, rfl⟩
    constructor
    · exact hk
    · change threshold k <=
        threshold k + (k : Real) * mean - (k : Real) * mean
      linarith

@[simp]
theorem mem_fst_image_positiveLowerDeviationPairs_iff
    (mean : Real) (threshold : Nat -> Real) (k : Nat) :
    k ∈ Prod.fst '' positiveLowerDeviationPairs mean threshold ↔ 0 < k := by
  constructor
  · rintro ⟨pair, hpair, rfl⟩
    exact hpair.1
  · intro hk
    refine ⟨(k, (k : Real) * mean - threshold k), ?_, rfl⟩
    constructor
    · exact hk
    · change threshold k <=
        (k : Real) * mean - ((k : Real) * mean - threshold k)
      linarith

/--
Adaptive-count upper selected-reward tail for the recursive UCB process.

The threshold may depend on the realized pull count. Peeling turns the event
into a finite sum over all fixed counts `k <= n`, and each term is discharged
by the stationary fixed-arm sub-Gaussian prefix tail.
-/
theorem measure_sumRewards_sub_pullCount_mul_ge_le
    {K : Nat} (hK : 0 < K) (c : Real)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu]
    (arm : Fin K) (mean : Real) (sigma2 : NNReal)
    (hsubG : HasSubgaussianMGF
      (fun reward => reward - mean) sigma2 (nu arm))
    (n : Nat) (threshold : Nat -> Real)
    (hthreshold : forall k, k <= n -> 0 <= threshold k) :
    armStreamMeasure nu {stream : ArmRewardStream K |
        threshold (pullCount (armStreamAction hK c stream) arm n) <=
          sumRewards (armStreamAction hK c stream)
              (armStreamReward hK c stream) arm n -
            (pullCount (armStreamAction hK c stream) arm n : Real) * mean} <=
      (Finset.range (n + 1)).sum (fun k =>
        ENNReal.ofReal
          (Real.exp
            (-(threshold k) ^ 2 /
              (2 * (k : Real) * (sigma2 : Real))))) := by
  classical
  have hpeel := measure_pullCount_prod_sumRewards_armStreamUCB_mem_le
    hK c nu arm n (upperDeviationPairs mean threshold)
  have hprojected : forall k : Nat,
      exists value : Real,
        threshold k <= value - (k : Real) * mean := by
    intro k
    refine ⟨threshold k + (k : Real) * mean, ?_⟩
    linarith
  have hpeel' :
      armStreamMeasure nu {stream : ArmRewardStream K |
          threshold (pullCount (armStreamAction hK c stream) arm n) <=
            sumRewards (armStreamAction hK c stream)
                (armStreamReward hK c stream) arm n -
              (pullCount (armStreamAction hK c stream) arm n : Real) * mean} <=
        (Finset.range (n + 1)).sum (fun k =>
          armStreamMeasure nu {stream : ArmRewardStream K |
            threshold k <=
              armPrefixSum arm k stream - (k : Real) * mean}) := by
    simpa [upperDeviationPairs, hprojected] using hpeel
  refine hpeel'.trans (Finset.sum_le_sum ?_)
  intro k hk
  exact measure_armPrefixSum_sub_mul_ge_le
    nu arm mean sigma2 hsubG k
      (hthreshold k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))

/-- Adaptive-count lower selected-reward tail for the recursive UCB process. -/
theorem measure_pullCount_mul_sub_sumRewards_ge_le
    {K : Nat} (hK : 0 < K) (c : Real)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu]
    (arm : Fin K) (mean : Real) (sigma2 : NNReal)
    (hsubG : HasSubgaussianMGF
      (fun reward => reward - mean) sigma2 (nu arm))
    (n : Nat) (threshold : Nat -> Real)
    (hthreshold : forall k, k <= n -> 0 <= threshold k) :
    armStreamMeasure nu {stream : ArmRewardStream K |
        threshold (pullCount (armStreamAction hK c stream) arm n) <=
          (pullCount (armStreamAction hK c stream) arm n : Real) * mean -
            sumRewards (armStreamAction hK c stream)
              (armStreamReward hK c stream) arm n} <=
      (Finset.range (n + 1)).sum (fun k =>
        ENNReal.ofReal
          (Real.exp
            (-(threshold k) ^ 2 /
              (2 * (k : Real) * (sigma2 : Real))))) := by
  classical
  have hpeel := measure_pullCount_prod_sumRewards_armStreamUCB_mem_le
    hK c nu arm n (lowerDeviationPairs mean threshold)
  have hprojected : forall k : Nat,
      exists value : Real,
        threshold k <= (k : Real) * mean - value := by
    intro k
    refine ⟨(k : Real) * mean - threshold k, ?_⟩
    linarith
  have hpeel' :
      armStreamMeasure nu {stream : ArmRewardStream K |
          threshold (pullCount (armStreamAction hK c stream) arm n) <=
            (pullCount (armStreamAction hK c stream) arm n : Real) * mean -
              sumRewards (armStreamAction hK c stream)
                (armStreamReward hK c stream) arm n} <=
        (Finset.range (n + 1)).sum (fun k =>
          armStreamMeasure nu {stream : ArmRewardStream K |
            threshold k <=
              (k : Real) * mean - armPrefixSum arm k stream}) := by
    simpa [lowerDeviationPairs, hprojected] using hpeel
  refine hpeel'.trans (Finset.sum_le_sum ?_)
  intro k hk
  exact measure_mul_sub_armPrefixSum_ge_le
    nu arm mean sigma2 hsubG k
      (hthreshold k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))

/-- Positive-pull-count adaptive upper tail, with the zero-count fiber removed. -/
theorem measure_pos_and_sumRewards_sub_pullCount_mul_ge_le
    {K : Nat} (hK : 0 < K) (c : Real)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu]
    (arm : Fin K) (mean : Real) (sigma2 : NNReal)
    (hsubG : HasSubgaussianMGF
      (fun reward => reward - mean) sigma2 (nu arm))
    (n : Nat) (threshold : Nat -> Real)
    (hthreshold : forall k, 0 < k -> k <= n -> 0 <= threshold k) :
    armStreamMeasure nu {stream : ArmRewardStream K |
        0 < pullCount (armStreamAction hK c stream) arm n ∧
        threshold (pullCount (armStreamAction hK c stream) arm n) <=
          sumRewards (armStreamAction hK c stream)
              (armStreamReward hK c stream) arm n -
            (pullCount (armStreamAction hK c stream) arm n : Real) * mean} <=
      ((Finset.range (n + 1)).filter (fun k => 0 < k)).sum (fun k =>
        ENNReal.ofReal
          (Real.exp
            (-(threshold k) ^ 2 /
              (2 * (k : Real) * (sigma2 : Real))))) := by
  classical
  have hpeel := measure_pullCount_prod_sumRewards_armStreamUCB_mem_le
    hK c nu arm n (positiveUpperDeviationPairs mean threshold)
  have hprojected : forall k : Nat,
      0 < k -> exists value : Real,
        threshold k <= value - (k : Real) * mean := by
    intro k _hk
    refine ⟨threshold k + (k : Real) * mean, ?_⟩
    linarith
  have hprojection_iff : forall k : Nat,
      (0 < k ∧ exists value : Real,
        threshold k <= value - (k : Real) * mean) ↔ 0 < k := by
    intro k
    constructor
    · exact And.left
    · intro hk
      exact ⟨hk, hprojected k hk⟩
  have hpeel' :
      armStreamMeasure nu {stream : ArmRewardStream K |
          0 < pullCount (armStreamAction hK c stream) arm n ∧
          threshold (pullCount (armStreamAction hK c stream) arm n) <=
            sumRewards (armStreamAction hK c stream)
                (armStreamReward hK c stream) arm n -
              (pullCount (armStreamAction hK c stream) arm n : Real) * mean} <=
        ((Finset.range (n + 1)).filter (fun k => 0 < k)).sum (fun k =>
          armStreamMeasure nu {stream : ArmRewardStream K |
            0 < k ∧ threshold k <=
              armPrefixSum arm k stream - (k : Real) * mean}) := by
    simpa [positiveUpperDeviationPairs, hprojection_iff] using hpeel
  refine hpeel'.trans (Finset.sum_le_sum ?_)
  intro k hk
  have hk' := Finset.mem_filter.mp hk
  simpa [hk'.2] using
    (measure_armPrefixSum_sub_mul_ge_le
      nu arm mean sigma2 hsubG k
        (hthreshold k hk'.2
          (Nat.le_of_lt_succ (Finset.mem_range.mp hk'.1))))

/-- Positive-pull-count adaptive lower tail, with the zero-count fiber removed. -/
theorem measure_pos_and_pullCount_mul_sub_sumRewards_ge_le
    {K : Nat} (hK : 0 < K) (c : Real)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu]
    (arm : Fin K) (mean : Real) (sigma2 : NNReal)
    (hsubG : HasSubgaussianMGF
      (fun reward => reward - mean) sigma2 (nu arm))
    (n : Nat) (threshold : Nat -> Real)
    (hthreshold : forall k, 0 < k -> k <= n -> 0 <= threshold k) :
    armStreamMeasure nu {stream : ArmRewardStream K |
        0 < pullCount (armStreamAction hK c stream) arm n ∧
        threshold (pullCount (armStreamAction hK c stream) arm n) <=
          (pullCount (armStreamAction hK c stream) arm n : Real) * mean -
            sumRewards (armStreamAction hK c stream)
              (armStreamReward hK c stream) arm n} <=
      ((Finset.range (n + 1)).filter (fun k => 0 < k)).sum (fun k =>
        ENNReal.ofReal
          (Real.exp
            (-(threshold k) ^ 2 /
              (2 * (k : Real) * (sigma2 : Real))))) := by
  classical
  have hpeel := measure_pullCount_prod_sumRewards_armStreamUCB_mem_le
    hK c nu arm n (positiveLowerDeviationPairs mean threshold)
  have hprojected : forall k : Nat,
      0 < k -> exists value : Real,
        threshold k <= (k : Real) * mean - value := by
    intro k _hk
    refine ⟨(k : Real) * mean - threshold k, ?_⟩
    linarith
  have hprojection_iff : forall k : Nat,
      (0 < k ∧ exists value : Real,
        threshold k <= (k : Real) * mean - value) ↔ 0 < k := by
    intro k
    constructor
    · exact And.left
    · intro hk
      exact ⟨hk, hprojected k hk⟩
  have hpeel' :
      armStreamMeasure nu {stream : ArmRewardStream K |
          0 < pullCount (armStreamAction hK c stream) arm n ∧
          threshold (pullCount (armStreamAction hK c stream) arm n) <=
            (pullCount (armStreamAction hK c stream) arm n : Real) * mean -
              sumRewards (armStreamAction hK c stream)
                (armStreamReward hK c stream) arm n} <=
        ((Finset.range (n + 1)).filter (fun k => 0 < k)).sum (fun k =>
          armStreamMeasure nu {stream : ArmRewardStream K |
            0 < k ∧ threshold k <=
              (k : Real) * mean - armPrefixSum arm k stream}) := by
    simpa [positiveLowerDeviationPairs, hprojection_iff] using hpeel
  refine hpeel'.trans (Finset.sum_le_sum ?_)
  intro k hk
  have hk' := Finset.mem_filter.mp hk
  simpa [hk'.2] using
    (measure_mul_sub_armPrefixSum_ge_le
      nu arm mean sigma2 hsubG k
        (hthreshold k hk'.2
          (Nat.le_of_lt_succ (Finset.mem_range.mp hk'.1))))

/-- Pull-count-scaled confidence width used in the fixed-count tail fibers. -/
noncomputable def countWidthThreshold
    (c : Real) (sigma2 : NNReal) (n k : Nat) : Real :=
  (k : Real) *
    Real.sqrt
      (2 * (c * (sigma2 : Real)) * Real.log ((n + 1 : Nat) : Real) /
        (k : Real))

theorem countWidthThreshold_nonneg
    (c : Real) (sigma2 : NNReal) (n k : Nat) :
    0 <= countWidthThreshold c sigma2 n k := by
  exact mul_nonneg (Nat.cast_nonneg k) (Real.sqrt_nonneg _)

/-- Lower index failure implies the corresponding count-scaled lower sum deviation. -/
theorem countWidthThreshold_le_mul_mean_sub_sumRewards_of_empiricalMean_add_width_le
    {K : Nat} (action : ActionTrace (Fin K)) (reward : RewardTrace Real)
    (arm : Fin K) (n : Nat) (mean c : Real) (sigma2 : NNReal)
    (hcount : 0 < pullCount action arm n)
    (hindex :
      realEmpiricalMean action reward arm n +
          realWidth action (c * (sigma2 : Real)) arm n <= mean) :
    countWidthThreshold c sigma2 n (pullCount action arm n) <=
      (pullCount action arm n : Real) * mean -
        sumRewards action reward arm n := by
  let k := pullCount action arm n
  let total := sumRewards action reward arm n
  have hk : 0 < (k : Real) := by exact_mod_cast hcount
  have hk_ne : (k : Real) ≠ 0 := ne_of_gt hk
  have hdiv : total / (k : Real) * (k : Real) = total :=
    div_mul_cancel₀ total hk_ne
  change total / (k : Real) +
      Real.sqrt
        (2 * (c * (sigma2 : Real)) * Real.log ((n + 1 : Nat) : Real) /
          (k : Real)) <= mean at hindex
  change (k : Real) *
      Real.sqrt
        (2 * (c * (sigma2 : Real)) * Real.log ((n + 1 : Nat) : Real) /
          (k : Real)) <=
    (k : Real) * mean - total
  nlinarith

/-- Upper index failure implies the corresponding count-scaled upper sum deviation. -/
theorem countWidthThreshold_le_sumRewards_sub_mul_mean_of_mean_le_empiricalMean_sub_width
    {K : Nat} (action : ActionTrace (Fin K)) (reward : RewardTrace Real)
    (arm : Fin K) (n : Nat) (mean c : Real) (sigma2 : NNReal)
    (hcount : 0 < pullCount action arm n)
    (hindex : mean <=
      realEmpiricalMean action reward arm n -
        realWidth action (c * (sigma2 : Real)) arm n) :
    countWidthThreshold c sigma2 n (pullCount action arm n) <=
      sumRewards action reward arm n -
        (pullCount action arm n : Real) * mean := by
  let k := pullCount action arm n
  let total := sumRewards action reward arm n
  have hk : 0 < (k : Real) := by exact_mod_cast hcount
  have hk_ne : (k : Real) ≠ 0 := ne_of_gt hk
  have hdiv : total / (k : Real) * (k : Real) = total :=
    div_mul_cancel₀ total hk_ne
  change mean <= total / (k : Real) -
      Real.sqrt
        (2 * (c * (sigma2 : Real)) * Real.log ((n + 1 : Nat) : Real) /
          (k : Real)) at hindex
  change (k : Real) *
      Real.sqrt
        (2 * (c * (sigma2 : Real)) * Real.log ((n + 1 : Nat) : Real) /
          (k : Real)) <=
    total - (k : Real) * mean
  nlinarith

/--
LML-shaped lower UCB-index tail for the actual recursive arm-stream process,
before simplifying the finite fixed-count exponential sum.
-/
theorem measure_realEmpiricalMean_add_realWidth_le_mean
    {K : Nat} (hK : 0 < K) (c : Real)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu]
    (arm : Fin K) (mean : Real) (sigma2 : NNReal)
    (hsubG : HasSubgaussianMGF
      (fun reward => reward - mean) sigma2 (nu arm))
    (n : Nat) :
    armStreamMeasure nu {stream : ArmRewardStream K |
        0 < pullCount
            (armStreamAction hK (c * (sigma2 : Real)) stream) arm n ∧
        realEmpiricalMean
              (armStreamAction hK (c * (sigma2 : Real)) stream)
              (armStreamReward hK (c * (sigma2 : Real)) stream) arm n +
            realWidth
              (armStreamAction hK (c * (sigma2 : Real)) stream)
              (c * (sigma2 : Real)) arm n <= mean} <=
      ((Finset.range (n + 1)).filter (fun k => 0 < k)).sum (fun k =>
        ENNReal.ofReal
          (Real.exp
            (-(countWidthThreshold c sigma2 n k) ^ 2 /
              (2 * (k : Real) * (sigma2 : Real))))) := by
  let processScale := c * (sigma2 : Real)
  let action := armStreamAction hK processScale
  let reward := armStreamReward hK processScale
  have hsubset :
      {stream : ArmRewardStream K |
        0 < pullCount (action stream) arm n ∧
        realEmpiricalMean (action stream) (reward stream) arm n +
          realWidth (action stream) processScale arm n <= mean} ⊆
      {stream : ArmRewardStream K |
        0 < pullCount (action stream) arm n ∧
        countWidthThreshold c sigma2 n (pullCount (action stream) arm n) <=
          (pullCount (action stream) arm n : Real) * mean -
            sumRewards (action stream) (reward stream) arm n} := by
    intro stream hstream
    exact ⟨hstream.1,
      countWidthThreshold_le_mul_mean_sub_sumRewards_of_empiricalMean_add_width_le
        (action stream) (reward stream) arm n mean c sigma2
        hstream.1 hstream.2⟩
  calc
    armStreamMeasure nu {stream : ArmRewardStream K |
        0 < pullCount (action stream) arm n ∧
        realEmpiricalMean (action stream) (reward stream) arm n +
          realWidth (action stream) processScale arm n <= mean} <=
        armStreamMeasure nu {stream : ArmRewardStream K |
          0 < pullCount (action stream) arm n ∧
          countWidthThreshold c sigma2 n (pullCount (action stream) arm n) <=
            (pullCount (action stream) arm n : Real) * mean -
              sumRewards (action stream) (reward stream) arm n} :=
      measure_mono hsubset
    _ <= ((Finset.range (n + 1)).filter (fun k => 0 < k)).sum (fun k =>
          ENNReal.ofReal
            (Real.exp
              (-(countWidthThreshold c sigma2 n k) ^ 2 /
                (2 * (k : Real) * (sigma2 : Real))))) := by
      exact measure_pos_and_pullCount_mul_sub_sumRewards_ge_le
        hK processScale nu arm mean sigma2 hsubG n
        (countWidthThreshold c sigma2 n)
        (fun k _hk _hkn => countWidthThreshold_nonneg c sigma2 n k)

/--
LML-shaped upper UCB-index tail for the actual recursive arm-stream process,
before simplifying the finite fixed-count exponential sum.
-/
theorem measure_mean_le_realEmpiricalMean_sub_realWidth
    {K : Nat} (hK : 0 < K) (c : Real)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu]
    (arm : Fin K) (mean : Real) (sigma2 : NNReal)
    (hsubG : HasSubgaussianMGF
      (fun reward => reward - mean) sigma2 (nu arm))
    (n : Nat) :
    armStreamMeasure nu {stream : ArmRewardStream K |
        0 < pullCount
            (armStreamAction hK (c * (sigma2 : Real)) stream) arm n ∧
        mean <=
          realEmpiricalMean
              (armStreamAction hK (c * (sigma2 : Real)) stream)
              (armStreamReward hK (c * (sigma2 : Real)) stream) arm n -
            realWidth
              (armStreamAction hK (c * (sigma2 : Real)) stream)
              (c * (sigma2 : Real)) arm n} <=
      ((Finset.range (n + 1)).filter (fun k => 0 < k)).sum (fun k =>
        ENNReal.ofReal
          (Real.exp
            (-(countWidthThreshold c sigma2 n k) ^ 2 /
              (2 * (k : Real) * (sigma2 : Real))))) := by
  let processScale := c * (sigma2 : Real)
  let action := armStreamAction hK processScale
  let reward := armStreamReward hK processScale
  have hsubset :
      {stream : ArmRewardStream K |
        0 < pullCount (action stream) arm n ∧
        mean <= realEmpiricalMean (action stream) (reward stream) arm n -
          realWidth (action stream) processScale arm n} ⊆
      {stream : ArmRewardStream K |
        0 < pullCount (action stream) arm n ∧
        countWidthThreshold c sigma2 n (pullCount (action stream) arm n) <=
          sumRewards (action stream) (reward stream) arm n -
            (pullCount (action stream) arm n : Real) * mean} := by
    intro stream hstream
    exact ⟨hstream.1,
      countWidthThreshold_le_sumRewards_sub_mul_mean_of_mean_le_empiricalMean_sub_width
        (action stream) (reward stream) arm n mean c sigma2
        hstream.1 hstream.2⟩
  calc
    armStreamMeasure nu {stream : ArmRewardStream K |
        0 < pullCount (action stream) arm n ∧
        mean <= realEmpiricalMean (action stream) (reward stream) arm n -
          realWidth (action stream) processScale arm n} <=
        armStreamMeasure nu {stream : ArmRewardStream K |
          0 < pullCount (action stream) arm n ∧
          countWidthThreshold c sigma2 n (pullCount (action stream) arm n) <=
            sumRewards (action stream) (reward stream) arm n -
              (pullCount (action stream) arm n : Real) * mean} :=
      measure_mono hsubset
    _ <= ((Finset.range (n + 1)).filter (fun k => 0 < k)).sum (fun k =>
          ENNReal.ofReal
            (Real.exp
              (-(countWidthThreshold c sigma2 n k) ^ 2 /
                (2 * (k : Real) * (sigma2 : Real))))) := by
      exact measure_pos_and_sumRewards_sub_pullCount_mul_ge_le
        hK processScale nu arm mean sigma2 hsubG n
        (countWidthThreshold c sigma2 n)
        (fun k _hk _hkn => countWidthThreshold_nonneg c sigma2 n k)

/-- Every positive fixed-count fiber has the same logarithmic exponent. -/
theorem countWidthThreshold_sq_div_eq
    (c : Real) (sigma2 : NNReal) (n k : Nat)
    (hc : 0 <= c) (hsigma2 : sigma2 ≠ 0) (hk : 0 < k) :
    (countWidthThreshold c sigma2 n k) ^ 2 /
        (2 * (k : Real) * (sigma2 : Real)) =
      c * Real.log ((n + 1 : Nat) : Real) := by
  have hk_real : 0 < (k : Real) := by exact_mod_cast hk
  have hk_ne : (k : Real) ≠ 0 := ne_of_gt hk_real
  have hsigma_pos : 0 < (sigma2 : Real) := by
    exact_mod_cast (pos_iff_ne_zero.mpr hsigma2)
  have hsigma_ne : (sigma2 : Real) ≠ 0 := ne_of_gt hsigma_pos
  have hlog : 0 <= Real.log ((n + 1 : Nat) : Real) := by
    apply Real.log_nonneg
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hsqrt : 0 <=
      2 * (c * (sigma2 : Real)) * Real.log ((n + 1 : Nat) : Real) /
        (k : Real) := by
    positivity
  unfold countWidthThreshold
  rw [mul_pow, Real.sq_sqrt hsqrt]
  field_simp [hk_ne, hsigma_ne]

theorem positiveCountFilter_eq_Icc (n : Nat) :
    (Finset.range (n + 1)).filter (fun k => 0 < k) = Finset.Icc 1 n := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
  omega

/-- The fixed-count exponential sum collapses to `n` identical terms. -/
theorem sum_countWidthThreshold_tail_eq
    (c : Real) (sigma2 : NNReal) (n : Nat)
    (hc : 0 <= c) (hsigma2 : sigma2 ≠ 0) :
    ((Finset.range (n + 1)).filter (fun k => 0 < k)).sum (fun k =>
        ENNReal.ofReal
          (Real.exp
            (-(countWidthThreshold c sigma2 n k) ^ 2 /
              (2 * (k : Real) * (sigma2 : Real))))) =
      (n : ENNReal) *
        ENNReal.ofReal
          (Real.exp (-c * Real.log ((n + 1 : Nat) : Real))) := by
  rw [positiveCountFilter_eq_Icc]
  have hterm : forall k, k ∈ Finset.Icc 1 n ->
      ENNReal.ofReal
          (Real.exp
            (-(countWidthThreshold c sigma2 n k) ^ 2 /
              (2 * (k : Real) * (sigma2 : Real)))) =
        ENNReal.ofReal
          (Real.exp (-c * Real.log ((n + 1 : Nat) : Real))) := by
    intro k hk
    rw [neg_div,
      countWidthThreshold_sq_div_eq c sigma2 n k hc hsigma2
      (Finset.mem_Icc.mp hk).1]
    ring_nf
  rw [Finset.sum_congr rfl hterm]
  simp [nsmul_eq_mul]

/-- Convert the peeled logarithmic tail into the inverse-power form used by LML. -/
theorem natCast_mul_exp_neg_log_le_inv_rpow_sub_one
    (c : Real) (n : Nat) :
    (n : ENNReal) *
        ENNReal.ofReal
          (Real.exp (-c * Real.log ((n + 1 : Nat) : Real))) <=
      (1 : ENNReal) /
        (((n + 1 : Nat) : ENNReal) ^ (c - 1)) := by
  have hx_real : 0 < ((n + 1 : Nat) : Real) := by positivity
  have hx_zero : ((n + 1 : Nat) : ENNReal) ≠ 0 := by simp
  have hx_top : ((n + 1 : Nat) : ENNReal) ≠ ⊤ := by simp
  have hexp :
      ENNReal.ofReal
          (Real.exp (-c * Real.log ((n + 1 : Nat) : Real))) =
        (((n + 1 : Nat) : ENNReal) ^ (-c)) := by
    have hreal :
        Real.exp (-c * Real.log ((n + 1 : Nat) : Real)) =
          (((n + 1 : Nat) : Real) ^ (-c)) := by
      rw [Real.rpow_def_of_pos hx_real]
      congr 1
      ring
    rw [hreal, <- ENNReal.ofReal_rpow_of_pos hx_real]
    congr 1
    exact ENNReal.ofReal_natCast (n + 1)
  calc
    (n : ENNReal) *
        ENNReal.ofReal
          (Real.exp (-c * Real.log ((n + 1 : Nat) : Real))) =
        (n : ENNReal) * (((n + 1 : Nat) : ENNReal) ^ (-c)) := by
          rw [hexp]
    _ <= ((n + 1 : Nat) : ENNReal) *
        (((n + 1 : Nat) : ENNReal) ^ (-c)) := by
          gcongr
          exact_mod_cast Nat.le_succ n
    _ = (((n + 1 : Nat) : ENNReal) ^ (1 : Real)) *
        (((n + 1 : Nat) : ENNReal) ^ (-c)) := by
          rw [ENNReal.rpow_one]
    _ = (((n + 1 : Nat) : ENNReal) ^ (1 + (-c))) := by
          exact (ENNReal.rpow_add 1 (-c) hx_zero hx_top).symm
    _ = (((n + 1 : Nat) : ENNReal) ^ (1 - c)) := by
          congr 1
    _ = (1 : ENNReal) /
        (((n + 1 : Nat) : ENNReal) ^ (c - 1)) := by
          rw [show 1 - c = -(c - 1) by ring, ENNReal.rpow_neg]
          simp

/-- Simplified logarithmic lower-index tail for the recursive UCB process. -/
theorem measure_realEmpiricalMean_add_realWidth_le_mean_log_bound
    {K : Nat} (hK : 0 < K) (c : Real)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu]
    (arm : Fin K) (mean : Real) (sigma2 : NNReal)
    (hsubG : HasSubgaussianMGF
      (fun reward => reward - mean) sigma2 (nu arm))
    (hc : 0 <= c) (hsigma2 : sigma2 ≠ 0) (n : Nat) :
    armStreamMeasure nu {stream : ArmRewardStream K |
        0 < pullCount
            (armStreamAction hK (c * (sigma2 : Real)) stream) arm n ∧
        realEmpiricalMean
              (armStreamAction hK (c * (sigma2 : Real)) stream)
              (armStreamReward hK (c * (sigma2 : Real)) stream) arm n +
            realWidth
              (armStreamAction hK (c * (sigma2 : Real)) stream)
              (c * (sigma2 : Real)) arm n <= mean} <=
      (n : ENNReal) *
        ENNReal.ofReal
          (Real.exp (-c * Real.log ((n + 1 : Nat) : Real))) := by
  have h := measure_realEmpiricalMean_add_realWidth_le_mean
    hK c nu arm mean sigma2 hsubG n
  rw [sum_countWidthThreshold_tail_eq c sigma2 n hc hsigma2] at h
  exact h

/-- Simplified logarithmic upper-index tail for the recursive UCB process. -/
theorem measure_mean_le_realEmpiricalMean_sub_realWidth_log_bound
    {K : Nat} (hK : 0 < K) (c : Real)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu]
    (arm : Fin K) (mean : Real) (sigma2 : NNReal)
    (hsubG : HasSubgaussianMGF
      (fun reward => reward - mean) sigma2 (nu arm))
    (hc : 0 <= c) (hsigma2 : sigma2 ≠ 0) (n : Nat) :
    armStreamMeasure nu {stream : ArmRewardStream K |
        0 < pullCount
            (armStreamAction hK (c * (sigma2 : Real)) stream) arm n ∧
        mean <=
          realEmpiricalMean
              (armStreamAction hK (c * (sigma2 : Real)) stream)
              (armStreamReward hK (c * (sigma2 : Real)) stream) arm n -
            realWidth
              (armStreamAction hK (c * (sigma2 : Real)) stream)
              (c * (sigma2 : Real)) arm n} <=
      (n : ENNReal) *
        ENNReal.ofReal
          (Real.exp (-c * Real.log ((n + 1 : Nat) : Real))) := by
  have h := measure_mean_le_realEmpiricalMean_sub_realWidth
    hK c nu arm mean sigma2 hsubG n
  rw [sum_countWidthThreshold_tail_eq c sigma2 n hc hsigma2] at h
  exact h

/-- LML-shaped inverse-power lower-index tail for the recursive UCB process. -/
theorem measure_realEmpiricalMean_add_realWidth_le_mean_rpow_bound
    {K : Nat} (hK : 0 < K) (c : Real)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu]
    (arm : Fin K) (mean : Real) (sigma2 : NNReal)
    (hsubG : HasSubgaussianMGF
      (fun reward => reward - mean) sigma2 (nu arm))
    (hc : 0 <= c) (hsigma2 : sigma2 ≠ 0) (n : Nat) :
    armStreamMeasure nu {stream : ArmRewardStream K |
        0 < pullCount
            (armStreamAction hK (c * (sigma2 : Real)) stream) arm n /\
        realEmpiricalMean
              (armStreamAction hK (c * (sigma2 : Real)) stream)
              (armStreamReward hK (c * (sigma2 : Real)) stream) arm n +
            realWidth
              (armStreamAction hK (c * (sigma2 : Real)) stream)
              (c * (sigma2 : Real)) arm n <= mean} <=
      (1 : ENNReal) /
        (((n + 1 : Nat) : ENNReal) ^ (c - 1)) := by
  exact (measure_realEmpiricalMean_add_realWidth_le_mean_log_bound
    hK c nu arm mean sigma2 hsubG hc hsigma2 n).trans
      (natCast_mul_exp_neg_log_le_inv_rpow_sub_one c n)

/-- LML-shaped inverse-power upper-index tail for the recursive UCB process. -/
theorem measure_mean_le_realEmpiricalMean_sub_realWidth_rpow_bound
    {K : Nat} (hK : 0 < K) (c : Real)
    (nu : Kernel (Fin K) Real) [IsMarkovKernel nu]
    (arm : Fin K) (mean : Real) (sigma2 : NNReal)
    (hsubG : HasSubgaussianMGF
      (fun reward => reward - mean) sigma2 (nu arm))
    (hc : 0 <= c) (hsigma2 : sigma2 ≠ 0) (n : Nat) :
    armStreamMeasure nu {stream : ArmRewardStream K |
        0 < pullCount
            (armStreamAction hK (c * (sigma2 : Real)) stream) arm n /\
        mean <=
          realEmpiricalMean
              (armStreamAction hK (c * (sigma2 : Real)) stream)
              (armStreamReward hK (c * (sigma2 : Real)) stream) arm n -
            realWidth
              (armStreamAction hK (c * (sigma2 : Real)) stream)
              (c * (sigma2 : Real)) arm n} <=
      (1 : ENNReal) /
        (((n + 1 : Nat) : ENNReal) ^ (c - 1)) := by
  exact (measure_mean_le_realEmpiricalMean_sub_realWidth_log_bound
    hK c nu arm mean sigma2 hsubG hc hsigma2 n).trans
      (natCast_mul_exp_neg_log_le_inv_rpow_sub_one c n)

end UCB
end BanditRLProof
