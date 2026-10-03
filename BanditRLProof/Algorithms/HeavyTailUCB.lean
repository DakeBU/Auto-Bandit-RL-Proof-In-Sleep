import BanditRLProof.Algorithms.HeavyTailHistory

/-! Causal robust UCB with the audited conservative confidence schedule.
Time is zero-based; the logarithm uses max(t,2), and failure probability t^-4
is the explicit repair recorded in DERIVATION.md. No regret endpoint is claimed here. -/
namespace BanditRLProof.HeavyTail
open MeasureTheory
variable {K : ℕ}

noncomputable def confidenceLog (t : ℕ) : ℝ := 4 * Real.log (max (t : ℝ) 2)

noncomputable def sampleThreshold (ε u : ℝ) (t s : ℕ) : ℝ :=
  (u * (s+1) / confidenceLog t) ^ (1 / (1+ε))

noncomputable def confidenceRadius (ε u : ℝ) (t count : ℕ) : ℝ :=
  8 * u ^ (1 / (1+ε)) * (confidenceLog t / count) ^ (ε / (1+ε))

noncomputable def historyIndex (initial : Fin K) (ε u : ℝ) (n : ℕ)
    (h : History.FinitePairHistory (Fin K) ℝ n) (arm : Fin K) : ℝ :=
  historyTruncatedMean initial (sampleThreshold ε u (n+1)) n h arm +
    confidenceRadius ε u (n+1) (pullCount (historyAction initial n h) arm (n+1))

noncomputable def nextArm (hK : 0 < K) (ε u : ℝ) (n : ℕ)
    (h : History.FinitePairHistory (Fin K) ℝ n) : Fin K :=
  if n+1 < K then UCB.initializationArm hK (n+1) else
    ETC.realLeastEncodedArgmax hK (historyIndex (UCB.initializationArm hK 0) ε u n h)

theorem measurable_historyIndex (initial : Fin K) (ε u : ℝ) (n : ℕ) (arm : Fin K) :
    Measurable (fun h => historyIndex initial ε u n h arm) := by
  exact (measurable_historyTruncatedMean initial _ n arm).add
    ((measurable_of_countable (confidenceRadius ε u (n+1))).comp
      (measurable_pullCount (historyAction initial n) (measurable_historyAction initial n)
        arm (n+1)))

theorem measurable_nextArm (hK : 0 < K) (ε u : ℝ) (n : ℕ) :
    Measurable (nextArm hK ε u n) := by
  change Measurable (fun h => nextArm hK ε u n h)
  by_cases hn : n+1 < K
  · simp only [nextArm, if_pos hn]
    exact measurable_const
  · simp only [nextArm, if_neg hn, ETC.realLeastEncodedArgmax_eq_realArgmaxCommit]
    apply ETC.measurable_realArgmaxCommit_of_forall_measurable
    exact measurable_historyIndex _ ε u n

noncomputable def robustAction (hK : 0 < K) (ε u : ℝ) :=
  ArmStreamPolicy.action (UCB.initializationArm hK 0) (nextArm hK ε u)

noncomputable def robustReward (hK : 0 < K) (ε u : ℝ) :=
  ArmStreamPolicy.reward (UCB.initializationArm hK 0) (nextArm hK ε u)

theorem measurable_robustAction (hK : 0 < K) (ε u : ℝ) (t : ℕ) :
    Measurable (fun stream => robustAction hK ε u stream t) := by
  exact ArmStreamPolicy.measurable_action _ _ (measurable_nextArm hK ε u) t

theorem robustAction_initialization (hK : 0 < K) (ε u : ℝ)
    (stream : UCB.ArmRewardStream K) (t : ℕ) (ht : t < K) :
    robustAction hK ε u stream t = UCB.initializationArm hK t := by
  cases t with
  | zero => rfl
  | succ t => simp [robustAction, ArmStreamPolicy.action_succ, nextArm, ht]

/-- The selected index is maximal on the actual observed history. -/
theorem robustAction_maximizes (hK : 0 < K) (ε u : ℝ)
    (stream : UCB.ArmRewardStream K) (n : ℕ) (hn : K ≤ n+1) (arm : Fin K) :
    let h := ArmStreamPolicy.history (UCB.initializationArm hK 0) (nextArm hK ε u) stream n
    historyIndex (UCB.initializationArm hK 0) ε u n h arm ≤
      historyIndex (UCB.initializationArm hK 0) ε u n h (robustAction hK ε u stream (n+1)) := by
  dsimp only
  simp only [robustAction, ArmStreamPolicy.action_succ, nextArm, if_neg (not_lt.mpr hn)]
  exact ETC.realLeastEncodedArgmax_spec hK _ arm

end BanditRLProof.HeavyTail
