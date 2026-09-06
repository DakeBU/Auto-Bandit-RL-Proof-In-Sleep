import BanditRLProof.Algorithms.MOSSRegret
import BanditRLProof.Algorithms.MOSSHistory
import BanditRLProof.ExpectationRegretPullCount

noncomputable section
open MeasureTheory
namespace BanditRLProof.MOSS
variable {Ω : Type*} [MeasurableSpace Ω]

theorem measurable_streamMean_at_count (X : ℕ → Ω → ℝ)
    (hXm : ∀ i, StronglyMeasurable (X i)) (c : Ω → ℕ) (hc : Measurable c) :
    Measurable (fun ω => streamMean X ω (c ω)) := by
  have hm : Measurable (fun p : Ω × ℕ => streamMean X p.1 p.2) := by
    apply measurable_from_prod_countable_left
    intro s
    unfold streamMean peelingSum
    change Measurable (fun ω => (∑ j ∈ Finset.range s, X (j+1) ω)/(s : ℝ))
    exact (Finset.measurable_sum (Finset.range s) (fun i _ => (hXm (i+1)).measurable)).div_const _
  exact hm.comp (measurable_id.prodMk hc)

theorem measurable_action_of_state {k : ℕ} (hk : 0 < k) (n t : ℕ)
    (emp : Ω → Fin k → ℝ) (counts : Ω → Fin k → ℕ)
    (he : ∀ a, Measurable (fun ω => emp ω a))
    (hc : ∀ a, Measurable (fun ω => counts ω a)) :
    Measurable (fun ω => action hk n t (emp ω) (counts ω)) := by
  unfold action
  split_ifs
  · exact measurable_const
  · change Measurable (fun ω => ETC.realArgmaxCommit hk (index n (emp ω) (counts ω)))
    apply ETC.measurable_realArgmaxCommit_of_forall_measurable
    intro a
    exact (he a).add ((measurable_of_countable (radius n k)).comp (hc a))

theorem measurable_streamCounts {k : ℕ} (hk : 0 < k) (n : ℕ)
    (mean : Fin k → ℝ) (X : Fin k → ℕ → Ω → ℝ)
    (hXm : ∀ a i, StronglyMeasurable (X a i)) (t : ℕ) (a : Fin k) :
    Measurable (fun ω => streamCounts hk n mean X ω t a) := by
  induction t generalizing a with
  | zero => exact measurable_const
  | succ t ih =>
      have ha : Measurable (fun ω => action hk n t
          (fun b => mean b + streamMean (X b) ω (streamCounts hk n mean X ω t b))
          (streamCounts hk n mean X ω t)) := by
        apply measurable_action_of_state
        · intro b
          exact measurable_const.add (measurable_streamMean_at_count (X b) (hXm b) _ (ih b))
        · exact ih
      exact (ih a).add (Measurable.ite (measurableSet_eq_fun ha measurable_const)
        measurable_const measurable_const)

theorem measurable_streamTrace {k : ℕ} (hk : 0 < k) (n : ℕ)
    (mean : Fin k → ℝ) (X : Fin k → ℕ → Ω → ℝ)
    (hXm : ∀ a i, StronglyMeasurable (X a i)) (t : ℕ) :
    Measurable (fun ω => streamTrace hk n mean X ω t) := by
  apply measurable_action_of_state
  · intro a
    exact measurable_const.add (measurable_streamMean_at_count (X a) (hXm a) _
      (measurable_streamCounts hk n mean X hXm t a))
  · exact measurable_streamCounts hk n mean X hXm t

theorem integrable_streamTrace_regret (μ : Measure Ω) [IsFiniteMeasure μ]
    {k : ℕ} (hk : 0 < k) (n : ℕ) (mean : Fin k → ℝ) (X : Fin k → ℕ → Ω → ℝ)
    (hXm : ∀ a i, StronglyMeasurable (X a i)) :
    Integrable (fun ω => realMeanRegret mean (streamTrace hk n mean X ω) n) μ := by
  apply integrable_realMeanRegret_of_integrable_pullCount
  intro a
  exact integrable_real_pullCount_of_measurable_action μ (streamTrace hk n mean X)
    (measurable_streamTrace hk n mean X hXm) a n

end BanditRLProof.MOSS
