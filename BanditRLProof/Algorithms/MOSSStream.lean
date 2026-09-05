import BanditRLProof.Algorithms.MOSSExpectedOccupancy

noncomputable section
open Real
namespace BanditRLProof.MOSS

theorem neg_optimismDeficit_le_centeredIndex {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (δ : ℝ) (n s : ℕ) (ω : Ω) (hs : 0 < s) (hsn : s ≤ n) :
    -optimismDeficit X δ n ω ≤ centeredIndex X δ s ω := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases h : s ≤ n
      · have hi := ih h
        have hm : optimismDeficit X δ n ω ≤ optimismDeficit X δ (n+1) ω := le_max_left _ _
        linarith
      · have he : s = n+1 := by omega
        subst s
        have hm : -centeredIndex X δ (n+1) ω ≤ optimismDeficit X δ (n+1) ω := le_max_right _ _
        linarith

theorem radius_eq_streamRadius (n k s : ℕ) (hn : 0 < n) (hk : 0 < k) :
    radius n k s = sqrt (4/(s : ℝ)*logPlus (1/((s : ℝ)*((k : ℝ)/(n : ℝ))))) := by
  unfold radius
  congr 3
  by_cases hs : s = 0
  · simp [hs]
  · have hnR : (n : ℝ) ≠ 0 := by positivity
    have hkR : (k : ℝ) ≠ 0 := by positivity
    have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast hs
    field_simp

/-- Empirical state indexed by actual arm pulls, using centered reward streams. -/
def streamEmpirical {Ω : Type*} {k : ℕ} (mean : Fin k → ℝ)
    (X : Fin k → ℕ → Ω → ℝ) (ω : Ω) (trace : ActionTrace (Fin k))
    (t : ℕ) (a : Fin k) : ℝ :=
  mean a + streamMean (X a) ω (pullCount trace a t)

/-- Pathwise large-gap count bound from the MOSS policy equation itself.
The law identifying centered streams with observed rewards is not assumed here. -/
theorem pullCount_le_of_stream_policy {Ω : Type*} [MeasurableSpace Ω]
    {k : ℕ} (hk : 0 < k) (n : ℕ) (hkn : k ≤ n)
    (mean : Fin k → ℝ) (X : Fin k → ℕ → Ω → ℝ) (ω : Ω)
    (trace : ActionTrace (Fin k))
    (hpolicy : ∀ t < n, trace t = action hk n t (streamEmpirical mean X ω trace t)
      (fun a => pullCount trace a t))
    (best chosen : Fin k)
    (hgap : 2 * optimismDeficit (X best) ((k : ℝ)/(n : ℝ)) n ω < mean best - mean chosen) :
    (pullCount trace chosen n : ℝ) ≤ 1 +
      indexExceedanceCount (streamMean (X chosen) ω) ((k : ℝ)/(n : ℝ))
        (mean best - mean chosen) n := by
  have hn : 0 < n := lt_of_lt_of_le hk hkn
  have hinit : ∀ s, (hs : s < k) → trace s = ⟨s, hs⟩ := by
    intro s hs
    rw [hpolicy s (lt_of_lt_of_le hs hkn), action_of_lt hk n s _ _ hs]
  apply pullCount_le_one_add_indexExceedanceCount
  intro t htn hchosen hpos
  have hkt : k ≤ t := by
    by_contra h
    have htk : t < k := by omega
    have hv : chosen.val = t := by
      have he := (hinit t htk).symm.trans hchosen
      exact (congrArg Fin.val he).symm
    have hz : pullCount trace chosen t = 0 := by
      apply pullCount_eq_zero_of_forall_ne
      intro s hst heq
      have hs : s < k := lt_trans hst htk
      have he := (hinit s hs).symm.trans heq
      have hv' := congrArg Fin.val he
      simp only at hv'
      omega
    omega
  have hbestpos : 0 < pullCount trace best t :=
    pullCount_pos_of_eq_before trace best (lt_of_lt_of_le best.isLt hkt)
      (by simpa using hinit best.val best.isLt)
  have hbestle : pullCount trace best t ≤ n :=
    (pullCount_le_time trace best t).trans (Nat.le_of_lt htn)
  have hb := neg_optimismDeficit_le_centeredIndex (X best) ((k : ℝ)/(n : ℝ)) n
    (pullCount trace best t) ω hbestpos hbestle
  have hindex (a : Fin k) :
      index n (streamEmpirical mean X ω trace t) (fun b => pullCount trace b t) a =
        mean a + centeredIndex (X a) ((k : ℝ)/(n : ℝ)) (pullCount trace a t) ω := by
    simp only [index, streamEmpirical, streamMean, centeredIndex,
      radius_eq_streamRadius n k _ hn hk]
    ring
  have ho : mean best - optimismDeficit (X best) ((k : ℝ)/(n : ℝ)) n ω ≤
      index n (streamEmpirical mean X ω trace t) (fun b => pullCount trace b t) best := by
    rw [hindex]
    linarith
  have hsel := selected_index_gt_mean_add_half_gap hk n t mean
    (streamEmpirical mean X ω trace t) (fun b => pullCount trace b t)
    best chosen (optimismDeficit (X best) ((k : ℝ)/(n : ℝ)) n ω) hkt
    ((hpolicy t htn).symm.trans hchosen) ho hgap
  rw [hindex] at hsel
  change (mean best - mean chosen)/2 ≤ centeredIndex (X chosen) ((k : ℝ)/(n : ℝ))
    (pullCount trace chosen t) ω
  linarith

/-- Concrete MOSS execution on a fixed reward table, tracking pre-pull counts. -/
def streamCounts {Ω : Type*} {k : ℕ} (hk : 0 < k) (n : ℕ)
    (mean : Fin k → ℝ) (X : Fin k → ℕ → Ω → ℝ) (ω : Ω) : ℕ → Fin k → ℕ
  | 0 => fun _ => 0
  | t+1 => fun a =>
      let counts := streamCounts hk n mean X ω t
      counts a + if action hk n t (fun b => mean b + streamMean (X b) ω (counts b)) counts = a
        then 1 else 0

def streamTrace {Ω : Type*} {k : ℕ} (hk : 0 < k) (n : ℕ)
    (mean : Fin k → ℝ) (X : Fin k → ℕ → Ω → ℝ) (ω : Ω) : ActionTrace (Fin k) :=
  fun t => action hk n t
    (fun a => mean a + streamMean (X a) ω (streamCounts hk n mean X ω t a))
    (streamCounts hk n mean X ω t)

theorem pullCount_streamTrace {Ω : Type*} {k : ℕ} (hk : 0 < k) (n : ℕ)
    (mean : Fin k → ℝ) (X : Fin k → ℕ → Ω → ℝ) (ω : Ω) (t : ℕ) (a : Fin k) :
    pullCount (streamTrace hk n mean X ω) a t = streamCounts hk n mean X ω t a := by
  induction t with
  | zero => rfl
  | succ t ih =>
      simp only [pullCount_succ, ih, streamCounts, streamTrace]
      rfl

theorem streamTrace_policy {Ω : Type*} {k : ℕ} (hk : 0 < k) (n : ℕ)
    (mean : Fin k → ℝ) (X : Fin k → ℕ → Ω → ℝ) (ω : Ω) (t : ℕ) :
    streamTrace hk n mean X ω t = action hk n t
      (streamEmpirical mean X ω (streamTrace hk n mean X ω) t)
      (fun a => pullCount (streamTrace hk n mean X ω) a t) := by
  unfold streamEmpirical
  simp only [pullCount_streamTrace]
  rfl

/-- Concrete generated-trace bound: no selected-event or policy-equation oracle. -/
theorem streamTrace_pullCount_le {Ω : Type*} [MeasurableSpace Ω]
    {k : ℕ} (hk : 0 < k) (n : ℕ) (hkn : k ≤ n)
    (mean : Fin k → ℝ) (X : Fin k → ℕ → Ω → ℝ) (ω : Ω) (best chosen : Fin k)
    (hgap : 2 * optimismDeficit (X best) ((k : ℝ)/(n : ℝ)) n ω < mean best - mean chosen) :
    (pullCount (streamTrace hk n mean X ω) chosen n : ℝ) ≤ 1 +
      indexExceedanceCount (streamMean (X chosen) ω) ((k : ℝ)/(n : ℝ))
        (mean best - mean chosen) n :=
  pullCount_le_of_stream_policy hk n hkn mean X ω (streamTrace hk n mean X ω)
    (fun t _ => streamTrace_policy hk n mean X ω t) best chosen hgap

end BanditRLProof.MOSS
