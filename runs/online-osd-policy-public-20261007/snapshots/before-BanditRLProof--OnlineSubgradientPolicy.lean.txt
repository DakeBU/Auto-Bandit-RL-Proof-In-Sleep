import BanditRLProof.OnlineSubgradientDescent

/-!
# Projected subgradient descent with arbitrary legal history-dependent supports
Orabona arXiv:1912.13213v10, Algorithm 2.2 / Lemma 2.31 and the explicit
Theorem 2.13 / equation (2.1) transfer (printed 19-21 and 13-15).
A support policy sees finite past losses/outputs and the current whole loss.
The actual history appends the shared nearest projection of the actual update.
Performance requires legal supports only at played points; the stronger off-path
oracle law is an optional sufficient adapter. Fixed and decreasing step bounds
keep the negative terminal squared-distance term. The fixed branch allows T=0
and unbounded domains. Tuning is for the same horizon-prescribed run with
D,G,T>0, not an anytime or future-support-energy optimizer.
Source round 1 is Lean time 0; output at T is source x_(T+1).
The prefix theorem compares a common exogenous policy/initialization and equal
strict-past loss functions/step schedules. It does not constrain how external
parameters were selected. This is deterministic pathwise full information,
with mathematical noncomputable choices, not a randomized adaptive-law API.
Canonical bridges recover the previously defined current-loss chooser exactly.
-/
noncomputable section
open Set Finset BanditRL.OnlineConvex
namespace BanditRL.OnlineSubgradientPolicy
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
abbrev Domain := BanditRL.OnlineGradientDescent.Domain E
abbrev SupportPolicy := (t : ℕ) → (Fin t → E → EReal) → (Fin (t + 1) → E) → (E → EReal) → E
/-- Only finite past losses/outputs and the currently observed loss are inputs. -/
def history (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) : (t : ℕ) → Fin (t + 1) → E :=
  Nat.rec (motive := fun t => Fin (t + 1) → E) (fun _ => x₁)
    (fun t h => Fin.snoc h
      (BanditRL.OnlineGradientDescent.project V
        (h (Fin.last t) - η t • p t (fun i => loss i.val) h (loss t))))
def output (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (t : ℕ) : E :=
  history V η loss x₁ p t (Fin.last t)
def selected (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (t : ℕ) : E :=
  p t (fun i => loss i.val) (history V η loss x₁ p t) (loss t)
def OracleLaw (V : Domain (E := E)) (p : SupportPolicy (E := E)) : Prop :=
  ∀ t past h f, BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V f →
    h (Fin.last t) ∈ V.carrier → p t past h f ∈ SourceSubdifferential f (h (Fin.last t))
def canonicalPolicy : SupportPolicy (E := E) := fun t _ h f =>
  BanditRL.OnlineSubgradientDescent.currentSubgradient f (h (Fin.last t))
/-- Legality is imposed only at the actual played points, not at off-path histories. -/
def LegalFeedback (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (T : ℕ) : Prop :=
  ∀ t < T, selected V η loss x₁ p t ∈ SourceSubdifferential (loss t) (output V η loss x₁ p t)
def regret (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (u : E) (T : ℕ) : ℝ :=
  ∑ t ∈ range T, ((loss t (output V η loss x₁ p t)).toReal - (loss t u).toReal)
theorem history_zero (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) :
    history V η loss x₁ p 0 = fun _ => x₁ := by
  rfl

theorem history_succ (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (t : ℕ) :
    history V η loss x₁ p (t + 1) =
      Fin.snoc (history V η loss x₁ p t)
        (BanditRL.OnlineGradientDescent.project V
          (output V η loss x₁ p t - η t • selected V η loss x₁ p t)) := by
  rfl

theorem output_zero (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) :
    output V η loss x₁ p 0 = x₁ := by
  rfl

theorem output_succ (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (t : ℕ) :
    output V η loss x₁ p (t + 1) =
      BanditRL.OnlineGradientDescent.project V
        (output V η loss x₁ p t - η t • selected V η loss x₁ p t) := by
  simp only [output, history, Fin.snoc_last, selected]

theorem history_mem (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (hx₁ : x₁ ∈ V.carrier) (t : ℕ) (i : Fin (t + 1)) :
    history V η loss x₁ p t i ∈ V.carrier := by
  induction t with
  | zero => simpa only [history] using hx₁
  | succ t ih =>
    rw [history_succ]
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snoc_last] using (BanditRL.OnlineGradientDescent.project_spec V _).1
    · simpa only [Fin.snoc_castSucc] using ih j

theorem output_mem (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (hx₁ : x₁ ∈ V.carrier) (t : ℕ) :
    output V η loss x₁ p t ∈ V.carrier := by
  exact history_mem V η loss x₁ p hx₁ t (Fin.last t)

theorem history_prefix (V : Domain (E := E)) (η η' : ℕ → ℝ)
    (loss loss' : ℕ → E → EReal) (x₁ : E) (p : SupportPolicy (E := E)) (t : ℕ)
    (hη : ∀ s < t, η s = η' s) (hloss : ∀ s < t, loss s = loss' s) :
    history V η loss x₁ p t = history V η' loss' x₁ p t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hh := ih (fun s hs => hη s (Nat.lt_succ_of_lt hs))
      (fun s hs => hloss s (Nat.lt_succ_of_lt hs))
    have hpast : (fun i : Fin t => loss i.val) = fun i : Fin t => loss' i.val := by
      funext i
      exact hloss i.val (Nat.lt_succ_of_lt i.isLt)
    simp only [history_succ, output, selected, hh, hpast,
      hη t (Nat.lt_succ_self t), hloss t (Nat.lt_succ_self t)]

theorem output_prefix (V : Domain (E := E)) (η η' : ℕ → ℝ)
    (loss loss' : ℕ → E → EReal) (x₁ : E) (p : SupportPolicy (E := E)) (t : ℕ)
    (hη : ∀ s < t, η s = η' s) (hloss : ∀ s < t, loss s = loss' s) :
    output V η loss x₁ p t = output V η' loss' x₁ p t := by
  exact congrArg (fun h : Fin (t + 1) → E => h (Fin.last t))
    (history_prefix V η η' loss loss' x₁ p t hη hloss)


theorem oracle_feedback (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (hx₁ : x₁ ∈ V.carrier) (T : ℕ)
    (hp : OracleLaw V p)
    (hloss : ∀ t < T, BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t)) :
    LegalFeedback V η loss x₁ p T := by
  intro t ht
  exact hp t (fun i => loss i.val) (history V η loss x₁ p t) (loss t)
    (hloss t ht) (output_mem V η loss x₁ p hx₁ t)

theorem trajectory_finite_loss (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (hx₁ : x₁ ∈ V.carrier) (t : ℕ)
    (hloss : BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t))
    (u : E) (hu : u ∈ V.carrier) :
    loss t (output V η loss x₁ p t) = ((loss t (output V η loss x₁ p t)).toReal : EReal) ∧
    loss t u = ((loss t u).toReal : EReal) := by
  exact ⟨BanditRL.OnlineSubgradientDescent.finite_loss V (loss t) hloss _
      (output_mem V η loss x₁ p hx₁ t),
    BanditRL.OnlineSubgradientDescent.finite_loss V (loss t) hloss u hu⟩

theorem one_step_chain (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (t : ℕ) (hη : 0 < η t)
    (hloss : BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t))
    (hg : selected V η loss x₁ p t ∈ SourceSubdifferential (loss t) (output V η loss x₁ p t))
    (u : E) (hu : u ∈ V.carrier) :
    η t * ((loss t (output V η loss x₁ p t)).toReal - (loss t u).toReal) ≤
      η t * inner ℝ (selected V η loss x₁ p t) (output V η loss x₁ p t - u) ∧
    η t * inner ℝ (selected V η loss x₁ p t) (output V η loss x₁ p t - u) ≤
      ‖output V η loss x₁ p t - u‖ ^ 2 / 2 -
      ‖output V η loss x₁ p (t + 1) - u‖ ^ 2 / 2 +
      (η t) ^ 2 / 2 * ‖selected V η loss x₁ p t‖ ^ 2 := by
  simpa only [output_succ] using
    BanditRL.OnlineSubgradientDescent.lemma_2_31 V (loss t) hloss (η t) hη
      (output V η loss x₁ p t) u hu (selected V η loss x₁ p t) hg

theorem one_step (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (t : ℕ) (hη : 0 < η t)
    (hloss : BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t))
    (hg : selected V η loss x₁ p t ∈ SourceSubdifferential (loss t) (output V η loss x₁ p t))
    (u : E) (hu : u ∈ V.carrier) :
    (loss t (output V η loss x₁ p t)).toReal - (loss t u).toReal ≤
      (‖output V η loss x₁ p t - u‖ ^ 2 -
        ‖output V η loss x₁ p (t + 1) - u‖ ^ 2) / (2 * η t) +
      η t / 2 * ‖selected V η loss x₁ p t‖ ^ 2 := by
  have hs := one_step_chain V η loss x₁ p t hη hloss hg u hu
  apply le_of_mul_le_mul_left (a := η t) _ hη
  calc
    η t * ((loss t (output V η loss x₁ p t)).toReal - (loss t u).toReal) ≤
        ‖output V η loss x₁ p t - u‖ ^ 2 / 2 -
        ‖output V η loss x₁ p (t + 1) - u‖ ^ 2 / 2 +
        (η t) ^ 2 / 2 * ‖selected V η loss x₁ p t‖ ^ 2 := hs.1.trans hs.2
    _ = η t * ((‖output V η loss x₁ p t - u‖ ^ 2 -
        ‖output V η loss x₁ p (t + 1) - u‖ ^ 2) / (2 * η t) +
        η t / 2 * ‖selected V η loss x₁ p t‖ ^ 2) := by field_simp


theorem regret_fixed (V : Domain (E := E)) (η : ℝ) (hη : 0 < η)
    (loss : ℕ → E → EReal) (x₁ : E) (p : SupportPolicy (E := E))
    (hx₁ : x₁ ∈ V.carrier) (T : ℕ)
    (hloss : ∀ t < T, BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t))
    (hlegal : LegalFeedback V (fun _ => η) loss x₁ p T) (u : E) (hu : u ∈ V.carrier) :
    regret V (fun _ => η) loss x₁ p u T ≤ ‖x₁ - u‖ ^ 2 / (2 * η) +
      η / 2 * (∑ t ∈ range T, ‖selected V (fun _ => η) loss x₁ p t‖ ^ 2) -
      ‖output V (fun _ => η) loss x₁ p T - u‖ ^ 2 / (2 * η) := by
  have hscaled : η * regret V (fun _ => η) loss x₁ p u T ≤
      ‖x₁ - u‖ ^ 2 / 2 - ‖output V (fun _ => η) loss x₁ p T - u‖ ^ 2 / 2 +
      η ^ 2 / 2 * (∑ t ∈ range T, ‖selected V (fun _ => η) loss x₁ p t‖ ^ 2) := by
    induction T with
    | zero => simp [regret, output_zero]
    | succ T ih =>
      have hi := ih (fun t ht => hloss t (Nat.lt_succ_of_lt ht))
        (fun t ht => hlegal t (Nat.lt_succ_of_lt ht))
      have hs := one_step_chain V (fun _ => η) loss x₁ p T hη
        (hloss T (Nat.lt_succ_self T)) (hlegal T (Nat.lt_succ_self T)) u hu
      simp only [regret, sum_range_succ, mul_add] at hi ⊢
      nlinarith [hs.1.trans hs.2]
  apply le_of_mul_le_mul_left (a := η) _ hη
  calc
    η * regret V (fun _ => η) loss x₁ p u T ≤ _ := hscaled
    _ = η * (‖x₁ - u‖ ^ 2 / (2 * η) +
        η / 2 * (∑ t ∈ range T, ‖selected V (fun _ => η) loss x₁ p t‖ ^ 2) -
        ‖output V (fun _ => η) loss x₁ p T - u‖ ^ 2 / (2 * η)) := by field_simp; ring

theorem regret_fixed_coarse (V : Domain (E := E)) (η : ℝ) (hη : 0 < η)
    (loss : ℕ → E → EReal) (x₁ : E) (p : SupportPolicy (E := E))
    (hx₁ : x₁ ∈ V.carrier) (T : ℕ)
    (hloss : ∀ t < T, BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t))
    (hlegal : LegalFeedback V (fun _ => η) loss x₁ p T) (u : E) (hu : u ∈ V.carrier) :
    regret V (fun _ => η) loss x₁ p u T ≤ ‖x₁ - u‖ ^ 2 / (2 * η) +
      η / 2 * (∑ t ∈ range T, ‖selected V (fun _ => η) loss x₁ p t‖ ^ 2) := by
  have hb := regret_fixed V η hη loss x₁ p hx₁ T hloss hlegal u hu
  have ht : 0 ≤ ‖output V (fun _ => η) loss x₁ p T - u‖ ^ 2 / (2 * η) := by positivity
  linarith

theorem regret_variable_bound (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (hx₁ : x₁ ∈ V.carrier) (T : ℕ) (hT : 0 < T)
    (hη : ∀ t < T, 0 < η t) (hmono : ∀ t, t + 1 < T → η (t + 1) ≤ η t)
    (hloss : ∀ t < T, BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t))
    (hlegal : LegalFeedback V η loss x₁ p T) (D : ℝ)
    (hdiam : ∀ x ∈ V.carrier, ∀ y ∈ V.carrier, ‖x - y‖ ≤ D)
    (u : E) (hu : u ∈ V.carrier) :
    regret V η loss x₁ p u T ≤ D ^ 2 / (2 * η (T - 1)) +
      (∑ t ∈ range T, η t / 2 * ‖selected V η loss x₁ p t‖ ^ 2) -
      ‖output V η loss x₁ p T - u‖ ^ 2 / (2 * η (T - 1)) := by
  have hp := BanditRL.OnlineGradientDescent.weighted_potential_sum
    (fun t => ‖output V η loss x₁ p t - u‖ ^ 2) η (D ^ 2) T hT hη hmono
    (fun t ht => pow_le_pow_left₀ (norm_nonneg _)
      (hdiam _ (output_mem V η loss x₁ p hx₁ t) u hu) 2)
  have hs := Finset.sum_le_sum (s := range T) (fun t ht =>
    one_step V η loss x₁ p t (hη t (mem_range.mp ht))
      (hloss t (mem_range.mp ht)) (hlegal t (mem_range.mp ht)) u hu)
  rw [sum_add_distrib] at hs
  change regret V η loss x₁ p u T ≤ _ at hs
  linarith

theorem regret_variable (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (hx₁ : x₁ ∈ V.carrier) (T : ℕ) (hT : 0 < T)
    (hη : ∀ t < T, 0 < η t) (hmono : ∀ t, t + 1 < T → η (t + 1) ≤ η t)
    (hloss : ∀ t < T, BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t))
    (hlegal : LegalFeedback V η loss x₁ p T) (hV : Bornology.IsBounded V.carrier) (u : E) (hu : u ∈ V.carrier) :
    regret V η loss x₁ p u T ≤ (Metric.diam V.carrier) ^ 2 / (2 * η (T - 1)) +
      (∑ t ∈ range T, η t / 2 * ‖selected V η loss x₁ p t‖ ^ 2) -
      ‖output V η loss x₁ p T - u‖ ^ 2 / (2 * η (T - 1)) := by
  apply regret_variable_bound V η loss x₁ p hx₁ T hT hη hmono hloss hlegal
    (Metric.diam V.carrier) ?_ u hu
  intro x hx y hy
  simpa only [dist_eq_norm] using Metric.dist_le_diam_of_mem hV hx hy

theorem regret_tuned_distance (V : Domain (E := E)) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (hx₁ : x₁ ∈ V.carrier)
    (T : ℕ) (hT : 0 < T) (D G : ℝ) (hD : 0 < D) (hG : 0 < G)
    (hloss : ∀ t < T, BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t))
    (hlegal : LegalFeedback V (fun _ => D / (G * Real.sqrt T)) loss x₁ p T) (u : E) (hu : u ∈ V.carrier)
    (hdist : ‖x₁ - u‖ ≤ D)
    (hgrad : ∀ t < T, ‖selected V (fun _ => D / (G * Real.sqrt T)) loss x₁ p t‖ ≤ G) :
    regret V (fun _ => D / (G * Real.sqrt T)) loss x₁ p u T ≤ D * G * Real.sqrt T := by
  have hTreal : 0 < (T : ℝ) := Nat.cast_pos.mpr hT
  have hsqrt : 0 < Real.sqrt (T : ℝ) := Real.sqrt_pos.mpr hTreal
  have hη : 0 < D / (G * Real.sqrt T) := div_pos hD (mul_pos hG hsqrt)
  have hb := regret_fixed V (D / (G * Real.sqrt T)) hη loss x₁ p hx₁ T hloss hlegal u hu
  have hdist2 : ‖x₁ - u‖ ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hdist 2
  have hsum : (∑ t ∈ range T,
      ‖selected V (fun _ => D / (G * Real.sqrt T)) loss x₁ p t‖ ^ 2) ≤
      (T : ℝ) * G ^ 2 := by
    calc
      _ ≤ ∑ _t ∈ range T, G ^ 2 := sum_le_sum fun t ht =>
        pow_le_pow_left₀ (norm_nonneg _) (hgrad t (mem_range.mp ht)) 2
      _ = _ := by simp
  have hinit := div_le_div_of_nonneg_right hdist2 (by positivity :
    0 ≤ 2 * (D / (G * Real.sqrt T)))
  have henergy := mul_le_mul_of_nonneg_left hsum (by positivity :
    0 ≤ (D / (G * Real.sqrt T)) / 2)
  have hterminal : 0 ≤ ‖output V (fun _ => D / (G * Real.sqrt T)) loss x₁ p T - u‖ ^ 2 /
      (2 * (D / (G * Real.sqrt T))) := by positivity
  have htune : D ^ 2 / (2 * (D / (G * Real.sqrt T))) +
      (D / (G * Real.sqrt T)) / 2 * ((T : ℝ) * G ^ 2) = D * G * Real.sqrt T := by
    have hsq := Real.sq_sqrt (Nat.cast_nonneg T)
    field_simp
    nlinarith
  linarith

theorem regret_tuned (V : Domain (E := E)) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (hx₁ : x₁ ∈ V.carrier)
    (T : ℕ) (hT : 0 < T) (D G : ℝ) (hD : 0 < D) (hG : 0 < G)
    (hloss : ∀ t < T, BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t))
    (hlegal : LegalFeedback V (fun _ => D / (G * Real.sqrt T)) loss x₁ p T)
    (hdiam : ∀ x ∈ V.carrier, ∀ y ∈ V.carrier, ‖x - y‖ ≤ D)
    (hgrad : ∀ t < T, ‖selected V (fun _ => D / (G * Real.sqrt T)) loss x₁ p t‖ ≤ G) :
    ∀ u ∈ V.carrier,
      regret V (fun _ => D / (G * Real.sqrt T)) loss x₁ p u T ≤ D * G * Real.sqrt T := by
  intro u hu
  exact regret_tuned_distance V loss x₁ p hx₁ T hT D G hD hG hloss hlegal u hu
    (hdiam x₁ hx₁ u hu) hgrad

theorem canonicalPolicy_legal (V : Domain (E := E)) :
    OracleLaw V (canonicalPolicy (E := E)) := by
  intro t past h f hf hx
  exact BanditRL.OnlineSubgradientDescent.currentSubgradient_mem V f hf _ hx

theorem canonical_output (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (t : ℕ) :
    output V η loss x₁ canonicalPolicy t =
      BanditRL.OnlineSubgradientDescent.iterate V η loss x₁ t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [output_succ]
    change BanditRL.OnlineGradientDescent.project V
      (output V η loss x₁ canonicalPolicy t - η t •
        BanditRL.OnlineSubgradientDescent.currentSubgradient (loss t)
          (output V η loss x₁ canonicalPolicy t)) = _
    rw [ih]
    rfl

theorem canonical_selected (V : Domain (E := E)) (η : ℕ → ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (t : ℕ) :
    selected V η loss x₁ canonicalPolicy t =
      BanditRL.OnlineSubgradientDescent.currentSubgradient (loss t)
        (BanditRL.OnlineSubgradientDescent.iterate V η loss x₁ t) := by
  change BanditRL.OnlineSubgradientDescent.currentSubgradient (loss t)
    (output V η loss x₁ canonicalPolicy t) = _
  rw [canonical_output]

end BanditRL.OnlineSubgradientPolicy
