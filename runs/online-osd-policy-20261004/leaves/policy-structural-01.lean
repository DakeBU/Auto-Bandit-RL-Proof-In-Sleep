import BanditRLProof.OnlineSubgradientDescent
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

end BanditRL.OnlineSubgradientPolicy
