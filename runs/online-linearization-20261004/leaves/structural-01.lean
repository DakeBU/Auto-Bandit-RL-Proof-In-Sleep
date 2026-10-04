import BanditRLProof.OnlineSubgradientPolicy
import BanditRLProof.OnlineLearningRegret
noncomputable section
open Set Finset BanditRL.OnlineConvex
namespace BanditRL.OnlineLinearization
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
abbrev Domain := BanditRL.OnlineGradientDescent.Domain E
abbrev LinearPolicy := (t : ℕ) → (Fin t → E) → E
abbrev SupportPolicy := BanditRL.OnlineSubgradientPolicy.SupportPolicy (E := E)
def Feasible (V : Domain (E := E)) (A : LinearPolicy (E := E)) : Prop :=
  ∀ t h, A t h ∈ V.carrier
/-- Reconstruct all outputs from a finite strict-past vector history. -/
def outputHistory (A : LinearPolicy (E := E)) {t : ℕ} (h : Fin t → E) : Fin (t + 1) → E :=
  fun i => A i.val (fun j => h ⟨j.val, by omega⟩)
/-- The current support is appended only after the current output has been made. -/
def history (A : LinearPolicy (E := E)) (loss : ℕ → E → EReal)
    (p : SupportPolicy (E := E)) : (t : ℕ) → Fin t → E :=
  Nat.rec (motive := fun t => Fin t → E) Fin.elim0
    (fun t h => Fin.snoc h (p t (fun i => loss i.val) (outputHistory A h) (loss t)))
def output (A : LinearPolicy (E := E)) (loss : ℕ → E → EReal)
    (p : SupportPolicy (E := E)) (t : ℕ) : E := A t (history A loss p t)
def selected (A : LinearPolicy (E := E)) (loss : ℕ → E → EReal)
    (p : SupportPolicy (E := E)) (t : ℕ) : E :=
  p t (fun i => loss i.val) (outputHistory A (history A loss p t)) (loss t)
def LegalFeedback (A : LinearPolicy (E := E)) (loss : ℕ → E → EReal)
    (p : SupportPolicy (E := E)) (T : ℕ) : Prop :=
  ∀ t < T, selected A loss p t ∈ SourceSubdifferential (loss t) (output A loss p t)
def linearRun (A : LinearPolicy (E := E)) (g : ℕ → E) (t : ℕ) : E :=
  A t (fun i => g i.val)
def linearLoss (g x : E) : ℝ := inner ℝ g x
def regret (A : LinearPolicy (E := E)) (loss : ℕ → E → EReal)
    (p : SupportPolicy (E := E)) (u : E) (T : ℕ) : ℝ :=
  ∑ t ∈ range T, ((loss t (output A loss p t)).toReal - (loss t u).toReal)
theorem outputHistory_last (A : LinearPolicy (E := E)) (t : ℕ) (h : Fin t → E) :
    outputHistory A h (Fin.last t) = A t h := by
  rfl

theorem history_zero (A : LinearPolicy (E := E)) (loss : ℕ → E → EReal) (p : SupportPolicy (E := E)) :
    history A loss p 0 = Fin.elim0 := by
  rfl

theorem history_succ (A : LinearPolicy (E := E)) (loss : ℕ → E → EReal) (p : SupportPolicy (E := E)) (t : ℕ) :
    history A loss p (t + 1) = Fin.snoc (history A loss p t) (selected A loss p t) := by
  rfl

theorem history_castSucc (A : LinearPolicy (E := E)) (loss : ℕ → E → EReal) (p : SupportPolicy (E := E)) (t : ℕ) (i : Fin t) :
    history A loss p (t + 1) i.castSucc = history A loss p t i := by
  rw [history_succ, Fin.snoc_castSucc]

theorem history_selected (A : LinearPolicy (E := E)) (loss : ℕ → E → EReal) (p : SupportPolicy (E := E)) (t : ℕ) (i : Fin t) :
    history A loss p t i = selected A loss p i.val := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [history_succ, Fin.snoc_last, Fin.val_last]
    · rw [history_castSucc]
      exact ih j

theorem output_linear_run (A : LinearPolicy (E := E)) (loss : ℕ → E → EReal) (p : SupportPolicy (E := E)) (t : ℕ) :
    output A loss p t = linearRun A (selected A loss p) t := by
  unfold output linearRun
  congr 1
  funext i
  exact history_selected A loss p t i

theorem outputHistory_played (A : LinearPolicy (E := E)) (loss : ℕ → E → EReal) (p : SupportPolicy (E := E)) (t : ℕ) (i : Fin (t + 1)) :
    outputHistory A (history A loss p t) i = output A loss p i.val := by
  unfold outputHistory output
  congr 1
  funext j
  rw [history_selected, history_selected]

theorem output_mem (V : Domain (E := E)) (A : LinearPolicy (E := E)) (hA : Feasible V A) (loss : ℕ → E → EReal) (p : SupportPolicy (E := E)) (t : ℕ) :
    output A loss p t ∈ V.carrier := by
  exact hA t (history A loss p t)

theorem history_prefix (A : LinearPolicy (E := E)) (loss loss' : ℕ → E → EReal) (p : SupportPolicy (E := E)) (t : ℕ) (hloss : ∀ s < t, loss s = loss' s) :
    history A loss p t = history A loss' p t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hh := ih (fun s hs => hloss s (Nat.lt_succ_of_lt hs))
    have hpast : (fun i : Fin t => loss i.val) = fun i : Fin t => loss' i.val := by
      funext i
      exact hloss i.val (Nat.lt_succ_of_lt i.isLt)
    rw [history_succ, history_succ]
    unfold selected
    rw [hh, hpast, hloss t (Nat.lt_succ_self t)]

theorem output_prefix (A : LinearPolicy (E := E)) (loss loss' : ℕ → E → EReal) (p : SupportPolicy (E := E)) (t : ℕ) (hloss : ∀ s < t, loss s = loss' s) :
    output A loss p t = output A loss' p t := by
  exact congrArg (A t) (history_prefix A loss loss' p t hloss)

end BanditRL.OnlineLinearization
