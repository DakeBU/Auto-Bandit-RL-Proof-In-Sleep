import BanditRLProof.OnlineSubgradientPolicy
noncomputable section
open Set Finset Filter BanditRL.OnlineConvex
namespace NeutralScalarHistory
abbrev W := BanditRL.OnlineGradientDescent.unitInterval
abbrev F := BanditRL.OnlineSubgradientPolicy.SupportPolicy (E := ℝ)
abbrev X := BanditRL.OnlineSubgradientPolicy.output
abbrev A := BanditRL.OnlineSubgradientPolicy.selected
abbrev L := BanditRL.OnlineSubgradientPolicy.LegalFeedback
def b (y x : ℝ) : EReal := ((|x-y| : ℝ) : EReal)
def Q01 : Prop :=
  ∀ (η : ℕ → ℝ) (y : ℕ → ℝ) (x₁ : ℝ)
    (p : F) (T : ℕ)
    (hlegal : L W η (fun s => b (y s)) x₁ p T)
    (t : ℕ) (ht : t < T),
    ‖A W η (fun s => b (y s)) x₁ p t‖ ≤ 1

def Q02 : Prop :=
  ∀ (η : ℕ → ℝ) (y : ℕ → ℝ) (x₁ : ℝ)
    (p : F) (t : ℕ),
    X W η (fun s => b (y s)) x₁ p (t + 1) =
      min (max (X W η (fun s => b (y s)) x₁ p t -
        η t * A W η (fun s => b (y s)) x₁ p t) 0) 1

def Q03 : Prop :=
  ∀ (y : ℕ → ℝ) (x₁ : ℝ) (p : F)
    (hx₁ : x₁ ∈ Icc (0 : ℝ) 1) (T : ℕ) (hT : 0 < T)
    (hy : ∀ t < T, y t ∈ Icc (0 : ℝ) 1)
    (hlegal : L W (fun _ => 1 / Real.sqrt T)
      (fun s => b (y s)) x₁ p T),
    ∀ u ∈ Icc (0 : ℝ) 1,
      (∑ t ∈ range T,
        (|X W (fun _ => 1 / Real.sqrt T)
          (fun s => b (y s)) x₁ p t - y t| - |u - y t|)) ≤ Real.sqrt T

def Q04 : Prop :=
  ∀ (y : ℕ → ℝ) (x₁ : ℝ)
    (p : F) (hx₁ : x₁ ∈ Icc (0 : ℝ) 1)
    (hy : ∀ t, y t ∈ Icc (0 : ℝ) 1)
    (hlegal : ∀ T : ℕ, 0 < T → L W
      (fun _ => 1 / Real.sqrt T) (fun s => b (y s)) x₁ p T)
    (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) (ε : ℝ) (hε : 0 < ε),
    ∀ᶠ T : ℕ in atTop,
      (∑ t ∈ range T,
        (|X W (fun _ => 1 / Real.sqrt T)
          (fun s => b (y s)) x₁ p t - y t| - |u - y t|)) / T < ε
end NeutralScalarHistory
