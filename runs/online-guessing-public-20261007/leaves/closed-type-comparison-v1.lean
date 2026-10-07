import BanditRLProof.OnlineSubgradientDescent
import BanditRLProof.OnlineSubgradientAbsolute
import BanditRLProof.OnlineGuessingOGD
import BanditRLProof.OnlineGuessingSubgradient
noncomputable section
open Set Finset Filter
namespace NeutralRealLoss
abbrev S (f : ℝ → EReal) (x : ℝ) : Set ℝ := BanditRL.OnlineConvex.SourceSubdifferential f x
abbrev A := BanditRL.OnlineGradientDescent.unitInterval
abbrev W (V : BanditRL.OnlineGradientDescent.Domain ℝ) (f : ℝ → EReal) : Prop := BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V f
abbrev q (f : ℝ → EReal) (x : ℝ) : ℝ := BanditRL.OnlineSubgradientDescent.currentSubgradient f x
abbrev s (V : BanditRL.OnlineGradientDescent.Domain ℝ) (η : ℝ) (f : ℝ → EReal) (x : ℝ) : ℝ := BanditRL.OnlineSubgradientDescent.step V η f x
abbrev z (V : BanditRL.OnlineGradientDescent.Domain ℝ) (η : ℕ → ℝ) (f : ℕ → ℝ → EReal) (x₁ : ℝ) (t : ℕ) : ℝ := BanditRL.OnlineSubgradientDescent.iterate V η f x₁ t
def b (y x : ℝ) : EReal := ((|x - y| : ℝ) : EReal)
def Q01 : Prop :=
  ∀ (y x : ℝ),
  S (b y) x =
      S (fun z : ℝ => ((|z| : ℝ) : EReal)) (x - y)

def Q02 : Prop :=
  ∀ (y x : ℝ) (hxy : y < x),
  S (b y) x = {(1 : ℝ)}

def Q03 : Prop :=
  ∀ (y : ℝ),
  S (b y) y = Icc (-1 : ℝ) 1

def Q04 : Prop :=
  ∀ (y x : ℝ) (hxy : x < y),
  S (b y) x = {(-1 : ℝ)}

def Q05 : Prop :=
  ∀ (y x : ℝ),
  S (b y) x =
      if y < x then {(1 : ℝ)} else if x = y then Icc (-1 : ℝ) 1 else {(-1 : ℝ)}

def Q06 : Prop :=
  ∀ (y : ℝ),
  W A (b y)

def Q07 : Prop :=
  ∀ (y x g : ℝ)
    (hg : g ∈ S (b y) x),
  ‖g‖ ≤ 1

def Q08 : Prop :=
  ∀ (y x : ℝ)
    (hx : x ∈ Icc (0 : ℝ) 1),
  ‖q (b y) x‖ ≤ 1

def Q09 : Prop :=
  ∀ (η y x : ℝ),
  s A η (b y) x =
      min (max (x - η * q (b y) x) 0) 1

def Q10 : Prop :=
  ∀ (η η' : ℕ → ℝ) (y y' : ℕ → ℝ) (x₁ : ℝ) (t : ℕ)
    (hη : ∀ s < t, η s = η' s) (hy : ∀ s < t, y s = y' s),
  z A η (fun s => b (y s)) x₁ t =
      z A η' (fun s => b (y' s)) x₁ t

def Q11 : Prop :=
  ∀ (y : ℕ → ℝ) (x₁ : ℝ) (hx₁ : x₁ ∈ Icc (0 : ℝ) 1)
    (T : ℕ) (hT : 0 < T) (hy : ∀ t < T, y t ∈ Icc (0 : ℝ) 1),
  ∀ u ∈ Icc (0 : ℝ) 1,
      (∑ t ∈ range T,
        (|z A (fun _ => 1 / Real.sqrt T)
          (fun s => b (y s)) x₁ t - y t| - |u - y t|)) ≤ Real.sqrt T

def Q12 : Prop :=
  ∀ (y : ℕ → ℝ) (x₁ : ℝ)
    (hx₁ : x₁ ∈ Icc (0 : ℝ) 1) (hy : ∀ t, y t ∈ Icc (0 : ℝ) 1)
    (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) (ε : ℝ) (hε : 0 < ε),
  ∀ᶠ T : ℕ in atTop,
      (∑ t ∈ range T,
        (|z A (fun _ => 1 / Real.sqrt T)
          (fun s => b (y s)) x₁ t - y t| - |u - y t|)) / T < ε
#check Q01
#check Q02
#check Q03
#check Q04
#check Q05
#check Q06
#check Q07
#check Q08
#check Q09
#check Q10
#check Q11
#check Q12
end NeutralRealLoss
noncomputable section
open Set Finset Filter BanditRL.OnlineConvex BanditRL.OnlineSubgradientDescent
namespace CurrentClosedTypes
open BanditRL.OnlineGuessingSubgradient (loss)
def S01 : Prop :=
  ∀ (y x : ℝ),
  SourceSubdifferential (loss y) x =
      SourceSubdifferential (fun z : ℝ => ((|z| : ℝ) : EReal)) (x - y)

def S02 : Prop :=
  ∀ (y x : ℝ) (hxy : y < x),
  SourceSubdifferential (loss y) x = {(1 : ℝ)}

def S03 : Prop :=
  ∀ (y : ℝ),
  SourceSubdifferential (loss y) y = Icc (-1 : ℝ) 1

def S04 : Prop :=
  ∀ (y x : ℝ) (hxy : x < y),
  SourceSubdifferential (loss y) x = {(-1 : ℝ)}

def S05 : Prop :=
  ∀ (y x : ℝ),
  SourceSubdifferential (loss y) x =
      if y < x then {(1 : ℝ)} else if x = y then Icc (-1 : ℝ) 1 else {(-1 : ℝ)}

def S06 : Prop :=
  ∀ (y : ℝ),
  SubdifferentiableOn BanditRL.OnlineGradientDescent.unitInterval (loss y)

def S07 : Prop :=
  ∀ (y x g : ℝ)
    (hg : g ∈ SourceSubdifferential (loss y) x),
  ‖g‖ ≤ 1

def S08 : Prop :=
  ∀ (y x : ℝ)
    (hx : x ∈ Icc (0 : ℝ) 1),
  ‖currentSubgradient (loss y) x‖ ≤ 1

def S09 : Prop :=
  ∀ (η y x : ℝ),
  step BanditRL.OnlineGradientDescent.unitInterval η (loss y) x =
      min (max (x - η * currentSubgradient (loss y) x) 0) 1

def S10 : Prop :=
  ∀ (η η' : ℕ → ℝ) (y y' : ℕ → ℝ) (x₁ : ℝ) (t : ℕ)
    (hη : ∀ s < t, η s = η' s) (hy : ∀ s < t, y s = y' s),
  iterate BanditRL.OnlineGradientDescent.unitInterval η (fun s => loss (y s)) x₁ t =
      iterate BanditRL.OnlineGradientDescent.unitInterval η' (fun s => loss (y' s)) x₁ t

def S11 : Prop :=
  ∀ (y : ℕ → ℝ) (x₁ : ℝ) (hx₁ : x₁ ∈ Icc (0 : ℝ) 1)
    (T : ℕ) (hT : 0 < T) (hy : ∀ t < T, y t ∈ Icc (0 : ℝ) 1),
  ∀ u ∈ Icc (0 : ℝ) 1,
      (∑ t ∈ range T,
        (|iterate BanditRL.OnlineGradientDescent.unitInterval (fun _ => 1 / Real.sqrt T)
          (fun s => loss (y s)) x₁ t - y t| - |u - y t|)) ≤ Real.sqrt T

def S12 : Prop :=
  ∀ (y : ℕ → ℝ) (x₁ : ℝ)
    (hx₁ : x₁ ∈ Icc (0 : ℝ) 1) (hy : ∀ t, y t ∈ Icc (0 : ℝ) 1)
    (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) (ε : ℝ) (hε : 0 < ε),
  ∀ᶠ T : ℕ in atTop,
      (∑ t ∈ range T,
        (|iterate BanditRL.OnlineGradientDescent.unitInterval (fun _ => 1 / Real.sqrt T)
          (fun s => loss (y s)) x₁ t - y t| - |u - y t|)) / T < ε
end CurrentClosedTypes
example : NeutralRealLoss.Q01 = CurrentClosedTypes.S01 := rfl
example : NeutralRealLoss.Q02 = CurrentClosedTypes.S02 := rfl
example : NeutralRealLoss.Q03 = CurrentClosedTypes.S03 := rfl
example : NeutralRealLoss.Q04 = CurrentClosedTypes.S04 := rfl
example : NeutralRealLoss.Q05 = CurrentClosedTypes.S05 := rfl
example : NeutralRealLoss.Q06 = CurrentClosedTypes.S06 := rfl
example : NeutralRealLoss.Q07 = CurrentClosedTypes.S07 := rfl
example : NeutralRealLoss.Q08 = CurrentClosedTypes.S08 := rfl
example : NeutralRealLoss.Q09 = CurrentClosedTypes.S09 := rfl
example : NeutralRealLoss.Q10 = CurrentClosedTypes.S10 := rfl
example : NeutralRealLoss.Q11 = CurrentClosedTypes.S11 := rfl
example : NeutralRealLoss.Q12 = CurrentClosedTypes.S12 := rfl
