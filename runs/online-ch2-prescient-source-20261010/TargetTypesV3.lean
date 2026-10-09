import BanditRLProof.OnlinePrescientBregmanRegret
noncomputable section
open Set Finset
open BanditRL.OnlineBregman
set_option autoImplicit false
set_option linter.unusedVariables false
namespace BanditRL.OnlineConvex
variable {E : Type*}
#check fun (f : E → EReal) (V : Set E)
    (hV : V.Nonempty) (hbot : ∀ z, f z ≠ ⊥)
    (hdom : V ⊆ effectiveDomain f) =>
  (SourceProper f : Prop)
end BanditRL.OnlineConvex
namespace BanditRL.OnlinePrescientBregman
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
#check fun (V X : Set E) (hV : Convex ℝ V) (hVX : V ⊆ X)
    (ψ : E → ℝ) (hψ : StrictConvexOn ℝ X ψ)
    (f : E → EReal) (hf : BanditRL.OnlineConvex.SourceProper f)
    (hs : ∀ z ∈ V, (BanditRL.OnlineConvex.SourceSubdifferential f z).Nonempty)
    (η : ℝ) (hη : 0 < η) (x : E) =>
  (StrictConvexOn ℝ V (fun z => (f z).toReal + η⁻¹ * divergence ψ z x) : Prop)
end BanditRL.OnlinePrescientBregman
namespace BanditRL.OnlinePrescientBregman
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
#check fun (V X : Set E) (hV : Convex ℝ V)
    (hVX : V ⊆ X) (ψ : E → ℝ) (hψ : StrictConvexOn ℝ X ψ)
    (f : E → EReal) (hf : BanditRL.OnlineConvex.SourceProper f)
    (hs : ∀ z ∈ V, (BanditRL.OnlineConvex.SourceSubdifferential f z).Nonempty)
    (η : ℝ) (hη : 0 < η) (x p : E) (hp : p ∈ V)
    (hmin : IsMinOn (fun z => f z + ((η⁻¹ * divergence ψ z x : ℝ) : EReal)) V p) =>
  (advance V ψ η f x = some p : Prop)
end BanditRL.OnlinePrescientBregman
namespace BanditRL.OnlinePrescientBregman
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
#check fun (V X : Set E) (hV : Convex ℝ V)
    (hVX : V ⊆ X) (ψ : E → ℝ) (hψ : StrictConvexOn ℝ X ψ)
    (η : ℕ → ℝ) (loss : ℕ → E → EReal) (x0 : E) (x : ℕ → E) (T : ℕ)
    (hinit : x 0 = x0) (hη : ∀ t < T, 0 < η t)
    (hf : ∀ t < T, BanditRL.OnlineConvex.SourceProper (loss t))
    (hs : ∀ t < T, ∀ z ∈ V,
      (BanditRL.OnlineConvex.SourceSubdifferential (loss t) z).Nonempty)
    (hmin : ∀ t < T, x (t + 1) ∈ V ∧
      IsMinOn (fun z => loss t z + (((η t)⁻¹ * divergence ψ z (x t) : ℝ) : EReal))
        V (x (t + 1))) =>
  (∀ t ≤ T, iterate V ψ η loss x0 t = some (x t) : Prop)
end BanditRL.OnlinePrescientBregman
namespace BanditRL.OnlinePrescientBregman
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
#check fun (V X : Set E) (hV : Convex ℝ V)
    (hVn : V.Nonempty) (_hVc : IsClosed V) (hVX : V ⊆ X)
    (ψ : E → ℝ) (hψ : StrictConvexOn ℝ X ψ)
    (_hψc : BanditRL.OnlineConvex.SourceClosed (fun z =>
      (ψ z : EReal) + BanditRL.OnlineConvex.extendedIndicator X z))
    (hd : DifferentiableOn ℝ ψ (interior X))
    (η : ℝ) (hη : 0 < η) (loss : ℕ → E → EReal)
    (x0 : E) (x : ℕ → E) (T : ℕ) (hinit : x 0 = x0)
    (hinterior : ∀ t ≤ T, x t ∈ interior X)
    (hbot : ∀ t < T, ∀ z, loss t z ≠ ⊥)
    (hdom : ∀ t < T, V ⊆ BanditRL.OnlineConvex.effectiveDomain (loss t))
    (hs : ∀ t < T, ∀ z ∈ V,
      (BanditRL.OnlineConvex.SourceSubdifferential (loss t) z).Nonempty)
    (hmin : ∀ t < T, x (t + 1) ∈ V ∧
      IsMinOn (fun z => loss t z + ((η⁻¹ * divergence ψ z (x t) : ℝ) : EReal))
        V (x (t + 1))) (u : E) (hu : u ∈ V) =>
  ((∑ t ∈ range T, ((loss t (x (t + 1))).toReal - (loss t u).toReal)) ≤
      divergence ψ u x0 / η - (∑ t ∈ range T, divergence ψ (x (t + 1)) (x t)) / η : Prop)
end BanditRL.OnlinePrescientBregman
namespace BanditRL.OnlinePrescientBregman
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
#check fun (V X : Set E) (hV : Convex ℝ V)
    (hVn : V.Nonempty) (_hVc : IsClosed V) (hVX : V ⊆ X)
    (ψ : E → ℝ) (hψ : StrictConvexOn ℝ X ψ)
    (_hψc : BanditRL.OnlineConvex.SourceClosed (fun z =>
      (ψ z : EReal) + BanditRL.OnlineConvex.extendedIndicator X z))
    (hd : DifferentiableOn ℝ ψ (interior X))
    (η : ℕ → ℝ)
    (loss : ℕ → E → EReal) (x0 : E) (x : ℕ → E) (T : ℕ) (hT : 0 < T)
    (hη : ∀ t < T, 0 < η t)
    (hinit : x 0 = x0) (hinterior : ∀ t ≤ T, x t ∈ interior X)
    (hmono : ∀ t, t + 1 < T → η (t + 1) ≤ η t)
    (hbot : ∀ t < T, ∀ z, loss t z ≠ ⊥)
    (hdom : ∀ t < T, V ⊆ BanditRL.OnlineConvex.effectiveDomain (loss t))
    (hs : ∀ t < T, ∀ z ∈ V,
      (BanditRL.OnlineConvex.SourceSubdifferential (loss t) z).Nonempty)
    (hmin : ∀ t < T, x (t + 1) ∈ V ∧
      IsMinOn (fun z => loss t z + (((η t)⁻¹ * divergence ψ z (x t) : ℝ) : EReal))
        V (x (t + 1))) (u : E) (hu : u ∈ V) =>
  ((∑ t ∈ range T, ((loss t (x (t + 1))).toReal - (loss t u).toReal)) ≤
      ((range T).sup' (nonempty_range_iff.mpr (Nat.ne_of_gt hT))
        (fun t => divergence ψ u (x t))) / η (T - 1) -
      ∑ t ∈ range T, divergence ψ (x (t + 1)) (x t) / η t : Prop)
end BanditRL.OnlinePrescientBregman
