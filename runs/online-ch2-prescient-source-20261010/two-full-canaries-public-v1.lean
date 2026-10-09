import Tests.OnlinePrescientBregmanSourceCanary
noncomputable section
open Set Finset BanditRL.OnlineConvex BanditRL.OnlineBregman BanditRL.OnlinePrescientBregman
namespace BanditRL.OnlinePrescientBregmanSourceCanary
example :
    let V : Set ℝ := Icc (-1) 1
    let ψ : ℝ → ℝ := fun z => z ^ 4 / 4 + z ^ 2 / 2
    let f0 : ℝ → EReal := fun z => if z ∈ V then ((|z| : ℝ) : EReal) else ⊤
    let f1 : ℝ → EReal := fun z => if z ∈ V then ((-5 * z / 8 : ℝ) : EReal) else ⊤
    let loss : ℕ → ℝ → EReal := fun t => if t = 0 then f0 else f1
    let x : ℕ → ℝ := fun t => if t = 1 then 0 else 1 / 2
    SourceProper f0 ∧
      StrictConvexOn ℝ V (fun z => (f0 z).toReal + divergence ψ z (1 / 2)) ∧
      advance V ψ 1 f0 (1 / 2) = some 0 ∧
      (∀ t ≤ 2, iterate V ψ (fun _ => 1) loss (1 / 2) t = some (x t)) ∧
      divergence ψ (x 1) (x 0) = 11 / 64 ∧
      divergence ψ (x 2) (x 1) = 9 / 64 ∧
      (∀ u ∈ V, (∑ t ∈ range 2, ((loss t (x (t + 1))).toReal - (loss t u).toReal)) ≤
        divergence ψ u (1 / 2) / 1 -
        (∑ t ∈ range 2, divergence ψ (x (t + 1)) (x t)) / 1) ∧
      (-9 / 8 : ℝ) ≤ 5 / 16 := by
  exact BanditRL.OnlinePrescientBregmanSourceCanary.fixed_source_run

#check @BanditRL.OnlinePrescientBregmanSourceCanary.fixed_source_run
#print axioms BanditRL.OnlinePrescientBregmanSourceCanary.fixed_source_run
example :
    let V : Set ℝ := Icc (-1) 1
    let ψ : ℝ → ℝ := fun z => z ^ 4 / 4 + z ^ 2 / 2
    let f0 : ℝ → EReal := fun z => if z ∈ V then ((|z| : ℝ) : EReal) else ⊤
    let f1 : ℝ → EReal := fun z => if z ∈ V then ((-5 * z / 4 : ℝ) : EReal) else ⊤
    let loss : ℕ → ℝ → EReal := fun t => if t = 0 then f0 else f1
    let η : ℕ → ℝ := fun t => if t = 0 then 1 else 1 / 2
    let x : ℕ → ℝ := fun t => if t = 1 then 0 else 1 / 2
    (∀ t ≤ 2, iterate V ψ η loss (1 / 2) t = some (x t)) ∧
      (∑ t ∈ range 2, divergence ψ (x (t + 1)) (x t) / η t) = 29 / 64 ∧
      ((range 2).sup' (by decide) (fun t => divergence ψ (-1 / 2) (x t))) = 5 / 8 ∧
      ((range 2).sup' (by decide) (fun t => divergence ψ (1 / 2) (x t))) = 9 / 64 ∧
      (∀ u ∈ V, (∑ t ∈ range 2, ((loss t (x (t + 1))).toReal - (loss t u).toReal)) ≤
        ((range 2).sup' (by decide) (fun t => divergence ψ u (x t))) / η 1 -
        ∑ t ∈ range 2, divergence ψ (x (t + 1)) (x t) / η t) ∧
      (-1 / 2 : ℝ) ≤ -11 / 64 := by
  exact BanditRL.OnlinePrescientBregmanSourceCanary.decreasing_source_run

#check @BanditRL.OnlinePrescientBregmanSourceCanary.decreasing_source_run
#print axioms BanditRL.OnlinePrescientBregmanSourceCanary.decreasing_source_run
end BanditRL.OnlinePrescientBregmanSourceCanary
