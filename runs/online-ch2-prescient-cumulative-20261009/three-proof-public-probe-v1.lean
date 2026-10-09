import BanditRLProof.OnlinePrescientBregmanRegret
import Lean
noncomputable section

open Set Finset
namespace BanditRL.OnlinePrescientBregman
open BanditRL.OnlineBregman
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

example (V X : Set E) (hV : Convex ℝ V) (ψ : E → ℝ)
    (hd : DifferentiableOn ℝ ψ (interior X)) (η : ℕ → ℝ)
    (loss : ℕ → E → EReal) (x0 : E) (x : ℕ → E) (T : ℕ)
    (hseq : ∀ t ≤ T, iterate V ψ η loss x0 t = some (x t))
    (hinterior : ∀ t ≤ T, x t ∈ interior X)
    (hη : ∀ t < T, 0 < η t)
    (hf : ∀ t < T, BanditRL.OnlineConvex.SourceProper (loss t))
    (hs : ∀ t < T, ∀ z ∈ V,
      (BanditRL.OnlineConvex.SourceSubdifferential (loss t) z).Nonempty)
    (u : E) (hu : u ∈ V) :
    (∑ t ∈ range T, ((loss t (x (t + 1))).toReal - (loss t u).toReal)) ≤
      (∑ t ∈ range T, (divergence ψ u (x t) - divergence ψ u (x (t + 1))) / η t) -
      ∑ t ∈ range T, divergence ψ (x (t + 1)) (x t) / η t := by
  exact iterate_divergence_sum V X hV ψ hd η loss x0 x T hseq hinterior hη hf hs u hu

#check @BanditRL.OnlinePrescientBregman.iterate_divergence_sum
#print axioms BanditRL.OnlinePrescientBregman.iterate_divergence_sum

example (V X : Set E) (hV : Convex ℝ V) (ψ : E → ℝ)
    (hd : DifferentiableOn ℝ ψ (interior X)) (η : ℝ) (hη : 0 < η)
    (loss : ℕ → E → EReal) (x0 : E) (x : ℕ → E) (T : ℕ)
    (hseq : ∀ t ≤ T, iterate V ψ (fun _ => η) loss x0 t = some (x t))
    (hinterior : ∀ t ≤ T, x t ∈ interior X)
    (hf : ∀ t < T, BanditRL.OnlineConvex.SourceProper (loss t))
    (hs : ∀ t < T, ∀ z ∈ V,
      (BanditRL.OnlineConvex.SourceSubdifferential (loss t) z).Nonempty)
    (u : E) (hu : u ∈ V) :
    (∑ t ∈ range T, ((loss t (x (t + 1))).toReal - (loss t u).toReal)) ≤
      divergence ψ u x0 / η - divergence ψ u (x T) / η -
      (∑ t ∈ range T, divergence ψ (x (t + 1)) (x t)) / η := by
  exact iterate_fixed_sharp V X hV ψ hd η hη loss x0 x T hseq hinterior hf hs u hu

#check @BanditRL.OnlinePrescientBregman.iterate_fixed_sharp
#print axioms BanditRL.OnlinePrescientBregman.iterate_fixed_sharp

example (V X : Set E) (hV : Convex ℝ V) (ψ : E → ℝ)
    (hd : DifferentiableOn ℝ ψ (interior X)) (η : ℕ → ℝ)
    (loss : ℕ → E → EReal) (x0 : E) (x : ℕ → E) (T : ℕ) (hT : 0 < T)
    (hseq : ∀ t ≤ T, iterate V ψ η loss x0 t = some (x t))
    (hinterior : ∀ t ≤ T, x t ∈ interior X)
    (hη : ∀ t < T, 0 < η t)
    (hmono : ∀ t, t + 1 < T → η (t + 1) ≤ η t)
    (hf : ∀ t < T, BanditRL.OnlineConvex.SourceProper (loss t))
    (hs : ∀ t < T, ∀ z ∈ V,
      (BanditRL.OnlineConvex.SourceSubdifferential (loss t) z).Nonempty)
    (u : E) (hu : u ∈ V) (M : ℝ)
    (hbound : ∀ t < T, divergence ψ u (x t) ≤ M) :
    (∑ t ∈ range T, ((loss t (x (t + 1))).toReal - (loss t u).toReal)) ≤
      M / η (T - 1) - divergence ψ u (x T) / η (T - 1) -
      ∑ t ∈ range T, divergence ψ (x (t + 1)) (x t) / η t := by
  exact iterate_variable_sharp V X hV ψ hd η loss x0 x T hT hseq hinterior hη hmono hf hs u hu M hbound

#check @BanditRL.OnlinePrescientBregman.iterate_variable_sharp
#print axioms BanditRL.OnlinePrescientBregman.iterate_variable_sharp

end BanditRL.OnlinePrescientBregman
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut nodes : Array Json := #[]
  do
    let n := `BanditRL.OnlinePrescientBregman.iterate_divergence_sum
    let some (.thmInfo info) := env.find? n | throwError "Missing actual theorem value"
    let td := info.type.getUsedConstantsAsSet.toArray.qsort (fun a b => a.toString < b.toString)
    let vd := info.value.getUsedConstantsAsSet.toArray.qsort (fun a b => a.toString < b.toString)
    nodes := nodes.push <| Json.mkObj [("name",toJson n.toString),("has_value",toJson true),("type_dependencies",toJson (td.map Name.toString)),("value_dependencies",toJson (vd.map Name.toString))]
  do
    let n := `BanditRL.OnlinePrescientBregman.iterate_fixed_sharp
    let some (.thmInfo info) := env.find? n | throwError "Missing actual theorem value"
    let td := info.type.getUsedConstantsAsSet.toArray.qsort (fun a b => a.toString < b.toString)
    let vd := info.value.getUsedConstantsAsSet.toArray.qsort (fun a b => a.toString < b.toString)
    nodes := nodes.push <| Json.mkObj [("name",toJson n.toString),("has_value",toJson true),("type_dependencies",toJson (td.map Name.toString)),("value_dependencies",toJson (vd.map Name.toString))]
  do
    let n := `BanditRL.OnlinePrescientBregman.iterate_variable_sharp
    let some (.thmInfo info) := env.find? n | throwError "Missing actual theorem value"
    let td := info.type.getUsedConstantsAsSet.toArray.qsort (fun a b => a.toString < b.toString)
    let vd := info.value.getUsedConstantsAsSet.toArray.qsort (fun a b => a.toString < b.toString)
    nodes := nodes.push <| Json.mkObj [("name",toJson n.toString),("has_value",toJson true),("type_dependencies",toJson (td.map Name.toString)),("value_dependencies",toJson (vd.map Name.toString))]
  liftIO <| IO.FS.writeFile "runs/online-ch2-prescient-cumulative-20261009/three-proof-value-graph-v1.json" (toJson nodes).pretty
  logInfo "THREE-COMPLETE-PUBLIC-VALUES-EXPORTED"
