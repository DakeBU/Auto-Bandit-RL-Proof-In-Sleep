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
end BanditRL.OnlinePrescientBregman

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let n := `BanditRL.OnlinePrescientBregman.iterate_divergence_sum
  let some (.thmInfo info) := env.find? n | throwError "Missing actual theorem value"
  let deps := info.value.getUsedConstantsAsSet.toArray.qsort (fun a b => a.toString < b.toString)
  unless deps.contains `BanditRL.OnlinePrescientBregman.iterate_one_step do
    throwError "Missing actual parent theorem in proof VALUE"
  let j := Json.mkObj [("name",toJson n.toString),("actual_theorem_value",toJson true),
    ("value_dependencies",toJson (deps.map Name.toString)),
    ("type_dependencies",toJson (info.type.getUsedConstantsAsSet.toArray.map Name.toString))]
  liftIO <| IO.FS.writeFile "runs/online-ch2-prescient-cumulative-20261009/first-leaf-value-graph-v2.json" j.pretty
  logInfo "ACTUAL-FIRST-LEAF-VALUE-PARENT-CHECKED"
