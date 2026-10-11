import CumulativeOptimisticStabilityCandidate

noncomputable section
open Set Finset
namespace BanditRL.OnlineConvex

#check ∀ {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : Set E) (hV : Convex ℝ V)
    (psi hint : E → ℝ) (loss : ℕ → E → EReal) (n : ℕ) (lam : ℝ)
    (hbot : ∀ i < n + 1, ∀ x, loss i x ≠ ⊥)
    (hdom : ∀ i < n + 1, V ⊆ effectiveDomain (loss i))
    (hlam : 0 < lam)
    (hstrong : let G : E → EReal := fun x =>
        (psi x : EReal) + ∑ i ∈ range (n + 1), loss i x + extendedIndicator V x
      ∀ x ∈ V, ∀ y ∈ V, ∀ a : ℝ, 0 < a → a < 1 →
        G (a • x + (1 - a) • y) ≤
          (a : EReal) * G x + ((1 - a : ℝ) : EReal) * G y -
            (((lam / 2) * a * (1 - a) * ‖x - y‖ ^ 2 : ℝ) : EReal))
    (p : E) (hp : p ∈ V)
    (hprediction : IsMinOn (fun x =>
      (psi x : EReal) + ∑ i ∈ range n, loss i x + (hint x : EReal)) V p)
    (g : E →L[ℝ] ℝ)
    (hdifference : ∀ z ∈ V,
      (loss n p).toReal - hint p + g (z - p) ≤ (loss n z).toReal - hint z)
    (q : E) (hq : q ∈ V),
    let G : E → EReal := fun x =>
      (psi x : EReal) + ∑ i ∈ range (n + 1), loss i x + extendedIndicator V x
    (G p).toReal - (G q).toReal ≤
      ‖g‖ ^ 2 / (2 * lam)

end BanditRL.OnlineConvex

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut rows : Array Json := #[]
  for n in env.header.moduleNames do
    let p ← liftIO <| findOLean n
    rows := rows.push <| Json.mkObj [("module",toJson n.toString),("olean",toJson p.toString)]
  liftIO do
    let f ← IO.FS.Handle.mk "tmp/online-b4-next-dual-stability-body-20261012/header-origins-v1.json" .writeNew
    f.putStr ((toJson rows).pretty ++ "\n")
