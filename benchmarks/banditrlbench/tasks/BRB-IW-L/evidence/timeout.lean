import BanditRLProof.Exp3ImportanceWeighted
import Lean.Util.FoldConsts
theorem BenchExpansion.BRB_IW_L {Action : Type} [DecidableEq Action]
    (arms : Finset Action) (prob loss : Action → ℝ)
    (action : Action) (haction : action ∈ arms)
    (hnorm : arms.sum prob = 1) (hprob : prob action ≠ 0) :
    arms.sum (fun chosen => prob chosen *
      (BanditRLProof.Exp3.importanceWeightedLoss prob loss chosen action - loss action)^2)
      = (loss action)^2 * (1 / prob action - 1) := (
by
  classical
  have hm := BanditRLProof.Exp3.sum_prob_mul_importanceWeightedLoss_eq_loss
    arms prob loss action haction hprob
  have hs : arms.sum (fun chosen => prob chosen *
      (BanditRLProof.Exp3.importanceWeightedLoss prob loss chosen action)^2) =
      (loss action)^2 / prob action := by
    rw [Finset.sum_eq_single action]
    · simp [BanditRLProof.Exp3.importanceWeightedLoss]
      field_simp
    · intro chosen _ hne
      simp [BanditRLProof.Exp3.importanceWeightedLoss, hne]
    · exact fun hn => (hn haction).elim
  calc
    _ = arms.sum (fun chosen => prob chosen *
        (BanditRLProof.Exp3.importanceWeightedLoss prob loss chosen action)^2 -
        2 * loss action * (prob chosen *
          BanditRLProof.Exp3.importanceWeightedLoss prob loss chosen action) +
        (loss action)^2 * prob chosen) := by
      apply Finset.sum_congr rfl
      intro chosen _
      ring
    _ = (loss action)^2 / prob action - 2 * loss action * loss action +
        (loss action)^2 * 1 := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, hs, hm, hnorm]
    _ = _ := by ring

)
#print axioms BenchExpansion.BRB_IW_L
run_cmd do
  let info ← Lean.getConstInfo `BenchExpansion.BRB_IW_L
  let ty := info.type.getUsedConstantsAsSet.toList.map (·.toString)
  let vl := info.value?.map (fun v => v.getUsedConstantsAsSet.toList.map (·.toString)) |>.getD []
  let j := Lean.Json.mkObj [("type_constants", Lean.toJson ty), ("value_constants", Lean.toJson vl)]
  Lean.logInfo m!"BRB_DEPENDENCIES {j.compress}"
