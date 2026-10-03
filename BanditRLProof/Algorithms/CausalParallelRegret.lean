import BanditRLProof.Algorithms.CausalParallelLaw
import BanditRLProof.Algorithms.CausalImportanceTransport
import BanditRLProof.Algorithms.CausalAllocationRegret

/-! Parallel DAG adapter and actual allocation-dependent expected simple regret. -/
namespace BanditRLProof.Causal.ParallelParameters
open scoped Classical
open MeasureTheory
set_option autoImplicit false
set_option maxHeartbeats 800000

variable {N : ℕ} (p : ParallelParameters N) (reward : (Fin N → Bool) → PMF Bool)

noncomputable def graph : GraphModel Bool (N+1) where
  parents := Fin.lastCases Finset.univ (fun _ => ∅)
  table := Fin.lastCases reward (fun i _ => p.rootTable i)
  local_table := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · intro h h' heq
      simp only [Fin.lastCases_last] at heq ⊢
      have hh : h = h' := funext fun j => heq j (Finset.mem_univ _)
      rw [hh]
    · intro h h' _
      simp only [Fin.lastCases_castSucc]

def graphAction (a : Option (Fin N × Bool)) : Fin (N+1) → Option Bool :=
  Fin.lastCases none (rootAction a)

theorem graphAction_reward (a : Option (Fin N × Bool)) : graphAction a (Fin.last N) = none := by
  simp [graphAction]

theorem graph_parentLaw (a : Option (Fin N × Bool)) :
    (p.graph reward).parentLaw (graphAction a) (Fin.last N) =
      (p.rootLaw a).map ((p.graph reward).parentConfig (Fin.last N)) := by
  rw [GraphModel.parentLaw_prefix]
  congr 2
  funext i h
  change intervene (p.graph reward).table (graphAction a) i.castSucc h =
    intervene (fun j _ => p.rootTable j) (rootAction a) i h
  simp [intervene,graph,graphAction]

theorem graph_parentConfig_injective :
    Function.Injective ((p.graph reward).parentConfig (Fin.last N)) := by
  intro x y h
  funext i
  exact congrFun h ⟨i,by simp only [graph,Fin.lastCases_last]; exact Finset.mem_univ _⟩

theorem graph_allocation_covers :
    Covers (fun a => (p.graph reward).parentLaw (graphAction a) (Fin.last N))
      (mixture p.allocation (fun a => (p.graph reward).parentLaw (graphAction a) (Fin.last N))) := by
  simp only [p.graph_parentLaw,mixture_map]
  exact covers_map_injective p.rootLaw _ p.allocation_covers _ (p.graph_parentConfig_injective reward)

theorem graph_designCost (eta : PMF (Option (Fin N × Bool))) :
    designCost (fun a => (p.graph reward).parentLaw (graphAction a) (Fin.last N)) eta =
      designCost p.rootLaw eta := by
  simp only [p.graph_parentLaw]
  exact designCost_map_injective p.rootLaw eta _ (p.graph_parentConfig_injective reward)

theorem graph_allocation_cost_le :
    designCost (fun a => (p.graph reward).parentLaw (graphAction a) (Fin.last N)) p.allocation ≤
      2*p.rarity := by
  rw [p.graph_designCost]
  exact p.allocation_cost_le

theorem graph_optimal_cost_le :
    let laws := fun a => (p.graph reward).parentLaw (graphAction a) (Fin.last N)
    designCost laws (optimalAllocation laws) ≤ 2*p.rarity := by
  exact (optimalAllocation_minimizes _ p.allocation (p.graph_allocation_covers reward)).trans
    (p.graph_allocation_cost_le reward)

variable [LinearOrder (Option (Fin N × Bool))]
variable [MeasurableSpace (Option (Fin N × Bool))]
variable [MeasurableSingletonClass (Option (Fin N × Bool))]

theorem expected_simpleRegret_parallel (T : ℕ) (hT : 0 < T) :
    let m := designCost p.rootLaw p.allocation
    let L := sourceLog T (Fintype.card (Option (Fin N × Bool)))
    let B := sourceThreshold m T L
    (∫ w, (p.graph reward).simpleRegret id graphAction p.allocation (Fin.last N) B w
      ∂(p.graph reward).sampleLaw graphAction p.allocation T) ≤
      (2*Real.sqrt 2+7)*Real.sqrt ((2*p.rarity)*L/T)+1/(T:ℝ) := by
  have h := (p.graph reward).expected_simpleRegret_source_bound id graphAction p.allocation
    (Fin.last N) graphAction_reward (p.graph_allocation_covers reward) T hT
  dsimp only at h ⊢
  rw [p.graph_designCost] at h
  refine h.trans (add_le_add ?_ le_rfl)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.sqrt_le_sqrt
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_right p.allocation_cost_le
    (sourceLog_pos T _ hT Fintype.card_pos).le

theorem expected_simpleRegret_parallel_optimal (T : ℕ) (hT : 0 < T) :
    let laws := fun a => (p.graph reward).parentLaw (graphAction a) (Fin.last N)
    let eta := optimalAllocation laws
    let m := designCost laws eta
    let L := sourceLog T (Fintype.card (Option (Fin N × Bool)))
    let B := sourceThreshold m T L
    (∫ w, (p.graph reward).simpleRegret id graphAction eta (Fin.last N) B w
      ∂(p.graph reward).sampleLaw graphAction eta T) ≤
      (2*Real.sqrt 2+7)*Real.sqrt ((2*p.rarity)*L/T)+1/(T:ℝ) := by
  have h := (p.graph reward).expected_simpleRegret_optimal id graphAction
    (Fin.last N) graphAction_reward T hT
  dsimp only at h ⊢
  refine h.trans (add_le_add ?_ le_rfl)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.sqrt_le_sqrt
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_right (p.graph_optimal_cost_le reward)
    (sourceLog_pos T _ hT Fintype.card_pos).le

end BanditRLProof.Causal.ParallelParameters
