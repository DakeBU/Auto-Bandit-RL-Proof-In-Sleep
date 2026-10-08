import QuantumBlockEncoding.CircuitRewardBias
import QuantumBlockEncoding.QueryCircuitCost
import BanditRLProof.QuantumConfidence
import BanditRLProof.QuantumQueryAccounting

/-! A narrow actual cross-library transport. Statistical tails are an open
producer dependency; no quantum estimator or advantage is asserted by this file. -/
namespace BanditRLProof.QuantumBanditAdapter
open QuantumBlockEncoding
open scoped MatrixOrder Matrix.Norms.L2Operator

/-- Consumes an actual circuit alignment, deriving rather than assuming reward bias. -/
theorem aligned_circuit_confidence_transport {n : ℕ} {δ s estimate : ℝ}
    (hδ : 0 ≤ δ) (exact approximate : PrimitiveCircuit n)
    (ha : PrimitiveCircuitPerturbation.Aligned δ exact approximate)
    (P : _root_.Matrix (PrimitiveBasis n) (PrimitiveBasis n) ℂ)
    (ψ : EuclideanSpace ℂ (PrimitiveBasis n)) (hψ : ‖ψ‖ = 1)
    (hP : 0 ≤ P) (hPI : P ≤ 1)
    (hs : |estimate - BornStability.probability (evalPrimitiveCircuit approximate) P ψ| ≤ s) :
    |estimate - BornStability.probability (evalPrimitiveCircuit exact) P ψ| ≤
      (exact.length : ℝ) * δ + s :=
  QuantumConfidence.bias_statistical_composition
    (CircuitRewardBias.aligned_reward_bias_le hδ exact approximate ha P ψ hψ hP hPI) hs

/-- A concrete recommendation rule with circuit-derived biases. The marginal
statistical tails are explicit conditional leaves, not unproved noise hypotheses. -/
theorem circuit_certified_recommendation_failure_bound
    {Ω : Type*} [MeasurableSpace Ω] {K n : ℕ} [Nonempty (Fin K)]
    (law : MeasureTheory.Measure Ω) (exact approximate : Fin K → PrimitiveCircuit n)
    (δ : Fin K → ℝ) (hδ : ∀ i, 0 ≤ δ i)
    (ha : ∀ i, PrimitiveCircuitPerturbation.Aligned (δ i) (exact i) (approximate i))
    (P : _root_.Matrix (PrimitiveBasis n) (PrimitiveBasis n) ℂ)
    (ψ : EuclideanSpace ℂ (PrimitiveBasis n)) (hψ : ‖ψ‖ = 1)
    (hP : 0 ≤ P) (hPI : P ≤ 1)
    (estimate : Fin K → Ω → ℝ) (statistical share : Fin K → ℝ) {ε : ℝ}
    (hbudget : ∀ i, (exact i).length * δ i + statistical i ≤ ε / 2)
    (htail : ∀ i, law {ω | statistical i <
      |estimate i ω - BornStability.probability (evalPrimitiveCircuit (approximate i)) P ψ|} ≤
        ENNReal.ofReal (share i)) :
    law {ω | ∃ i,
      BornStability.probability (evalPrimitiveCircuit
        (exact (QuantumConfidence.recommend (fun j => estimate j ω)))) P ψ + ε <
      BornStability.probability (evalPrimitiveCircuit (exact i)) P ψ} ≤
        ∑ i, ENNReal.ofReal (share i) := by
  exact QuantumConfidence.recommend_fixed_fidelity_failure_bound law
    (fun i => BornStability.probability (evalPrimitiveCircuit (exact i)) P ψ)
    (fun i => BornStability.probability (evalPrimitiveCircuit (approximate i)) P ψ)
    (fun i => (exact i).length * δ i) statistical estimate
    (fun i => CircuitRewardBias.aligned_reward_bias_le (hδ i) _ _ (ha i) P ψ hψ hP hPI)
    hbudget share htail

/-- The same executed word provides the charged arm block. Reset is not
implemented by this accounting map. -/
noncomputable def chargedBlock {K D n : ℕ} (i : Fin K)
    (w : QueryCircuitCost.Word n)
    (hD : QuantumQueryWord.queryCount (QueryCircuitCost.erase w) ≤ D) :
    QuantumQueryAccounting.Block K D :=
  ⟨i, QuantumQueryWord.forwardCount (QueryCircuitCost.erase w),
    QuantumQueryWord.inverseCount (QueryCircuitCost.erase w),
    by rw [← QuantumQueryWord.queryCount_eq]; exact hD⟩

theorem chargedBlock_queries {K D n : ℕ} (i : Fin K)
    (w : QueryCircuitCost.Word n)
    (hD : QuantumQueryWord.queryCount (QueryCircuitCost.erase w) ≤ D) :
    (chargedBlock i w hD).queries = QuantumQueryWord.queryCount (QueryCircuitCost.erase w) :=
  (QuantumQueryWord.queryCount_eq _).symm

end BanditRLProof.QuantumBanditAdapter
