import QuantumBanditAdapter
import ABEISTests.PrimitiveCircuitPerturbation

namespace QuantumBanditCanary
open QuantumBlockEncoding
open PrimitiveCircuitPerturbationTests
open scoped MatrixOrder Matrix.Norms.L2Operator

example (a b e s estimate : ℝ)
    (P : _root_.Matrix (PrimitiveBasis 2) (PrimitiveBasis 2) ℂ)
    (ψ : EuclideanSpace ℂ (PrimitiveBasis 2)) (hψ : ‖ψ‖ = 1)
    (hP : 0 ≤ P) (hPI : P ≤ 1)
    (hs : |estimate - BornStability.probability
      (evalPrimitiveCircuit [.ry 0 (.real (a + e)), cx01, .ry 1 (.real (b + e))]) P ψ| ≤ s) :
    |estimate - BornStability.probability
      (evalPrimitiveCircuit [.ry 0 (.real a), cx01, .ry 1 (.real b)]) P ψ| ≤ 3 * |e| + s := by
  simpa using BanditRLProof.QuantumBanditAdapter.aligned_circuit_confidence_transport
    (abs_nonneg e) _ _ (noncommuting_sequence a b e) P ψ hψ hP hPI hs

def oracle : PrimitiveCircuit 1 := [.ry 0 (.rational (1/3)), .x 0]
def word : QueryCircuitCost.Word 1 := [.forward, .known [.x 0], .inverse]

example : (QueryCircuitCost.expand word oracle).length = 5 := by decide
example : QuantumQueryWord.queryCount (QueryCircuitCost.erase word) = 2 := by
  simp [word, QueryCircuitCost.erase, QueryCircuitCost.Instruction.erase,
    QuantumQueryWord.queryCount, QuantumQueryWord.Instruction.queryCost]
example : evalPrimitiveCircuit (QueryCircuitCost.expand word oracle) =
    QuantumQueryWord.eval (QueryCircuitCost.erase word) (evalPrimitiveCircuit oracle) :=
  QueryCircuitCost.expanded_semantics _ _
example : (BanditRLProof.QuantumBanditAdapter.chargedBlock (K := 2) (D := 2) 1 word
    (by simp [word, QueryCircuitCost.erase, QueryCircuitCost.Instruction.erase,
      QuantumQueryWord.queryCount, QuantumQueryWord.Instruction.queryCost])).queries = 2 := by
  rw [BanditRLProof.QuantumBanditAdapter.chargedBlock_queries]
  simp [word, QueryCircuitCost.erase, QueryCircuitCost.Instruction.erase,
    QuantumQueryWord.queryCount, QuantumQueryWord.Instruction.queryCost]

#eval (QueryCircuitCost.expand word oracle).length
#print axioms BanditRLProof.QuantumBanditAdapter.aligned_circuit_confidence_transport
#print axioms BanditRLProof.QuantumBanditAdapter.circuit_certified_recommendation_failure_bound
#print axioms QueryCircuitCost.expanded_length
#print axioms QueryCircuitCost.expanded_semantics

end QuantumBanditCanary
#print axioms QuantumBlockEncoding.BornStability.probability_mem_Icc
#print axioms BanditRLProof.QuantumBanditAdapter.chargedBlock_queries
