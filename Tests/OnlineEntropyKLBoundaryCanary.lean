import BanditRLProof.OnlineEntropyKLBoundary

noncomputable section
open Finset
namespace BanditRL.OnlineEntropy.KLBoundary.Canary

theorem unequal_mass_zero_played :
    divergence (fun _ : Fin 1 => 0) (fun _ => 2) = 2 ∧
    finiteKL (fun _ : Fin 1 => 0) (fun _ => 2) = 0 := by
  have hh := (generalized_identity (fun _ : Fin 1 => 0) (fun _ => 2)
    (fun _ => le_rfl) (fun _ => by norm_num)).2
  constructor
  · simpa using hh
  · simp [finiteKL]

theorem quarter_interior :
    (1:ℝ)/8 ≤ finiteKL (binaryVector (1/4)) (binaryVector (1/2)) ∧
    divergence (binaryVector (1/4)) (binaryVector (1/2)) =
      finiteKL (binaryVector (1/4)) (binaryVector (1/2)) := by
  let x := binaryVector (1/4)
  let y := binaryVector (1/2)
  have hx (i : Fin 2) : 0 < x i := by fin_cases i <;> norm_num [x,binaryVector]
  have hy (i : Fin 2) : 0 < y i := by fin_cases i <;> norm_num [y,binaryVector]
  have sx : ∑ i, x i = 1 := by norm_num [x,Fin.sum_univ_two,binaryVector]
  have sy : ∑ i, y i = 1 := by norm_num [y,Fin.sum_univ_two,binaryVector]
  have bound := interior_lower_bound x y hx hy sx sy
  refine ⟨?_,simplex_identity x y (fun i => (hx i).le) hy sx sy⟩
  norm_num [x,y,Fin.sum_univ_two,binaryVector] at bound ⊢
  exact bound

theorem two_endpoints_and_scaled :
    finiteKL (binaryVector 0) (binaryVector (1/2)) = Real.log 2 ∧
    finiteKL (binaryVector 1) (binaryVector (1/2)) = Real.log 2 ∧
    (3:ℝ)/2 ≤ 3 * Real.log 2 := by
  have b0 := binary_boundary.2.2.2 0 (by constructor <;> norm_num)
  have b1 := binary_boundary.2.2.2 1 (by constructor <;> norm_num)
  have hs := scaled_binary_use 3 (-3) (by norm_num) (by norm_num)
  have at0 : BanditRLProof.KLUCB.bernoulliKLCore 0 (1/2) = Real.log 2 := binary_boundary.2.1
  rw [show (1/2:ℝ)+(-3)/(2*3)=0 by norm_num,at0] at hs
  exact ⟨b0.1.trans binary_boundary.2.1,b1.1.trans binary_boundary.2.2.1,by linarith only [hs]⟩

end BanditRL.OnlineEntropy.KLBoundary.Canary
