import BanditRLProof.OnlineEntropyWeightedPairing

noncomputable section
namespace BanditRL.OnlineEntropyCanary
open BanditRL.OnlineEntropy Finset

def weights (i : Fin 2) : ℝ := if i = 0 then 1 else 2
def pointX (i : Fin 2) : ℝ := if i = 0 then 1/4 else 3/2
def pointY (i : Fin 2) : ℝ := if i = 0 then 3/4 else 1/2
def vertical (i : Fin 2) : ℝ := if i = 0 then 0 else 1

abbrev squaredDistance (a b : Fin 2 → ℝ) : ℝ := (∑ i, |a i - b i|)^2
abbrev intermediate (a b : Fin 2 → ℝ) : ℝ :=
  ∑ i, 2 * weights i * (a i - b i)^2 / (a i + b i)
abbrev differentialPair (a b : Fin 2 → ℝ) : ℝ :=
  (fderiv ℝ (weightedEntropy weights) a - fderiv ℝ (weightedEntropy weights) b) (a-b)

private theorem weightsPos (i : Fin 2) : 0 < weights i := by fin_cases i <;> norm_num [weights]
private theorem pointX_mem : pointX ∈ weightedSimplex weights := by
  constructor
  · intro i;fin_cases i <;> norm_num [pointX]
  · norm_num [Fin.sum_univ_two,pointX,weights]
private theorem pointY_mem : pointY ∈ weightedSimplex weights := by
  constructor
  · intro i;fin_cases i <;> norm_num [pointY]
  · norm_num [Fin.sum_univ_two,pointY,weights]

theorem ambient_vertical_derivative :
    pointX ∈ weightedSimplex weights ∧
    (∑ i, pointX i) = 7/4 ∧
    (∑ i, vertical i / weights i) = 1/2 ∧
    DifferentiableAt ℝ (weightedEntropy weights) pointX ∧
    fderiv ℝ (weightedEntropy weights) pointX vertical = 2 * (Real.log (3/2) + 1) := by
  have hd := weightedEntropy_differential weights pointX pointX_mem.1
  refine ⟨pointX_mem,?_,?_,hd.1,?_⟩
  · norm_num [Fin.sum_univ_two,pointX]
  · norm_num [Fin.sum_univ_two,weights,vertical]
  · rw [hd.2];norm_num [Fin.sum_univ_two,pointX,weights,vertical]

theorem nonunit_weights_pairing :
    pointX ∈ weightedSimplex weights ∧ pointY ∈ weightedSimplex weights ∧
    (∑ i, pointY i) = 5/4 ∧
    squaredDistance pointX pointY ≤ intermediate pointX pointY ∧
    intermediate pointX pointY ≤ differentialPair pointX pointY ∧
    squaredDistance pointX pointY = 9/4 ∧ intermediate pointX pointY = 5/2 ∧
    differentialPair pointX pointY = (5/2) * Real.log 3 := by
  have h := weightedEntropy_pairing weights pointX pointY weightsPos pointX_mem pointY_mem
  refine ⟨pointX_mem,pointY_mem,?_,h.1,h.2,?_,?_,?_⟩
  · norm_num [Fin.sum_univ_two,pointY]
  · norm_num [squaredDistance,Fin.sum_univ_two,pointX,pointY,abs_of_neg,abs_of_pos]
  · norm_num [intermediate,Fin.sum_univ_two,weights,pointX,pointY]
  · unfold differentialPair
    rw [ContinuousLinearMap.sub_apply,(weightedEntropy_differential weights pointX pointX_mem.1).2,
      (weightedEntropy_differential weights pointY pointY_mem.1).2]
    norm_num [Fin.sum_univ_two,weights,pointX,pointY,Pi.sub_apply,
      Real.log_div (by norm_num : (1:ℝ) ≠ 0) (by norm_num : (4:ℝ) ≠ 0),
      Real.log_div (by norm_num : (3:ℝ) ≠ 0) (by norm_num : (4:ℝ) ≠ 0),
      Real.log_div (by norm_num : (1:ℝ) ≠ 0) (by norm_num : (2:ℝ) ≠ 0),
      Real.log_div (by norm_num : (3:ℝ) ≠ 0) (by norm_num : (2:ℝ) ≠ 0)] <;> ring

theorem diagonal_pairing :
    squaredDistance pointX pointX ≤ intermediate pointX pointX ∧
    intermediate pointX pointX ≤ differentialPair pointX pointX ∧
    squaredDistance pointX pointX = 0 ∧ intermediate pointX pointX = 0 ∧
    differentialPair pointX pointX = 0 := by
  have h := weightedEntropy_pairing weights pointX pointX weightsPos pointX_mem pointX_mem
  exact ⟨h.1,h.2,by simp [squaredDistance],by simp [intermediate],by simp [differentialPair]⟩

end BanditRL.OnlineEntropyCanary
