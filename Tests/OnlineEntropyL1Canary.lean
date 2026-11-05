import BanditRLProof.OnlineEntropyL1

noncomputable section
open Finset
namespace BanditRL.OnlineEntropy.L1Canary

private def weights (i : Fin 2) : ℝ := if i = 0 then 1 else 2
private def p : EntropyL1 2 := entropyCoordinates.symm (fun i => if i = 0 then 1/2 else 1)
private def q : EntropyL1 2 := entropyCoordinates.symm (fun i => if i = 0 then 1/4 else 3/2)
private def mid : EntropyL1 2 := (1/2 : ℝ) • p + (1/2 : ℝ) • q
private def planeNormal : EntropyL1 2 →L[ℝ] ℝ :=
  ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0) +
    (1/2 : ℝ) • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1)).comp
      (entropyCoordinates (d := 2)).toContinuousLinearMap
private def slope : EntropyL1 2 →L[ℝ] ℝ :=
  (fderiv ℝ (weightedEntropy weights) (entropyCoordinates p)).comp
    (entropyCoordinates (d := 2)).toContinuousLinearMap

private theorem pos_weights (i : Fin 2) : 0 < weights i := by
  fin_cases i <;> norm_num [weights]

private theorem model_feasible : p ∈ entropyFeasible weights ∧ q ∈ entropyFeasible weights := by
  constructor
  · constructor
    · intro i; fin_cases i <;> norm_num [p,entropyCoordinates]
    · norm_num [Fin.sum_univ_two,p,weights,entropyCoordinates]
  · constructor
    · intro i; fin_cases i <;> norm_num [q,entropyCoordinates]
    · norm_num [Fin.sum_univ_two,q,weights,entropyCoordinates]

private theorem distance : ‖p-q‖ = 3/4 := by
  rw [PiLp.norm_eq_of_L1,Fin.sum_univ_two]
  norm_num [p,q,entropyCoordinates,Real.norm_eq_abs,PiLp.sub_apply]

private theorem normal_on (z : EntropyL1 2) (hz : z ∈ entropyFeasible weights) :
    planeNormal z = 1 := by
  have hh := hz.2
  rw [Fin.sum_univ_two] at hh
  norm_num [weights] at hh
  change z.ofLp 0 + (1/2:ℝ) * z.ofLp 1 = 1
  linarith only [hh]

theorem weighted_midpoint :
    entropyOnL1 weights mid ≤
      (entropyOnL1 weights p + entropyOnL1 weights q) / 2 - 9/128 ∧
    p ∈ entropyFeasible weights ∧ q ∈ entropyFeasible weights ∧
    (∑ i, entropyCoordinates p i) = 3/2 ∧
    (∑ i, entropyCoordinates q i) = 7/4 ∧
    ‖p-q‖ = 3/4 := by
  obtain ⟨hp,hq⟩ := model_feasible
  have hh := (weightedEntropy_l1_interpolation weights pos_weights).2 p hp q hq
    (1/2) (by norm_num) (by norm_num)
  rw [show (1:ℝ)-1/2=1/2 by norm_num,distance] at hh
  refine ⟨?_,hp,hq,?_,?_,distance⟩
  · unfold mid
    linarith only [hh]
  · norm_num [Fin.sum_univ_two,p,entropyCoordinates]
  · norm_num [Fin.sum_univ_two,q,entropyCoordinates]

theorem two_relative_supports :
    entropyOnL1 weights p + slope (q-p) + 9/32 ≤ entropyOnL1 weights q ∧
    entropyOnL1 weights p + (slope+planeNormal) (q-p) + 9/32 ≤ entropyOnL1 weights q ∧
    slope ≠ slope + planeNormal ∧
    (∀ z ∈ entropyFeasible weights,
      entropyOnL1 weights p + slope (z-p) ≤ entropyOnL1 weights z) ∧
    (∀ z ∈ entropyFeasible weights,
      entropyOnL1 weights p + (slope+planeNormal) (z-p) ≤ entropyOnL1 weights z) := by
  obtain ⟨hp,hq⟩ := model_feasible
  have dn : ‖q-p‖ = 3/4 := (norm_sub_rev q p).trans distance
  have h := weightedEntropy_l1_support_growth weights pos_weights q p hq hp
  have hd := h.1
  change entropyOnL1 weights p + slope (q-p) + ‖q-p‖^2/2 ≤ entropyOnL1 weights q at hd
  have hs (z : EntropyL1 2) (hz : z ∈ entropyFeasible weights) :
      entropyOnL1 weights p + slope (z-p) ≤ entropyOnL1 weights z := by
    have hz' := (weightedEntropy_l1_support_growth weights pos_weights z p hz hp).1
    change entropyOnL1 weights p + slope (z-p) + ‖z-p‖^2/2 ≤ entropyOnL1 weights z at hz'
    linarith only [hz',sq_nonneg ‖z-p‖]
  have hs' (z : EntropyL1 2) (hz : z ∈ entropyFeasible weights) :
      entropyOnL1 weights p + (slope+planeNormal) (z-p) ≤ entropyOnL1 weights z := by
    rw [ContinuousLinearMap.add_apply, map_sub planeNormal, normal_on z hz, normal_on p hp]
    simpa using hs z hz
  have shifted := h.2 (slope+planeNormal) hs'
  rw [dn] at hd shifted
  refine ⟨by linarith only [hd],by linarith only [shifted],?_,hs,hs'⟩
  intro eq
  have bad := DFunLike.congr_fun eq p
  rw [ContinuousLinearMap.add_apply,normal_on p hp] at bad
  linarith

end BanditRL.OnlineEntropy.L1Canary
