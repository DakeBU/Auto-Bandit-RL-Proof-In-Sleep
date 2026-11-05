import BanditRLProof.OnlineEntropyL1
import BanditRLProof.OnlineEntropyWeightedPairing
import BanditRLProof.Algorithms.KLUCBBernoulli
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

noncomputable section
open Finset
namespace BanditRL.OnlineEntropy.KLBoundary

def entropy {d : ℕ} (x : Fin d → ℝ) : ℝ := ∑ i, x i * Real.log (x i)
def divergence {d : ℕ} (x y : Fin d → ℝ) : ℝ :=
  entropy x - entropy y - fderiv ℝ entropy y (x-y)
def finiteKL {d : ℕ} (x y : Fin d → ℝ) : ℝ := ∑ i, x i * Real.log (x i / y i)
abbrev binaryVector (p : ℝ) (i : Fin 2) : ℝ := if i = 0 then p else 1 - p

theorem generalized_identity {d : ℕ} (x y : Fin d → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 < y i) :
    DifferentiableAt ℝ entropy y ∧
    divergence x y = ∑ i, (x i * Real.log (x i / y i) - x i + y i) := by
  have he : entropy (d := d) = weightedEntropy (fun _ : Fin d => (1 : ℝ)) := by
    funext z
    simp only [entropy, weightedEntropy, one_mul]
  have hd := weightedEntropy_differential (fun _ : Fin d => (1 : ℝ)) y hy
  rw [← he] at hd
  refine ⟨hd.1, ?_⟩
  rw [divergence, hd.2 (x - y)]
  simp only [one_mul, Pi.sub_apply, entropy, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rcases (hx i).eq_or_lt with hz | hp
  · rw [← hz]
    simp <;> ring
  · rw [Real.log_div hp.ne' (hy i).ne']
    ring

theorem simplex_identity {d : ℕ} (x y : Fin d → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 < y i)
    (sx : ∑ i, x i = 1) (sy : ∑ i, y i = 1) :
    divergence x y = finiteKL x y := by
  rw [(generalized_identity x y hx hy).2, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, sx, sy, finiteKL]
  ring

end BanditRL.OnlineEntropy.KLBoundary

namespace BanditRL.OnlineEntropy.KLBoundary
private theorem half_weighted_log (z : ℝ) :
    z * Real.log (z / (1/2 : ℝ)) = -Real.negMulLog z + z * Real.log 2 := by
  by_cases hz : z = 0
  · subst z
    simp
  · rw [show z / (1/2 : ℝ) = z * 2 by ring,
      Real.log_mul hz (by norm_num : (2 : ℝ) ≠ 0)]
    unfold Real.negMulLog
    ring

private theorem fixed_half_normal_form (p : ℝ) :
    BanditRLProof.KLUCB.bernoulliKLCore p (1/2) =
      -Real.negMulLog p - Real.negMulLog (1-p) + Real.log 2 := by
  unfold BanditRLProof.KLUCB.bernoulliKLCore
  rw [show (1 : ℝ) - 1/2 = 1/2 by norm_num, half_weighted_log, half_weighted_log]
  ring

private theorem fixed_half_continuous_endpoints :
    let k := fun p : ℝ => BanditRLProof.KLUCB.bernoulliKLCore p (1/2);
    ContinuousOn k (Set.Icc 0 1) ∧ k 0 = Real.log 2 ∧ k 1 = Real.log 2 := by
  dsimp only
  have formula : (fun p : ℝ => BanditRLProof.KLUCB.bernoulliKLCore p (1/2)) =
      (fun p : ℝ => -Real.negMulLog p - Real.negMulLog (1-p) + Real.log 2) :=
    funext fixed_half_normal_form
  constructor
  · rw [formula]
    exact ((Real.continuous_negMulLog.neg.sub
      (Real.continuous_negMulLog.comp (continuous_const.sub continuous_id))).add
      continuous_const).continuousOn
  · constructor <;> rw [fixed_half_normal_form] <;> simp

private theorem fixed_half_binary_identity (p : ℝ) (_hp : p ∈ Set.Icc (0 : ℝ) 1) :
    finiteKL (binaryVector p) (binaryVector (1/2)) =
      BanditRLProof.KLUCB.bernoulliKLCore p (1/2) := by
  unfold finiteKL BanditRLProof.KLUCB.bernoulliKLCore
  simp [Fin.sum_univ_two, binaryVector]

end BanditRL.OnlineEntropy.KLBoundary

namespace BanditRL.OnlineEntropy.KLBoundary
open Finset

theorem interior_lower_bound {d : ℕ} (x y : Fin d → ℝ)
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i)
    (sx : ∑ i, x i = 1) (sy : ∑ i, y i = 1) :
    (∑ i, |x i - y i|)^2 / 2 ≤ finiteKL x y := by
  let c := fun _ : Fin d => (1:ℝ)
  let X := (entropyCoordinates (d:=d)).symm x
  let Y := (entropyCoordinates (d:=d)).symm y
  have he : entropy (d := d) = weightedEntropy c := by
    funext z; simp [entropy,weightedEntropy,c]
  have hX : X ∈ entropyFeasible c := by
    change entropyCoordinates X ∈ weightedSimplex c
    simpa only [X,ContinuousLinearEquiv.apply_symm_apply,c,weightedSimplex,Set.mem_setOf_eq,div_one] using And.intro hx sx
  have hY : Y ∈ entropyFeasible c := by
    change entropyCoordinates Y ∈ weightedSimplex c
    simpa only [Y,ContinuousLinearEquiv.apply_symm_apply,c,weightedSimplex,Set.mem_setOf_eq,div_one] using And.intro hy sy
  have growth := (weightedEntropy_l1_support_growth c (fun _ => zero_lt_one) X Y hX hY).1
  have hn : ‖X-Y‖ = ∑ i, |x i-y i| := by
    rw [PiLp.norm_eq_of_L1]
    apply Finset.sum_congr rfl; intro i _
    exact Real.norm_eq_abs _
  rw [hn] at growth
  simp only [entropyOnL1,map_sub,X,Y,ContinuousLinearEquiv.apply_symm_apply,← he] at growth
  have ident := simplex_identity x y (fun i => (hx i).le) hy sx sy
  unfold divergence at ident
  rw [map_sub] at ident
  linarith only [ident,growth]

theorem binary_boundary :
    let k := fun p : ℝ => BanditRLProof.KLUCB.bernoulliKLCore p (1/2);
    ContinuousOn k (Set.Icc 0 1) ∧
    k 0 = Real.log 2 ∧ k 1 = Real.log 2 ∧
    (∀ p ∈ Set.Icc (0 : ℝ) 1,
      finiteKL (binaryVector p) (binaryVector (1/2)) = k p ∧
      2 * (p - 1/2)^2 ≤ k p) := by
  dsimp only
  obtain ⟨cont,at0,at1⟩ := fixed_half_continuous_endpoints
  refine ⟨cont,at0,at1,?_⟩
  intro p hp
  refine ⟨fixed_half_binary_identity p hp,?_⟩
  let k := fun z : ℝ => BanditRLProof.KLUCB.bernoulliKLCore z (1/2)
  have hlower (z : ℝ) (hz : z ∈ Set.Ioo (0:ℝ) 1) : 2*(z-1/2)^2 ≤ k z := by
    have posX (i : Fin 2) : 0 < binaryVector z i := by
      fin_cases i <;> simp [binaryVector] <;> obtain ⟨h0,h1⟩ := hz <;> linarith
    have posY (i : Fin 2) : 0 < binaryVector (1/2) i := by fin_cases i <;> norm_num [binaryVector]
    have hx : ∑ i, binaryVector z i = 1 := by simp [Fin.sum_univ_two,binaryVector] <;> ring
    have hy : ∑ i, binaryVector (1/2) i = 1 := by norm_num [Fin.sum_univ_two,binaryVector]
    have h := interior_lower_bound _ _ posX posY hx hy
    rw [fixed_half_binary_identity z ⟨hz.1.le,hz.2.le⟩] at h
    have mass : (∑ i, |binaryVector z i-binaryVector (1/2) i|) = 2*|z-1/2| := by
      rw [Fin.sum_univ_two]
      change |z-1/2| + |(1-z)-(1-1/2)| = _
      rw [show (1:ℝ)-1/2 = 1/2 by norm_num]
      rw [show (1-z)-(1/2) = -(z-1/2) by ring, abs_neg]
      ring
    rw [mass,mul_pow,sq_abs] at h
    dsimp [k]; linarith only [h]
  apply le_on_closure (f:=fun z : ℝ => 2*(z-1/2)^2) (g:=k) hlower
  · fun_prop
  · rw [closure_Ioo (by norm_num : (0:ℝ) ≠ 1)]; exact cont
  · rwa [closure_Ioo (by norm_num : (0:ℝ) ≠ 1)]

theorem scaled_binary_use (t s : ℝ) (ht : 1 ≤ t) (hs : |s| ≤ t) :
    s^2 / (2*t) ≤ t * BanditRLProof.KLUCB.bernoulliKLCore (1/2 + s/(2*t)) (1/2) := by
  have ht0 : 0 < t := by linarith
  have hp : 1/2+s/(2*t) ∈ Set.Icc (0:ℝ) 1 := by
    obtain ⟨lo,hi⟩ := abs_le.mp hs
    constructor <;> change _ ≤ _
    · have h : -(1/2:ℝ) ≤ s/(2*t) := (le_div_iff₀ (by positivity)).mpr (by linarith only [lo])
      linarith
    · have h : s/(2*t) ≤ (1/2:ℝ) := (div_le_iff₀ (by positivity)).mpr (by linarith only [hi])
      linarith
  have h := (binary_boundary.2.2.2 _ hp).2
  have hm := mul_le_mul_of_nonneg_left h ht0.le
  convert hm using 1 <;> field_simp [ht0.ne'] <;> ring

end BanditRL.OnlineEntropy.KLBoundary
