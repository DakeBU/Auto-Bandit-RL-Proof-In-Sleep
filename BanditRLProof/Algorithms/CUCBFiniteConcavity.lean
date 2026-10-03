import BanditRLProof.Algorithms.CUCBGapCutoff
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Jensen

/-! The source finite-concavity obligation, instantiated with actual
under-sampled charge counts, including zero counts and zero horizon. -/
namespace BanditRLProof.CUCB.SourceModel
open MeasureTheory ProbabilityTheory
set_option autoImplicit false

theorem finite_power_sum_le {m : ℕ} (hm : 0<m) (z : Fin m → ℝ) (hz : ∀i, 0≤z i)
    (H p : ℝ) (hp0 : 0≤p) (hp1 : p≤1) (hH : (∑i:Fin m, z i)≤H) :
    (∑i:Fin m, (z i)^p)≤(m:ℝ)^(1-p)*H^p := by
  have hmR : 0<(m:ℝ) := by exact_mod_cast hm
  have hw : (0:ℝ)≤1/(m:ℝ) := by positivity
  have hwSum : (∑_i:Fin m, (1:ℝ)/(m:ℝ))=1 := by simp [div_eq_mul_inv,ne_of_gt hmR]
  have h := (Real.concaveOn_rpow hp0 hp1).le_map_sum (t:=Finset.univ)
    (w:=fun _ : Fin m => (1:ℝ)/(m:ℝ)) (p:=z) (fun _ _ => hw) hwSum (fun i _ => hz i)
  simp only [smul_eq_mul,← Finset.mul_sum] at h
  have hsum : 0≤∑i:Fin m, z i := Finset.sum_nonneg (fun i _ => hz i)
  rw [Real.mul_rpow hw hsum] at h
  have hh := mul_le_mul_of_nonneg_left h hmR.le
  have he : (m:ℝ)*(1/(m:ℝ))^p=(m:ℝ)^(1-p) := by
    rw [one_div,Real.inv_rpow,Real.rpow_sub hmR,Real.rpow_one,div_eq_mul_inv]
    exact hmR.le
  have hcancel : (m:ℝ)*(1/(m:ℝ))=1 := by field_simp
  simp only [← mul_assoc,hcancel,one_mul,he] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hsum hH hp0)
    (Real.rpow_nonneg hmR.le _))

variable {A : Type*} [Fintype A] [Nonempty A] [MeasurableSpace A]
  {m : ℕ} {M : FeedbackModel A m} (S : SourceModel M)

theorem underChargeCount_power_sum_le (H : ℕ) (actions : ℕ → A)
    (ω : ℝ) (hω : 0<ω) (hω1 : ω≤1) :
    (∑i:Fin m, ((S.underChargeTimes H actions i).card:ℝ)^(1-ω/2))≤
      (m:ℝ)^(ω/2)*(H:ℝ)^(1-ω/2) := by
  have hm : 0<m := by
    obtain ⟨i,_⟩ := M.arms_nonempty
    have hi := i.isLt
    omega
  have h := finite_power_sum_le hm
    (fun i => ((S.underChargeTimes H actions i).card:ℝ)) (fun i => Nat.cast_nonneg _)
    (H:ℝ) (1-ω/2) (by linarith) (by linarith) (S.sum_card_underChargeTimes_le H actions)
  simpa only [show 1-(1-ω/2)=ω/2 by ring] using h

end BanditRLProof.CUCB.SourceModel

