import BanditRLProof.Algorithms.CUCBSourceModel
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Scalar inverse on the full frozen positive-gap interval, and the exact
integrable sampling threshold used in the refined source regret integral. -/
namespace BanditRLProof.CUCB
open MeasureTheory
set_option autoImplicit false

theorem thresholdCoefficient_antitone {u v p : ℝ} (hu : 0<u) (huv : u≤v) (hp : 0<p) :
    thresholdCoefficient v p≤thresholdCoefficient u p := by
  have hs : u^2≤v^2 := by nlinarith
  unfold thresholdCoefficient
  split_ifs
  · exact div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hu) hs
  · apply max_le_max _ le_rfl
    exact div_le_div_of_nonneg_left (by norm_num) (mul_pos (sq_pos_of_pos hu) hp)
      (mul_le_mul_of_nonneg_right hs hp.le)

namespace SourceModel
variable {A : Type*} [Fintype A] [Nonempty A] [MeasurableSpace A] {m : ℕ}
variable {M : FeedbackModel A m} (S : SourceModel M)

noncomputable def gapDomain : Set ℝ := Set.Ioc 0 (maxPositiveGap S.score M.trueInput S.alpha)

/-- The value outside the source inverse domain is zero by convention;
all inverse and integral claims below explicitly stay inside the domain. -/
noncomputable def inverseAt (d : ℝ) : ℝ := by
  classical
  exact
  if h : d∈S.gapDomain then Classical.choose (S.inverse_range d h.1 h.2) else 0

theorem inverseAt_spec {d : ℝ} (hd : d∈S.gapDomain) :
    0<S.inverseAt d ∧ S.modulus (S.inverseAt d)=d := by
  have h := Classical.choose_spec (S.inverse_range d hd.1 hd.2)
  rw [inverseAt, dif_pos hd]
  refine ⟨lt_of_le_of_ne h.1 ?_, h.2⟩
  intro hz
  rw [← hz, S.modulus_zero] at h
  linarith [h.2, hd.1]

theorem inverseAt_unique {d u : ℝ} (hd : d∈S.gapDomain) (hu : 0≤u)
    (he : S.modulus u=d) : S.inverseAt d=u :=
  S.modulus_strictMono.injOn (S.inverseAt_spec hd).1.le hu ((S.inverseAt_spec hd).2.trans he.symm)

theorem inverseAt_gap (a : A) (ha : 0<S.gap a) : S.inverseAt (S.gap a)=S.inverseGap a := by
  apply S.inverseAt_unique ⟨ha, gap_le_maxPositiveGap S.score M.trueInput S.alpha a⟩
    (S.inverseGap_spec a ha).1.le (S.inverseGap_spec a ha).2

theorem inverseAt_strictMono : StrictMonoOn S.inverseAt S.gapDomain := by
  intro d hd e he hde
  by_contra hn
  have hv := le_of_not_gt hn
  have hf := S.modulus_strictMono.monotoneOn (S.inverseAt_spec he).1.le
    (S.inverseAt_spec hd).1.le hv
  rw [(S.inverseAt_spec hd).2, (S.inverseAt_spec he).2] at hf
  linarith

noncomputable def gapThreshold (n : ℕ) (p d : ℝ) : ℝ := samplingThreshold n (S.inverseAt d) p

theorem gapThreshold_antitone (n : ℕ) (hn : 1≤n) (p : ℝ) (hp : 0<p) :
    AntitoneOn (S.gapThreshold n p) S.gapDomain := by
  intro d hd e he hde
  apply mul_le_mul_of_nonneg_left
    (thresholdCoefficient_antitone (S.inverseAt_spec hd).1
      (S.inverseAt_strictMono.monotoneOn hd he hde) hp)
  exact Real.log_nonneg (by exact_mod_cast hn)

theorem gapThreshold_nonneg (n : ℕ) (hn : 1≤n) (p : ℝ) (hp : 0<p)
    {d : ℝ} (hd : d∈S.gapDomain) : 0≤S.gapThreshold n p d :=
  mul_nonneg (Real.log_nonneg (by exact_mod_cast hn))
    (thresholdCoefficient_pos (S.inverseAt_spec hd).1 hp).le

theorem gapThreshold_intervalIntegrable (n : ℕ) (hn : 1≤n) (p : ℝ) (hp : 0<p)
    {a b : ℝ} (ha : a∈S.gapDomain) (hb : b∈S.gapDomain) :
    IntervalIntegrable (S.gapThreshold n p) volume a b := by
  apply AntitoneOn.intervalIntegrable
  apply (S.gapThreshold_antitone n hn p hp).mono
  intro x hx
  change min a b≤x ∧ x≤max a b at hx
  exact ⟨lt_of_lt_of_le (lt_min ha.1 hb.1) hx.1,
    hx.2.trans (max_le ha.2 hb.2)⟩

end SourceModel
end BanditRLProof.CUCB


