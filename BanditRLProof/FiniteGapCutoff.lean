import BanditRLProof.FiniteGapLayerCake

/-! A cutoff layer-cake envelope that pays the baseline once per observation. -/
namespace BanditRLProof.FiniteGapLayerCake
open MeasureTheory
set_option autoImplicit false

theorem sum_le_cutoff_integral {ι : Type*} (s : Finset ι) (d : ι → ℝ) (a b : ℝ)
    (hab : a≤b) (hd : ∀t∈s, d t≤b) (ell : ℝ → ℝ)
    (hi : IntervalIntegrable ell volume a b)
    (hc : ∀x∈Set.Icc a b, ((s.filter (fun t => x≤d t)).card:ℝ)≤ell x+1) :
    ∑t∈s, d t ≤ a*(s.card:ℝ)+(∫x in a..b, ell x)+(b-a) := by
  classical
  let large := s.filter (fun t => a≤d t)
  have hlarge : ∀t∈large, d t∈Set.Icc a b := by
    intro t ht
    exact ⟨(Finset.mem_filter.mp ht).2,hd t (Finset.mem_filter.mp ht).1⟩
  have hbase : ∑t∈s, d t≤a*(s.card:ℝ)+∑t∈large, (d t-a) := by
    have h := Finset.sum_le_sum (s:=s) (fun t _ =>
      show d t≤a+(if a≤d t then d t-a else 0) by split_ifs <;> linarith)
    simpa only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,mul_comm,
      ← Finset.sum_filter] using h
  have hid := sum_eq_layerCake large d a b hlarge
  have he : (∑t∈large, (d t-a))=
      ∫x in a..b, ((large.filter (fun t => x≤d t)).card:ℝ) := by
    rw [Finset.sum_sub_distrib,Finset.sum_const,nsmul_eq_mul,hid]
    ring
  have htail (x : ℝ) (hx : x∈Set.Icc a b) :
      large.filter (fun t => x≤d t)=s.filter (fun t => x≤d t) := by
    ext t
    simp only [large,Finset.mem_filter]
    constructor
    · intro h
      exact ⟨h.1.1,h.2⟩
    · intro h
      exact ⟨⟨h.1,hx.1.trans h.2⟩,h.2⟩
  have hOne : IntervalIntegrable (fun _ : ℝ => (1:ℝ)) volume a b := intervalIntegrable_const
  have hint := intervalIntegral.integral_mono_on hab (intervalIntegrable_card large d a b)
    (hi.add hOne) (fun x hx => by rw [htail x hx]; exact hc x hx)
  rw [intervalIntegral.integral_add hi hOne,
    intervalIntegral.integral_const] at hint
  simp only [smul_eq_mul,mul_one] at hint
  rw [he] at hbase
  linarith

end BanditRLProof.FiniteGapLayerCake
