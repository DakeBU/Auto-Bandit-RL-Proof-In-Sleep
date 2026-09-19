import BanditRLProof.Algorithms.HOORegretAlgebra

/-! Integer depth optimization with positive logarithms, including horizon one. -/
namespace BanditRLProof.HOO
set_option autoImplicit false

private theorem balance_identities {N L d : ℝ} (hN : 0<N) (hL : 0<L) (hd : 0<d) :
    N*(L/N)^(1/(d+2)) = N^((d+1)/(d+2))*L^(1/(d+2)) ∧
    L*((L/N)^(1/(d+2)))^(-(1+d)) = N^((d+1)/(d+2))*L^(1/(d+2)) := by
  let a := 1/(d+2)
  let b := (d+1)/(d+2)
  have hd2 : d+2≠0 := ne_of_gt (by linarith)
  have hab : 1-a=b := by dsimp [a, b]; field_simp; ring
  have hae : a*(-(1+d))=a-1 := by dsimp [a]; field_simp; ring
  have hn : N/N^a=N^b := by
    rw [← hab, Real.rpow_sub hN, Real.rpow_one]
  have hl : L*L^(a-1)=L^a := by
    calc
      L*L^(a-1)=L^((1:ℝ)+(a-1)) := by rw [Real.rpow_add hL, Real.rpow_one]
      _ = L^a := by congr 1; ring
  constructor
  · change N*(L/N)^a=N^b*L^a
    rw [Real.div_rpow hL.le hN.le]
    calc
      N*(L^a/N^a)=(N/N^a)*L^a := by ring
      _ = _ := by rw [hn]
  · change L*((L/N)^a)^(-(1+d))=N^b*L^a
    rw [← Real.rpow_mul (div_pos hL hN).le, hae, Real.div_rpow hL.le hN.le]
    have he : a-1 = -b := by linarith
    rw [he, Real.rpow_neg hN.le]
    calc
      L*(L^(-b)/(N^b)⁻¹)=N^b*(L*L^(-b)) := by simp only [div_inv_eq_mul]; ring
      _ = N^b*L^a := by rw [← he, hl]

/-- Chooses a genuine integer H>=1; no real-valued cutoff or asymptotic
rounding assumption is used. The same estimate works when L=N. -/
theorem exists_regret_depth {ρ d A B N L : ℝ}
    (hr : 0<ρ) (hr1 : ρ<1) (hd : 0<d) (hA : 0≤A) (hB : 0≤B)
    (hN : 0<N) (hL : 0<L) (hLN : L≤N) :
    ∃ H : ℕ, 1≤H ∧ A*N*ρ^H+B*L*(ρ^H)^(-(1+d)) ≤
      (A+B*ρ^(-(1+d)))*N^((d+1)/(d+2))*L^(1/(d+2)) := by
  let t := (L/N)^(1/(d+2))
  have ht : 0<t := Real.rpow_pos_of_pos (div_pos hL hN) _
  have ht1 : t≤1 := Real.rpow_le_one (div_pos hL hN).le ((div_le_one hN).mpr hLN)
    (by positivity)
  obtain ⟨n, hn, htn⟩ := exists_nat_pow_near_of_lt_one ht ht1 hr hr1
  have hlo : ρ*t≤ρ^(n+1) := by
    simpa only [pow_succ, mul_comm] using mul_le_mul_of_nonneg_left htn hr.le
  have hz : -(1+d)≤0 := by linarith
  have hp := Real.rpow_le_rpow_of_nonpos (mul_pos hr ht) hlo hz
  rw [Real.mul_rpow hr.le ht.le] at hp
  obtain ⟨hbal1, hbal2⟩ := balance_identities hN hL hd
  refine ⟨n+1, by omega, ?_⟩
  calc
    _ ≤ A*N*t + B*L*(ρ^(-(1+d))*t^(-(1+d))) :=
      add_le_add (mul_le_mul_of_nonneg_left hn.le (mul_nonneg hA hN.le))
        (mul_le_mul_of_nonneg_left hp (mul_nonneg hB hL.le))
    _ = A*(N*t)+(B*ρ^(-(1+d)))*(L*t^(-(1+d))) := by ring
    _ = _ := by dsimp only [t]; rw [hbal1, hbal2]; ring

theorem log_horizon_pos_le (N : ℕ) (hN : 1≤N) :
    0<Real.log (max (N:ℝ) 2) ∧ Real.log (max (N:ℝ) 2)≤(N:ℝ) := by
  have hn : (1:ℝ)≤N := by exact_mod_cast hN
  have hm : (1:ℝ)<max (N:ℝ) 2 := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  refine ⟨Real.log_pos hm, ?_⟩
  have hh := Real.log_le_sub_one_of_pos (lt_trans zero_lt_one hm)
  have hh2 : max (N:ℝ) 2 ≤ (N:ℝ)+1 := max_le (by linarith) (by linarith)
  linarith

end BanditRLProof.HOO
