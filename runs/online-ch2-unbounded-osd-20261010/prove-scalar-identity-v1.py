from leaf_driver import *
assert load(RUN/'phi_range-fence-compared-v3.json')['unchanged']
lower('switching_scalar_regret_identity','''  classical
  let m : ℕ := (T + 1) / 2
  let k : ℕ := T / 2
  have hmT : m ≤ T := by dsimp [m]; omega
  have hmk : m + k = T := by dsimp [m, k]; omega
  have hcast : (T : ℝ) = (m : ℝ) + (k : ℝ) := by exact_mod_cast hmk.symm
  have hc (n : ℕ) : (∑ t ∈ range n, switchSlope T t) =
      (n : ℝ) - 2 * ((min n m : ℕ) : ℝ) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ, ih]
      by_cases hn : n < m
      · rw [show switchSlope T n = -1 by simp [switchSlope, ← m, hn],
          min_eq_left (Nat.le_of_lt hn), min_eq_left (Nat.succ_le_of_lt hn)]
        push_cast
        ring
      · have hmn : m ≤ n := Nat.le_of_not_gt hn
        rw [show switchSlope T n = 1 by simp [switchSlope, ← m, hn],
          min_eq_right hmn, min_eq_right (hmn.trans (Nat.le_succ n))]
        push_cast
        ring
  have hsuf (i : ℕ) (hi : i < T) : (∑ t ∈ Ico (i + 1) T, switchSlope T t) =
      (T : ℝ) - 2 * (m : ℝ) - (((i + 1 : ℕ) : ℝ) - 2 * ((min (i + 1) m : ℕ) : ℝ)) := by
    rw [sum_Ico_eq_sub _ (Nat.succ_le_of_lt hi), hc T, hc (i + 1), min_eq_right hmT]
  have hrun (t : ℕ) :
      BanditRL.OnlineSubgradientDescent.iterate BanditRL.OnlineHuber.fullSpace (powerSteps α)
        (fun s z => (switchLoss T (1 : ℝ) s z : EReal)) 0 t =
      -(∑ i ∈ range t, powerSteps α i * switchSlope T i) := by
    have hloss : (fun (s : ℕ) (z : ℝ) => (switchLoss T (1 : ℝ) s z : EReal)) =
        (fun s z => ((inner ℝ (switchSlope T s : ℝ) z + 0 : ℝ) : EReal)) := by
      funext s z
      simp [switchLoss, mul_comm]
    rw [hloss, iterate_affine_prefix]
    simp
  have hreg :
      BanditRL.OnlineSubgradientDescent.regret BanditRL.OnlineHuber.fullSpace (powerSteps α)
        (fun t z => (switchLoss T (1 : ℝ) t z : EReal)) 0 0 T =
      -(∑ i ∈ range T, powerSteps α i * switchSlope T i *
        (∑ t ∈ Ico (i + 1) T, switchSlope T t)) := by
    unfold BanditRL.OnlineSubgradientDescent.regret
    simp only [hrun, EReal.toReal_coe, switchLoss, RCLike.inner_apply, conj_trivial,
      mul_one, mul_zero, sub_zero]
    calc
      _ = -(∑ t ∈ Ico 0 T, ∑ i ∈ Ico 0 t,
          powerSteps α i * switchSlope T i * switchSlope T t) := by
        simp only [Nat.Ico_zero_eq_range, mul_neg, Finset.mul_sum, Finset.sum_neg_distrib]
        congr 1
        apply Finset.sum_congr rfl
        intro t ht
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = -(∑ i ∈ range T, powerSteps α i * switchSlope T i *
          (∑ t ∈ Ico (i + 1) T, switchSlope T t)) := by
        rw [← Finset.sum_Ico_Ico_comm' 0 T
          (fun i t => powerSteps α i * switchSlope T i * switchSlope T t)]
        simp only [Nat.Ico_zero_eq_range, Finset.mul_sum]
  have hfirst : -(∑ i ∈ range m, powerSteps α i * switchSlope T i *
      (∑ t ∈ Ico (i + 1) T, switchSlope T t)) =
      (∑ i ∈ range m, ((i + 1 : ℕ) : ℝ) * powerSteps α i) -
        ((m : ℝ) - (k : ℝ)) * (∑ i ∈ range m, powerSteps α i) := by
    rw [← Finset.sum_neg_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have him : i < m := Finset.mem_range.mp hi
    rw [hsuf i (him.trans_le hmT),
      show switchSlope T i = -1 by simp [switchSlope, ← m, him],
      min_eq_left (Nat.succ_le_of_lt him)]
    push_cast
    rw [hcast]
    ring
  have hlast : -(∑ i ∈ Ico m T, powerSteps α i * switchSlope T i *
      (∑ t ∈ Ico (i + 1) T, switchSlope T t)) =
      (∑ i ∈ Ico m T, ((i + 1 : ℕ) : ℝ) * powerSteps α i) -
        (T : ℝ) * (∑ i ∈ Ico m T, powerSteps α i) := by
    rw [← Finset.sum_neg_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have him : m ≤ i := (Finset.mem_Ico.mp hi).1
    rw [hsuf i (Finset.mem_Ico.mp hi).2,
      show switchSlope T i = 1 by simp [switchSlope, ← m, not_lt.mpr him],
      min_eq_right (him.trans (Nat.le_succ i))]
    push_cast
    ring
  have hpow (i : ℕ) : ((i + 1 : ℕ) : ℝ) * powerSteps α i =
      ((i + 1 : ℕ) : ℝ) ^ (1 - α) := by
    unfold powerSteps
    rw [show 1 - α = 1 + (-α) by ring,
      Real.rpow_add (by exact_mod_cast Nat.succ_pos i), Real.rpow_one]
  calc
    _ = -(∑ i ∈ range m, powerSteps α i * switchSlope T i *
          (∑ t ∈ Ico (i + 1) T, switchSlope T t)) -
        (∑ i ∈ Ico m T, powerSteps α i * switchSlope T i *
          (∑ t ∈ Ico (i + 1) T, switchSlope T t)) := by
      rw [hreg, ← Finset.sum_range_add_sum_Ico _ hmT]
      ring
    _ = -((m : ℝ) - (k : ℝ)) * (∑ i ∈ range m, powerSteps α i) +
        (∑ i ∈ range T, ((i + 1 : ℕ) : ℝ) ^ (1 - α)) -
        (T : ℝ) * (∑ i ∈ Ico m T, powerSteps α i) := by
      rw [sub_eq_add_neg, hfirst, hlast]
      rw [← Finset.sum_range_add_sum_Ico (fun i => ((i + 1 : ℕ) : ℝ) ^ (1 - α)) hmT]
      simp_rw [← hpow]
      ring
''',['iterate_affine_prefix actual same canonical OSD run','Finset.sum_Ico_Ico_comm\' actual finite triangular reversal','Nat ceil/floor exact split','Real.rpow_add exact shifted steps'])
write(RUN/'scalar-identity-local-milestone-v1.json',dict(leaf=targets['switching_scalar_regret_identity']['name'],status='focused compiled/frozen only',actual_run_identity_closed=True,source_lower_bound_open=True,package_BODY_accepted=False,whole_Goal='ACTIVE'))
