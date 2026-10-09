from leaf_driver import *
assert load(RUN/'switching_scalar_lower_bound-fence-compared-v2.json')['unchanged']
lower('switching_vector_lower_bound','''  classical
  have hin (a b : ℝ) : inner ℝ a b = b * a := rfl
  have hvec (t : ℕ) :
      BanditRL.OnlineSubgradientDescent.iterate BanditRL.OnlineHuber.fullSpace (powerSteps α)
        (fun s z => (switchLoss T v s z : EReal)) 0 t =
      (-(∑ i ∈ range t, powerSteps α i * switchSlope T i)) • v := by
    have hloss : (fun s z => (switchLoss T v s z : EReal)) =
        (fun s z => ((inner ℝ (switchSlope T s • v) z + 0 : ℝ) : EReal)) := by
      funext s z
      simp [switchLoss, real_inner_smul_left]
    rw [hloss, iterate_affine_prefix]
    simp only [zero_sub, smul_smul, ← Finset.sum_smul, neg_smul]
  have hscalar (t : ℕ) :
      BanditRL.OnlineSubgradientDescent.iterate BanditRL.OnlineHuber.fullSpace (powerSteps α)
        (fun s z => (switchLoss T (1 : ℝ) s z : EReal)) 0 t =
      -(∑ i ∈ range t, powerSteps α i * switchSlope T i) := by
    have hloss : (fun (s : ℕ) (z : ℝ) => (switchLoss T (1 : ℝ) s z : EReal)) =
        (fun s z => ((inner ℝ (switchSlope T s : ℝ) z + 0 : ℝ) : EReal)) := by
      funext s z
      simp [switchLoss, hin, mul_comm]
    rw [hloss, iterate_affine_prefix]
    simp
  have hreg : BanditRL.OnlineSubgradientDescent.regret BanditRL.OnlineHuber.fullSpace (powerSteps α)
      (fun t z => (switchLoss T v t z : EReal)) 0 0 T =
      BanditRL.OnlineSubgradientDescent.regret BanditRL.OnlineHuber.fullSpace (powerSteps α)
        (fun t z => (switchLoss T (1 : ℝ) t z : EReal)) 0 0 T := by
    unfold BanditRL.OnlineSubgradientDescent.regret
    simp only [EReal.toReal_coe]
    simp_rw [hvec, hscalar]
    apply Finset.sum_congr rfl
    intro t ht
    simp [switchLoss, inner_smul_right, real_inner_self_eq_norm_sq, hv, hin]
  rw [hreg]
  exact switching_scalar_lower_bound α hα0 hα1 T hT
''',['switching_scalar_lower_bound actual same canonical scalar OSD run','iterate_affine_prefix actual canonical vector OSD run','unit-vector inner/norm identity'])
lower('theorem_5_4','''  obtain ⟨v, hv⟩ := exists_norm_eq E (show (0 : ℝ) ≤ 1 by norm_num)
  refine ⟨switchLoss T v, ?_, switching_vector_lower_bound α hα0 hα1 T hT v hv⟩
  intro t ht
  exact switching_loss_regular T v hv t
''',['switching_vector_lower_bound actual SAME canonical vector run','switching_loss_regular actual constructed convex1-Lipschitz losses','exists_norm_eq primary mathlib API with Nontrivial E'])
write(RUN/'full-source-local-milestone-v1.json',dict(status='all11 frozen source terminals focused compiled/fenced only',full_source_lower_bound_body_locally_compiled=True,all_package_gates_open=True,exact_canary_contracts_and_proofs_open=True,distinct_final_BODY_review_open=True,chapter_complete=False,whole_Goal='ACTIVE'))
