import BanditRLProof.Algorithms.HOORate

/-! Expected actual/cumulative regret equals expected pseudo-regret for the
constructed HOO trajectory, with bounded integrability proved. -/
namespace BanditRLProof.HOO
open MeasureTheory ProbabilityTheory
set_option autoImplicit false

theorem trajectory_reward_bounded (ν ρ : ℝ) (law : Kernel Node ℝ) [IsMarkovKernel law]
    (hbound : ∀v, ∀ᵐ y ∂law v, y ∈ Set.Icc (0:ℝ) 1) (n : ℕ) :
    ∀ᵐ Y ∂trajectory ν ρ law, Y n ∈ Set.Icc (0:ℝ) 1 := by
  cases n with
  | zero =>
    have hh := hbound (action ν ρ (fun _ => 0) 0)
    rw [← trajectory_initial_law ν ρ law] at hh
    exact (ae_map_iff (measurable_pi_apply 0).aemeasurable measurableSet_Icc).mp hh
  | succ n =>
    let μ := trajectory ν ρ law
    have hj : ∀ᵐ p ∂μ.map (Preorder.frestrictLe n) ⊗ₘ stepKernel ν ρ law n,
        p.2 ∈ Set.Icc (0:ℝ) 1 := by
      apply (Measure.ae_compProd_iff (measurableSet_Icc.preimage measurable_snd)).mpr
      exact ae_of_all _ (fun h => hbound (action ν ρ (prefixExtension n h) (n+1)))
    rw [trajectory_prefix_compProd] at hj
    exact (ae_map_iff (by fun_prop) (measurableSet_Icc.preimage measurable_snd)).mp hj

theorem integrable_trajectory_reward (ν ρ : ℝ) (law : Kernel Node ℝ) [IsMarkovKernel law]
    (hbound : ∀v, ∀ᵐ y ∂law v, y ∈ Set.Icc (0:ℝ) 1) (n : ℕ) :
    Integrable (fun Y => Y n) (trajectory ν ρ law) := by
  apply Integrable.of_bound (measurable_pi_apply n).aestronglyMeasurable 1
  filter_upwards [trajectory_reward_bounded ν ρ law hbound n] with Y hY
  rw [Real.norm_eq_abs, abs_of_nonneg hY.1]
  exact hY.2

/-- The reward mean at each actual round equals the mean of its causally
selected node. Both the initial round and the successor joint law are used. -/
theorem integral_trajectory_reward (ν ρ : ℝ) (law : Kernel Node ℝ) [IsMarkovKernel law]
    (hbound : ∀v, ∀ᵐ y ∂law v, y ∈ Set.Icc (0:ℝ) 1) (n : ℕ) :
    (∫ Y, Y n ∂trajectory ν ρ law) =
      ∫ Y, nodeMean law (action ν ρ Y n) ∂trajectory ν ρ law := by
  cases n with
  | zero =>
    have ha (Y : ℕ → ℝ) : action ν ρ Y 0=action ν ρ (fun _ => 0) 0 :=
      action_causal ν ρ Y (fun _ => 0) 0 (by intro i hi; omega)
    simp only [ha]
    rw [integral_const, probReal_univ, one_smul]
    have he := integral_map (μ := trajectory ν ρ law)
      (measurable_pi_apply 0).aemeasurable measurable_id.aestronglyMeasurable
    rw [trajectory_initial_law] at he
    exact he.symm
  | succ n =>
    let μ := trajectory ν ρ law
    have hm : Measurable (fun Y : ℕ → ℝ => (Preorder.frestrictLe n Y, Y (n+1))) := by fun_prop
    have hi : Integrable (fun p : ((i : Finset.Iic n) → ℝ) × ℝ => p.2)
        (μ.map (Preorder.frestrictLe n) ⊗ₘ stepKernel ν ρ law n) := by
      rw [trajectory_prefix_compProd]
      apply (integrable_map_measure measurable_snd.aestronglyMeasurable hm.aemeasurable).mpr
      exact integrable_trajectory_reward ν ρ law hbound (n+1)
    have hg : Measurable (fun h : (i : Finset.Iic n) → ℝ =>
        nodeMean law (action ν ρ (prefixExtension n h) (n+1))) :=
      (measurable_of_countable (nodeMean law)).comp
        ((measurable_action ν ρ (n+1)).comp (measurable_prefixExtension n))
    calc
      _ = ∫ p, p.2 ∂μ.map (Preorder.frestrictLe n) ⊗ₘ stepKernel ν ρ law n := by
        rw [trajectory_prefix_compProd, integral_map hm.aemeasurable measurable_snd.aestronglyMeasurable]
      _ = ∫ h, nodeMean law (action ν ρ (prefixExtension n h) (n+1)) ∂μ.map (Preorder.frestrictLe n) := by
        rw [Measure.integral_compProd hi]
        rfl
      _ = _ := by
        rw [integral_map (Preorder.measurable_frestrictLe n).aemeasurable hg.aestronglyMeasurable]
        simp only [action_prefixExtension]
        rfl

/-- Source model version of the one-round expectation identity. -/
theorem Covering.integral_actual_reward {X : Type*} [MeasurableSpace X]
    (C : Covering X) (law : Kernel X ℝ) [IsMarkovKernel law] (ν ρ : ℝ)
    (f : X → ℝ) (hmean : ∀x, (∫ y, y ∂law x)=f x)
    (hbound : ∀x, ∀ᵐ y ∂law x, y ∈ Set.Icc (0:ℝ) 1) (n : ℕ) :
    (∫ Y, Y n ∂trajectory ν ρ (C.nodeLaw law)) =
      ∫ Y, f (C.arm ν ρ Y n) ∂trajectory ν ρ (C.nodeLaw law) := by
  have he := integral_trajectory_reward ν ρ (C.nodeLaw law)
    (fun v => hbound (C.representative v)) n
  simpa only [nodeMean, Covering.nodeLaw, Kernel.comap_apply, hmean, Covering.arm] using he

/-- Expected cumulative realized regret and pseudo-regret coincide at every
horizon for one fixed policy and compatible infinite reward trajectory. -/
theorem RegularCovering.expected_actual_eq_pseudoRegret {X : Type*} [MeasurableSpace X]
    (C : RegularCovering X) (law : Kernel X ℝ) [IsMarkovKernel law]
    (f : X → ℝ) (best : ℝ) (hmean : ∀x, (∫ y, y ∂law x)=f x)
    (hfrange : ∀x, f x ∈ Set.Icc (0:ℝ) 1)
    (hbound : ∀x, ∀ᵐ y ∂law x, y ∈ Set.Icc (0:ℝ) 1) (N : ℕ) :
    (∫ Y, (∑ n ∈ Finset.range N, (best-Y n))
      ∂trajectory C.nu1 C.rho (C.toCovering.nodeLaw law)) =
    (∫ Y, (∑ n ∈ Finset.range N, (best-f (C.toCovering.arm C.nu1 C.rho Y n)))
      ∂trajectory C.nu1 C.rho (C.toCovering.nodeLaw law)) := by
  let μ := trajectory C.nu1 C.rho (C.toCovering.nodeLaw law)
  have hY (n : ℕ) : Integrable (fun Y => Y n) μ :=
    integrable_trajectory_reward C.nu1 C.rho (C.toCovering.nodeLaw law)
      (fun v => hbound (C.toCovering.representative v)) n
  have hgap (n : ℕ) := C.integrable_actual_gap f best hfrange μ n
  have hmeanI (n : ℕ) : Integrable (fun Y => f (C.toCovering.arm C.nu1 C.rho Y n)) μ := by
    have he : Integrable (fun Y => best-(best-f (C.toCovering.arm C.nu1 C.rho Y n))) μ :=
      (integrable_const best).sub (hgap n)
    simpa only [sub_sub_cancel] using he
  have hactual (n : ℕ) : Integrable (fun Y => best-Y n) μ :=
    (integrable_const best).sub (hY n)
  change (∫ Y, (∑ n ∈ Finset.range N, (best-Y n)) ∂μ) =
    (∫ Y, (∑ n ∈ Finset.range N, (best-f (C.toCovering.arm C.nu1 C.rho Y n))) ∂μ)
  rw [integral_finset_sum _ (fun n _ => hactual n),
    integral_finset_sum _ (fun n _ => hgap n)]
  apply Finset.sum_congr rfl
  intro n hn
  rw [integral_sub (integrable_const best) (hY n), integral_sub (integrable_const best) (hmeanI n),
    C.toCovering.integral_actual_reward law C.nu1 C.rho f hmean hbound n]


/-- The same repaired source rate for expected realized cumulative regret. -/
theorem RegularCovering.expected_actualRegret_rate {X : Type*} [MeasurableSpace X]
    (C : RegularCovering X) (law : Kernel X ℝ) [IsMarkovKernel law]
    (f : X → ℝ) (best d : ℝ) (hmean : ∀x, (∫ y, y ∂law x)=f x)
    (hf : ∀x, f x≤best) (hfrange : ∀x, f x ∈ Set.Icc (0:ℝ) 1)
    (hbest : regionSup f Set.univ=best) (hw : WeaklyLipschitz f C.ell best)
    (hbound : ∀x, ∀ᵐ y ∂law x, y ∈ Set.Icc (0:ℝ) 1)
    (hd : C.nearOptimalityDimension f best (4*C.nu1/C.nu2) < (d:EReal)) :
    ∃ γ : ℝ, 0<γ ∧ ∀ N : ℕ, 1≤N →
      (∫ Y, (∑ n ∈ Finset.range N, (best-Y n))
        ∂trajectory C.nu1 C.rho (C.toCovering.nodeLaw law)) ≤
      γ*(N:ℝ)^((d+1)/(d+2))*(Real.log (max (N:ℝ) 2))^(1/(d+2)) := by
  obtain ⟨γ, hγ, hrate⟩ := C.expected_pseudoRegret_rate law f best d hmean hf hfrange hbest hw hbound hd
  refine ⟨γ, hγ, fun N hN => ?_⟩
  rw [C.expected_actual_eq_pseudoRegret law f best hmean hfrange hbound N]
  exact hrate N hN

end BanditRLProof.HOO

