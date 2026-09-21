import BanditRLProof.Algorithms.CUCBHistory
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-! The actual CUCB trajectory first samples a feasible oracle action, then
its fresh triggered feedback. Neither concentration nor oracle success is
assumed by this construction; those properties must be derived separately. -/
namespace BanditRLProof.CUCB
open MeasureTheory ProbabilityTheory
set_option autoImplicit false

abbrev Round (A : Type*) (m : ℕ) := A × Feedback m
abbrev Input (m : ℕ) := Fin m → UnitOutcome

def emptyFeedback (m : ℕ) : Feedback m :=
  (fun _ => false, (fun _ => ⟨0, by norm_num⟩, 0))

def initialInput (m : ℕ) : Input m := fun _ => ⟨1, by norm_num⟩

theorem oracleInput_zero {m : ℕ} (Y : ℕ → Feedback m) :
    oracleInput Y 0 = initialInput m := by
  funext i
  apply Subtype.ext
  simp [oracleInput, upperIndex, observationCount, initialInput]

variable {A : Type*} [MeasurableSpace A] {m : ℕ}

instance cucbPath_standardBorel [StandardBorelSpace A] : StandardBorelSpace (ℕ → Round A m) :=
  @StandardBorelSpace.pi_countable ℕ inferInstance (fun _ => Round A m)
    (fun _ => inferInstance) (fun _ => inferInstance)

noncomputable def roundKernel (oracle : Kernel (Input m) A)
    (environment : Kernel A (Feedback m)) : Kernel (Input m) (Round A m) :=
  oracle ⊗ₖ environment.comap Prod.snd measurable_snd

instance roundKernel_markov (oracle : Kernel (Input m) A)
    (environment : Kernel A (Feedback m)) [IsMarkovKernel oracle] [IsMarkovKernel environment] :
    IsMarkovKernel (roundKernel oracle environment) := by
  unfold roundKernel
  infer_instance

/-- The oracle draw precedes environment feedback; the latter depends on
the realized action, not on an independently redrawn action. -/
theorem roundKernel_rectangle (oracle : Kernel (Input m) A)
    (environment : Kernel A (Feedback m)) [IsMarkovKernel oracle] [IsMarkovKernel environment]
    (v : Input m) (s : Set A) (t : Set (Feedback m))
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    roundKernel oracle environment v (s ×ˢ t) = ∫⁻ a in s, environment a t ∂oracle v := by
  simp only [roundKernel, Kernel.compProd_apply_prod hs ht, Kernel.comap_apply]

theorem roundKernel_action_law (oracle : Kernel (Input m) A)
    (environment : Kernel A (Feedback m)) [IsMarkovKernel oracle] [IsMarkovKernel environment]
    (v : Input m) : (roundKernel oracle environment v).map Prod.fst = oracle v := by
  ext s hs
  rw [Measure.map_apply measurable_fst hs]
  exact Kernel.compProd_preimage_fst hs oracle
    (environment.comap Prod.snd measurable_snd) v

def feedbackExtension (n : ℕ) (h : (i : Finset.Iic n) → Round A m) : ℕ → Feedback m :=
  fun t => if ht : t≤n then (h ⟨t, Finset.mem_Iic.mpr ht⟩).2 else emptyFeedback m

theorem measurable_feedbackExtension (n : ℕ) : Measurable
    (feedbackExtension (A:=A) (m:=m) n) := by
  apply measurable_pi_lambda
  intro t
  by_cases ht : t≤n
  · simp only [feedbackExtension, dif_pos ht]
    exact measurable_snd.comp (measurable_pi_apply _)
  · simp only [feedbackExtension, dif_neg ht]
    exact measurable_const

omit [MeasurableSpace A] in
theorem oracleInput_feedbackExtension (Y : ℕ → Round A m) (n : ℕ) :
    oracleInput (feedbackExtension n (Preorder.frestrictLe n Y)) (n+1) =
      oracleInput (fun t => (Y t).2) (n+1) := by
  apply oracleInput_causal
  intro t ht
  simp only [feedbackExtension, dif_pos (show t≤n by omega), Preorder.frestrictLe_apply]

noncomputable def cucbStepKernel (oracle : Kernel (Input m) A)
    (environment : Kernel A (Feedback m)) (n : ℕ) :
    Kernel ((i : Finset.Iic n) → Round A m) (Round A m) :=
  (roundKernel oracle environment).comap
    (fun h => oracleInput (feedbackExtension n h) (n+1))
    ((measurable_oracleInput (n+1)).comp (measurable_feedbackExtension n))

instance cucbStepKernel_markov (oracle : Kernel (Input m) A)
    (environment : Kernel A (Feedback m)) [IsMarkovKernel oracle] [IsMarkovKernel environment]
    (n : ℕ) : IsMarkovKernel (cucbStepKernel oracle environment n) := by
  unfold cucbStepKernel
  infer_instance

noncomputable def cucbTrajectory (oracle : Kernel (Input m) A)
    (environment : Kernel A (Feedback m)) [IsMarkovKernel oracle] [IsMarkovKernel environment] :
    Measure (ℕ → Round A m) :=
  Kernel.trajMeasure (roundKernel oracle environment (initialInput m))
    (cucbStepKernel oracle environment)

instance cucbTrajectory_probability (oracle : Kernel (Input m) A)
    (environment : Kernel A (Feedback m)) [IsMarkovKernel oracle] [IsMarkovKernel environment] :
    IsProbabilityMeasure (cucbTrajectory oracle environment) := by
  unfold cucbTrajectory
  infer_instance

theorem cucbStepKernel_apply_prefix (oracle : Kernel (Input m) A)
    (environment : Kernel A (Feedback m)) (Y : ℕ → Round A m) (n : ℕ) :
    cucbStepKernel oracle environment n (Preorder.frestrictLe n Y) =
      roundKernel oracle environment (oracleInput (fun t => (Y t).2) (n+1)) := by
  simp only [cucbStepKernel, Kernel.comap_apply, oracleInput_feedbackExtension]

theorem cucbTrajectory_prefix_compProd (oracle : Kernel (Input m) A)
    (environment : Kernel A (Feedback m)) [IsMarkovKernel oracle] [IsMarkovKernel environment]
    (n : ℕ) :
    (cucbTrajectory oracle environment).map (Preorder.frestrictLe n) ⊗ₘ
      cucbStepKernel oracle environment n =
    (cucbTrajectory oracle environment).map (fun Y => (Preorder.frestrictLe n Y, Y (n+1))) :=
  Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure

theorem cucbTrajectory_condDistrib [StandardBorelSpace A] [Nonempty A]
    (oracle : Kernel (Input m) A) (environment : Kernel A (Feedback m))
    [IsMarkovKernel oracle] [IsMarkovKernel environment] (n : ℕ) :
    condDistrib (fun Y : ℕ → Round A m => Y (n+1)) (Preorder.frestrictLe n)
      (cucbTrajectory oracle environment) =ᵐ[
        (cucbTrajectory oracle environment).map (Preorder.frestrictLe n)]
      cucbStepKernel oracle environment n :=
  Kernel.condDistrib_trajMeasure

theorem cucbTrajectory_initial_law (oracle : Kernel (Input m) A)
    (environment : Kernel A (Feedback m)) [IsMarkovKernel oracle] [IsMarkovKernel environment] :
    (cucbTrajectory oracle environment).map (fun Y => Y 0) =
      roundKernel oracle environment (initialInput m) := by
  have he : (fun Y : ℕ → Round A m => Y 0) =
      (fun h : (i : Finset.Iic 0) → Round A m => h ⟨0, by simp⟩) ∘ Preorder.frestrictLe 0 := rfl
  rw [he, ← Measure.map_map (by fun_prop) (by fun_prop), cucbTrajectory, Kernel.trajMeasure,
    Measure.map_comp _ _ (Preorder.measurable_frestrictLe 0),
    Kernel.traj_map_frestrictLe_of_le (le_refl 0), Measure.deterministic_comp_eq_map,
    Measure.map_map (by fun_prop) (Preorder.measurable_frestrictLe₂
      (X := fun _ : ℕ => Round A m) (le_refl 0)),
    Measure.map_map ((measurable_pi_apply _).comp
      (Preorder.measurable_frestrictLe₂ (X := fun _ : ℕ => Round A m) (le_refl 0)))
      (by fun_prop)]
  convert (Measure.map_id (μ := roundKernel oracle environment (initialInput m))) using 1

end BanditRLProof.CUCB
