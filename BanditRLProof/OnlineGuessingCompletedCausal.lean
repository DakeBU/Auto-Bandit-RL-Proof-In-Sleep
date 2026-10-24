import BanditRLProof.OnlineGuessingAECausal
import Mathlib.MeasureTheory.MeasurableSpace.EventuallyMeasurable
import Mathlib.MeasureTheory.Constructions.Polish.Basic

open MeasureTheory ProbabilityTheory Filter

universe u v
namespace BanditRL.OnlineLearning


/-! Derived ambient-null-augmentation real versions and causal IID adapters for Orabona v10 printed1/PDF13 and printed3/PDF15. This field is eventuallyMeasurableSpace F (ae ambient_mu), not an asserted completion of mu.trim F. Full causal kernels remain required. -/

theorem completed_measurable_real_exists_version {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (F : MeasurableSpace Ω) (P : Ω → ℝ)
    (hP : @Measurable _ _ (eventuallyMeasurableSpace F (ae μ)) _ P) :
    ∃ version : Ω → ℝ, Measurable[F] version ∧ P =ᶠ[ae μ] version := by
  classical
  rename_i mΩ
  letI : MeasurableSpace Ω := mΩ
  let code : ℝ → ℕ → Bool := MeasurableSpace.mapNatBool ℝ
  have hcode : Measurable code := MeasurableSpace.measurable_mapNatBool ℝ
  have hemb : MeasurableEmbedding code :=
    hcode.measurableEmbedding (MeasurableSpace.injective_mapNatBool ℝ)
  have hcoordinate (n : ℕ) :
      ∃ A : Set Ω, MeasurableSet[F] A ∧
        {ω | code (P ω) n = true} =ᶠ[ae μ] A := by
    have hm : @Measurable Ω Bool (eventuallyMeasurableSpace F (ae μ)) _
        (fun ω => code (P ω) n) :=
      (measurable_pi_apply n).comp (hcode.comp hP)
    exact hm (measurableSet_singleton true)
  choose A hA heq using hcoordinate
  let representative : Ω → ℕ → Bool := fun ω n => decide (ω ∈ A n)
  have hrepresentative : Measurable[F] representative := by
    letI : MeasurableSpace Ω := F
    apply measurable_pi_iff.2
    intro n
    apply measurable_to_bool
    simpa only [representative, Set.preimage, Set.mem_singleton_iff,
      Bool.decide_iff, Set.setOf_mem_eq] using hA n
  refine ⟨fun ω => hemb.invFun (representative ω),
    hemb.measurable_invFun.comp hrepresentative, ?_⟩
  filter_upwards [ae_all_iff.2 heq] with ω hω
  have hre : representative ω = code (P ω) := by
    funext n
    have hn := hω n
    change (code (P ω) n = true) = (ω ∈ A n) at hn
    dsimp [representative]
    rw [← hn]
    cases h : code (P ω) n <;> simp [h]
  rw [hre]
  exact (hemb.leftInverse_invFun (P ω)).symm

theorem completed_predictable_exists_bounded_history_policy {Ω : Type u} {Seed : Type v}
    [MeasurableSpace Ω] [MeasurableSpace Seed]
    (μ : Measure Ω) (Y : ℕ → Ω → ℝ) (S : Ω → Seed)
    (F : ℕ → MeasurableSpace Ω)
    (hF : ∀ t, F t ≤ privateSeedPastInformation S Y t)
    (prediction : ℕ → Ω → ℝ)
    (hP : ∀ t, @Measurable _ _ (eventuallyMeasurableSpace (F t) (ae μ)) _ (prediction t))
    (hpb : ∀ t, ∀ᵐ ω ∂μ, prediction t ω ∈ Set.Icc (0 : ℝ) 1) :
    ∃ policy : (t : ℕ) → (Seed × ((↑(Finset.range t) : Type) → ℝ)) → ℝ,
      (∀ t, Measurable (policy t)) ∧
      (∀ t q, policy t q ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ᵐ ω ∂μ, ∀ t, prediction t ω = policy t (S ω, fun i => Y i ω) := by
  rename_i mΩ mSeed
  letI : MeasurableSpace Ω := mΩ
  have hAE (t : ℕ) : AEStronglyMeasurable[F t] (prediction t) μ := by
    obtain ⟨version, hv, he⟩ :=
      completed_measurable_real_exists_version μ (F t) (prediction t) (hP t)
    exact hv.aestronglyMeasurable.congr he.symm
  exact ae_predictable_exists_bounded_history_policy μ Y S F hF prediction hAE hpb

theorem completed_predictable_private_seed_independent {Ω : Type u} {Seed : Type v}
    [MeasurableSpace Ω] [MeasurableSpace Seed]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hY : ∀ t, Measurable (Y t)) (hind : iIndepFun Y μ)
    (S : Ω → Seed) (hS : Measurable S)
    (hseed : IndepFun S (fun ω t => Y t ω) μ)
    (t : ℕ) (F : MeasurableSpace Ω) (hF : F ≤ privateSeedPastInformation S Y t)
    (P : Ω → ℝ)
    (hP : @Measurable _ _ (eventuallyMeasurableSpace F (ae μ)) _ P) :
    IndepFun P (Y t) μ := by
  rename_i mΩ mSeed hμ
  letI : MeasurableSpace Ω := mΩ
  obtain ⟨version, hv, he⟩ := completed_measurable_real_exists_version μ F P hP
  have hAE : AEStronglyMeasurable[F] P μ := hv.aestronglyMeasurable.congr he.symm
  exact ae_predictable_private_seed_independent μ Y hY hind S hS hseed t F hF P hAE

theorem completed_predictable_private_seed_expectedFixed_excess {Ω : Type u} {Seed : Type v}
    [MeasurableSpace Ω] [MeasurableSpace Seed]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ)
    (hY : ∀ t, Measurable (Y t))
    (hlaw : ∀ t, IdentDistrib (Y t) (Y 0) μ μ)
    (hb : ∀ t, ∀ᵐ ω ∂μ, Y t ω ∈ Set.Icc (0 : ℝ) 1)
    (hind : iIndepFun Y μ)
    (S : Ω → Seed) (hS : Measurable S)
    (hseed : IndepFun S (fun ω t => Y t ω) μ)
    (F : ℕ → MeasurableSpace Ω)
    (hF : ∀ t, F t ≤ privateSeedPastInformation S Y t)
    (prediction : ℕ → Ω → ℝ)
    (hP : ∀ t, @Measurable _ _ (eventuallyMeasurableSpace (F t) (ae μ)) _ (prediction t))
    (hpb : ∀ t, ∀ᵐ ω ∂μ, prediction t ω ∈ Set.Icc (0 : ℝ) 1) (T : ℕ) :
    expectedFixedRegret μ Y prediction T =
      (∑ t ∈ Finset.range T,
        ∫ ω, (prediction t ω - ∫ ω, Y 0 ω ∂μ)^2 ∂μ) ∧
      0 ≤ expectedFixedRegret μ Y prediction T := by
  rename_i mΩ mSeed hμ
  letI : MeasurableSpace Ω := mΩ
  have hAE (t : ℕ) : AEStronglyMeasurable[F t] (prediction t) μ := by
    obtain ⟨version, hv, he⟩ :=
      completed_measurable_real_exists_version μ (F t) (prediction t) (hP t)
    exact hv.aestronglyMeasurable.congr he.symm
  exact ae_predictable_private_seed_expectedFixed_excess μ Y hY hlaw hb hind S hS hseed
    F hF prediction hAE hpb T

end BanditRL.OnlineLearning
