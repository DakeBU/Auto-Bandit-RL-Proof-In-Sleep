import BanditRLProof.OnlineGuessingRandomizedIID
import Mathlib.Probability.Kernel.Representation
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Data.Fin.Tuple.Basic

open MeasureTheory ProbabilityTheory unitInterval

set_option pp.notation false
set_option pp.universes true

namespace BanditRL.OnlineLearning

/-- Actions already generated and observations strictly before the current round. -/
abbrev KernelDecisionHistory (t : ℕ) := (Fin t → I) × (Fin t → ℝ)

/-- One sampler at every natural time, fixed without an observation law or horizon. -/
abbrev KernelDecisionSampler := (t : ℕ) → KernelDecisionHistory t → I → I

/-- Real causal recursion: append the sampled action to the previously generated actions. -/
def kernelGeneratedActions (f : KernelDecisionSampler) :
    (t : ℕ) → (Fin t → I) → (Fin t → ℝ) → (Fin t → I)
  | 0, _, _ => Fin.elim0
  | t + 1, u, y =>
      let past := kernelGeneratedActions f t (fun i => u i.castSucc) (fun i => y i.castSucc)
      Fin.snoc past (f t (past, fun i => y i.castSucc) (u (Fin.last t)))

/-- Before-reveal policy; input observations have exactly the strict-past length. -/
def kernelCausalPolicy (f : KernelDecisionSampler) (t : ℕ)
    (q : (ℕ → I) × (Fin t → ℝ)) : I :=
  f t (kernelGeneratedActions f t (fun i => q.1 i) q.2, q.2) (q.1 t)

/-- Joint generated action history and strict-past observations on the common sample space. -/
def kernelGeneratedHistory (f : KernelDecisionSampler) (t : ℕ)
    (ω : (ℕ → I) × (ℕ → ℝ)) : KernelDecisionHistory t :=
  (kernelGeneratedActions f t (fun i => ω.1 i) (fun i => ω.2 i), fun i => ω.2 i)

/-- A single infinite prediction process, rather than a separate algorithm for each horizon. -/
def kernelGeneratedPrediction (f : KernelDecisionSampler) (t : ℕ)
    (ω : (ℕ → I) × (ℕ → ℝ)) : I :=
  kernelCausalPolicy f t (ω.1, fun i => ω.2 i)

/-- Independent fresh uniform draws form the private infinite tape. -/
noncomputable abbrev kernelUniformTapeLaw : Measure (ℕ → I) :=
  Measure.infinitePi (fun _ : ℕ => (volume : Measure I))

/-- Observation law may have arbitrary temporal dependence for the kernel realization. -/
noncomputable abbrev kernelGameLaw (ν : ProbabilityMeasure (ℕ → ℝ)) : Measure ((ℕ → I) × (ℕ → ℝ)) :=
  kernelUniformTapeLaw.prod (ν : Measure (ℕ → ℝ))


#check (∀ (κ : (t : ℕ) → Kernel (KernelDecisionHistory t) I) [∀ t, IsMarkovKernel (κ t)],
    ∃ f : KernelDecisionSampler,
      (∀ t, Measurable (Function.uncurry (f t))) ∧
      ∀ t h, (volume : Measure I).map (f t h) = κ t h)

#check (∀ (f : KernelDecisionSampler) (hf : ∀ t, Measurable (Function.uncurry (f t))),
    (∀ t, Measurable (kernelCausalPolicy f t)) ∧
    (∀ t (u : ℕ → I) (y : ℕ → ℝ) (i : Fin t),
      kernelGeneratedActions f t (fun j => u j) (fun j => y j) i =
        kernelGeneratedPrediction f (i : ℕ) (u, y)) ∧
    ∀ t (ω ω' : (ℕ → I) × (ℕ → ℝ)),
      (∀ i, i ≤ t → ω.1 i = ω'.1 i) →
      (∀ i, i < t → ω.2 i = ω'.2 i) →
      kernelGeneratedPrediction f t ω = kernelGeneratedPrediction f t ω')

#check (∀ (κ : (t : ℕ) → Kernel (KernelDecisionHistory t) I) [∀ t, IsMarkovKernel (κ t)]
    (f : KernelDecisionSampler) (hf : ∀ t, Measurable (Function.uncurry (f t)))
    (hκ : ∀ t h, (volume : Measure I).map (f t h) = κ t h)
    (ν : ProbabilityMeasure (ℕ → ℝ)) (t : ℕ),
    (kernelGameLaw ν).map (fun ω =>
      (kernelGeneratedHistory f t ω, kernelGeneratedPrediction f t ω)) =
      (kernelGameLaw ν).map (kernelGeneratedHistory f t) ⊗ₘ κ t)

#check (∀ (κ : (t : ℕ) → Kernel (KernelDecisionHistory t) I) [∀ t, IsMarkovKernel (κ t)]
    (f : KernelDecisionSampler) (hf : ∀ t, Measurable (Function.uncurry (f t)))
    (hκ : ∀ t h, (volume : Measure I).map (f t h) = κ t h)
    (ν : ProbabilityMeasure (ℕ → ℝ)) (t : ℕ),
    condDistrib (kernelGeneratedPrediction f t) (kernelGeneratedHistory f t) (kernelGameLaw ν)
      =ᵐ[(kernelGameLaw ν).map (kernelGeneratedHistory f t)] κ t)

#check (∀ (κ : (t : ℕ) → Kernel (KernelDecisionHistory t) I) [∀ t, IsMarkovKernel (κ t)],
    ∃ f : KernelDecisionSampler,
      (∀ t, Measurable (Function.uncurry (f t))) ∧
      (∀ t h, (volume : Measure I).map (f t h) = κ t h) ∧
      (∀ t, Measurable (kernelCausalPolicy f t)) ∧
      (∀ t (u : ℕ → I) (y : ℕ → ℝ) (i : Fin t),
        kernelGeneratedActions f t (fun j => u j) (fun j => y j) i =
          kernelGeneratedPrediction f (i : ℕ) (u, y)) ∧
      (∀ t (ω ω' : (ℕ → I) × (ℕ → ℝ)),
        (∀ i, i ≤ t → ω.1 i = ω'.1 i) →
        (∀ i, i < t → ω.2 i = ω'.2 i) →
        kernelGeneratedPrediction f t ω = kernelGeneratedPrediction f t ω') ∧
      ∀ ν : ProbabilityMeasure (ℕ → ℝ),
        (∀ t, (kernelGameLaw ν).map (fun ω =>
          (kernelGeneratedHistory f t ω, kernelGeneratedPrediction f t ω)) =
          (kernelGameLaw ν).map (kernelGeneratedHistory f t) ⊗ₘ κ t) ∧
        (∀ t, condDistrib (kernelGeneratedPrediction f t) (kernelGeneratedHistory f t)
          (kernelGameLaw ν) =ᵐ[(kernelGameLaw ν).map (kernelGeneratedHistory f t)] κ t) ∧
        (iIndepFun (fun t (y : ℕ → ℝ) => y t) (ν : Measure (ℕ → ℝ)) →
          (∀ t, IdentDistrib (fun y : ℕ → ℝ => y t) (fun y : ℕ → ℝ => y 0)
            (ν : Measure (ℕ → ℝ)) (ν : Measure (ℕ → ℝ))) →
          (∀ t, ∀ᵐ y ∂(ν : Measure (ℕ → ℝ)), y t ∈ Set.Icc (0 : ℝ) 1) →
          ∀ T : ℕ,
            expectedFixedRegret (kernelGameLaw ν) (fun t ω => ω.2 t)
              (fun t ω => (kernelGeneratedPrediction f t ω : ℝ)) T =
              (∑ t ∈ Finset.range T, ∫ ω,
                ((kernelGeneratedPrediction f t ω : ℝ) -
                  ∫ ω, ω.2 0 ∂(kernelGameLaw ν))^2 ∂(kernelGameLaw ν)) ∧
            0 ≤ expectedFixedRegret (kernelGameLaw ν) (fun t ω => ω.2 t)
              (fun t ω => (kernelGeneratedPrediction f t ω : ℝ)) T))

end BanditRL.OnlineLearning
