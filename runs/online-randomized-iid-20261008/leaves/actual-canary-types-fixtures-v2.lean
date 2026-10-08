import Tests.OnlineGuessingRandomizedIIDCanary

noncomputable section
open MeasureTheory ProbabilityTheory BanditRL.OnlineLearning
open Tests.OnlineGuessingIIDBenchmark Tests.OnlineGuessingRandomizedIID
open scoped ENNReal

namespace ExactSeedCanary
def propositionOf {P : Prop} (_ : P) : Prop := P
local instance : MeasurableSpace (Fin 4) :=
  Tests.OnlineGuessingRandomizedIID.instMeasurableSpaceFinOfNatNat_tests
local instance : MeasurableSingletonClass (Fin 4) :=
  Tests.OnlineGuessingRandomizedIID.instMeasurableSingletonClassFinOfNatNat_tests

def C001 : Prop := Measurable seed
example : C001 = propositionOf (@Tests.OnlineGuessingRandomizedIID.seed_measurable) := rfl

def C002 : Prop := ∀ (t : ℕ),
Measurable (target t)
example : C002 = propositionOf (@Tests.OnlineGuessingRandomizedIID.target_measurable) := rfl

def C003 : Prop := IdentDistrib seed (fun x : ℝ => x) seededLaw coinLaw
example : C003 = propositionOf (@Tests.OnlineGuessingRandomizedIID.seed_has_coinLaw) := rfl

def C004 : Prop := ∀ (t : ℕ),
IdentDistrib (target t) (fun x : ℝ => x) seededLaw coinLaw
example : C004 = propositionOf (@Tests.OnlineGuessingRandomizedIID.target_has_coinLaw) := rfl

def C005 : Prop := ∀ (t : ℕ),
IdentDistrib (target t) (target 0) seededLaw seededLaw
example : C005 = propositionOf (@Tests.OnlineGuessingRandomizedIID.target_sameLaw) := rfl

def C006 : Prop := ∀ (t : ℕ),
∀ᵐ ω ∂seededLaw, target t ω ∈ Set.Icc (0 : ℝ) 1
example : C006 = propositionOf (@Tests.OnlineGuessingRandomizedIID.target_support) := rfl

def C007 : Prop := iIndepFun target seededLaw
example : C007 = propositionOf (@Tests.OnlineGuessingRandomizedIID.target_independent) := rfl

def C008 : Prop := IndepFun seed (fun ω t => target t ω) seededLaw
example : C008 = propositionOf (@Tests.OnlineGuessingRandomizedIID.seed_independent_whole_process) := rfl

def C009 : Prop := ∀ (t : ℕ),
(∫ ω, target t ω ∂seededLaw) = 1 / 2
example : C009 = propositionOf (@Tests.OnlineGuessingRandomizedIID.target_mean) := rfl

def C010 : Prop := ∀ (t : ℕ),
variance (target t) seededLaw = 1 / 4
example : C010 = propositionOf (@Tests.OnlineGuessingRandomizedIID.target_variance) := rfl

def C011 : Prop := Measurable seedBit
example : C011 = propositionOf (@Tests.OnlineGuessingRandomizedIID.seedBit_measurable) := rfl

def C012 : Prop := ∀ (s : ℝ),
seedBit s ∈ Set.Icc (0 : ℝ) 1
example : C012 = propositionOf (@Tests.OnlineGuessingRandomizedIID.seedBit_feasible) := rfl

def C013 : Prop := ∀ (t : ℕ),
Measurable (seededPolicy t)
example : C013 = propositionOf (@Tests.OnlineGuessingRandomizedIID.seededPolicy_measurable) := rfl

def C014 : Prop := ∀ (t : ℕ) (s : ℝ) (z : (↑(Finset.range t) : Type) → ℝ)
    (hz : ∀ i, z i ∈ Set.Icc (0 : ℝ) 1),
seededPolicy t (s, z) ∈ Set.Icc (0 : ℝ) 1
example : C014 = propositionOf (@Tests.OnlineGuessingRandomizedIID.seededPolicy_legal) := rfl

def C015 : Prop := ¬ (∀ t s z, seededPolicy t (s, z) ∈ Set.Icc (0 : ℝ) 1)
example : C015 = propositionOf (@Tests.OnlineGuessingRandomizedIID.policy_not_off_cube_bounded) := rfl

def C016 : Prop := Monotone (privateSeedPastInformation seed target)
example : C016 = propositionOf (@Tests.OnlineGuessingRandomizedIID.actual_information_monotone) := rfl

def C017 : Prop := ∀ (t : ℕ),
IndepFun (fun ω => (seed ω, fun i : (↑(Finset.range t) : Type) => target i ω))
      (target t) seededLaw
example : C017 = propositionOf (@Tests.OnlineGuessingRandomizedIID.actual_seed_history_independent) := rfl

def C018 : Prop := ∀ (t : ℕ),
IndepFun (fun ω => seededPolicy t (seed ω, fun i => target i ω)) (target t) seededLaw
example : C018 = propositionOf (@Tests.OnlineGuessingRandomizedIID.actual_policy_current_independent) := rfl

def C019 : Prop := ∀ (T : ℕ),
0 ≤ expectedFixedRegret seededLaw target
      (fun t ω => seededPolicy t (seed ω, fun i => target i ω)) T
example : C019 = propositionOf (@Tests.OnlineGuessingRandomizedIID.actual_randomized_excess_nonnegative) := rfl

def C020 : Prop := ∀ (T : ℕ),
0 ≤ expectedFixedRegret seededLaw target
      (fun t ω => seededPolicy t (seed ω, fun i => target i ω)) T
example : C020 = propositionOf (@Tests.OnlineGuessingRandomizedIID.actual_general_information_excess_nonnegative) := rfl

def C021 : Prop := expectedFixedRegret seededLaw target
      (fun t ω => seededPolicy t (seed ω, fun i => target i ω)) 0 = 0
example : C021 = propositionOf (@Tests.OnlineGuessingRandomizedIID.actual_empty_excess) := rfl

def C022 : Prop := expectedFixedRegret seededLaw target
      (fun t ω => seededPolicy t (seed ω, fun i => target i ω)) 2 = 1 / 2
example : C022 = propositionOf (@Tests.OnlineGuessingRandomizedIID.actual_two_round_excess) := rfl

def C023 : Prop := ¬ Measurable[privateSeedPastInformation seed target 0] (target 0)
example : C023 = propositionOf (@Tests.OnlineGuessingRandomizedIID.current_target_not_private_information) := rfl

def C024 : Prop := IndepFun xorX xorY fourLaw
example : C024 = propositionOf (@Tests.OnlineGuessingRandomizedIID.xor_targets_independent) := rfl

def C025 : Prop := IndepFun xorTape xorX fourLaw
example : C025 = propositionOf (@Tests.OnlineGuessingRandomizedIID.xor_tape_individually_independent_X) := rfl

def C026 : Prop := IndepFun xorTape xorY fourLaw
example : C026 = propositionOf (@Tests.OnlineGuessingRandomizedIID.xor_tape_individually_independent_Y) := rfl

def C027 : Prop := ¬ IndepFun (fun q => (xorTape q, xorX q)) xorY fourLaw
example : C027 = propositionOf (@Tests.OnlineGuessingRandomizedIID.xor_seed_past_not_independent_current) := rfl

def C028 : Prop := ¬ IndepFun xorTape (fun q => (xorX q, xorY q)) fourLaw
example : C028 = propositionOf (@Tests.OnlineGuessingRandomizedIID.xor_seed_not_independent_whole_pair) := rfl

def C029 : Prop := IndepFun xorX xorY fourLaw ∧ IndepFun xorTape xorX fourLaw ∧
      IndepFun xorTape xorY fourLaw ∧
      ¬ IndepFun (fun q => (xorTape q, xorX q)) xorY fourLaw
example : C029 = propositionOf (@Tests.OnlineGuessingRandomizedIID.pairwise_seed_independence_is_insufficient) := rfl

def seededLawFixture : Measure (ℝ × (ℕ → ℝ)) := coinLaw.prod iidLaw
example : @seededLawFixture = @Tests.OnlineGuessingRandomizedIID.seededLaw := rfl

def seedFixture (ω : ℝ × (ℕ → ℝ)) : ℝ := ω.1
def target (t : ℕ) (ω : ℝ × (ℕ → ℝ)) : ℝ := ω.2 t
example : @seedFixture = @Tests.OnlineGuessingRandomizedIID.seed := rfl

def targetFixture (t : ℕ) (ω : ℝ × (ℕ → ℝ)) : ℝ := ω.2 t
example : @targetFixture = @Tests.OnlineGuessingRandomizedIID.target := rfl

def seedBitFixture (s : ℝ) : ℝ := if s ≤ 1 / 2 then 0 else 1
example : @seedBitFixture = @Tests.OnlineGuessingRandomizedIID.seedBit := rfl

def seededPolicyFixture (t : ℕ) (q : ℝ × ((↑(Finset.range t) : Type) → ℝ)) : ℝ :=
  if t = 0 then seedBit q.1 else lastPolicy t q.2
example : @seededPolicyFixture = @Tests.OnlineGuessingRandomizedIID.seededPolicy := rfl

def fourLawFixture : Measure (Fin 4) :=
  (1 / 4 : ℝ≥0∞) • Measure.dirac 0 + (1 / 4 : ℝ≥0∞) • Measure.dirac 1 +
    (1 / 4 : ℝ≥0∞) • Measure.dirac 2 + (1 / 4 : ℝ≥0∞) • Measure.dirac 3
example : @fourLawFixture = @Tests.OnlineGuessingRandomizedIID.fourLaw := rfl

def xorXFixture (q : Fin 4) : ℝ := if q.val < 2 then 0 else 1
def xorY (q : Fin 4) : ℝ := if q.val % 2 = 0 then 0 else 1
def xorTape (q : Fin 4) : ℝ := if xorX q = xorY q then 0 else 1
example : @xorXFixture = @Tests.OnlineGuessingRandomizedIID.xorX := rfl

def xorYFixture (q : Fin 4) : ℝ := if q.val % 2 = 0 then 0 else 1
def xorTape (q : Fin 4) : ℝ := if xorX q = xorY q then 0 else 1
example : @xorYFixture = @Tests.OnlineGuessingRandomizedIID.xorY := rfl

def xorTapeFixture (q : Fin 4) : ℝ := if xorX q = xorY q then 0 else 1
example : @xorTapeFixture = @Tests.OnlineGuessingRandomizedIID.xorTape := rfl

example : propositionOf (@seededLaw_probability) = IsProbabilityMeasure seededLaw := rfl
example : propositionOf (@fourLaw_probability) = IsProbabilityMeasure fourLaw := rfl
example : @Tests.OnlineGuessingRandomizedIID.instMeasurableSpaceFinOfNatNat_tests = (⊤ : MeasurableSpace (Fin 4)) := rfl
example : propositionOf (@Tests.OnlineGuessingRandomizedIID.instMeasurableSingletonClassFinOfNatNat_tests) = @MeasurableSingletonClass (Fin 4) (⊤ : MeasurableSpace (Fin 4)) := rfl
end ExactSeedCanary
