# HOO with arbitrary reward families

The independent HOO round trip found that the original terminal API required a
Markov kernel on the entire arm space, while the paper's Section2 specifies
an arm-indexed family of reward laws and a measurable mean. The production adapter
`BanditRLProof/Algorithms/HOORewardFamily.lean` removes that extra kernel
premise in the shared library. The reviewed prototype remains as an immutable checkpoint.

For every arm x, supply a probability measure M_x on real rewards, supported
on [0,1] and with mean f(x). There is no measurability premise on x -> M_x.
The theorem also does not need global measurability of f: its use along the
countable representative range is measurable, so the source measurable-mean
case is included. Original region measurability remains in RegularCovering.
For the actual covering's fixed representative a_v of each binary-word node v,
define the node kernel Q(v)=M_(a_v). Binary words form a countable measurable
space, so this is a measurable Markov kernel for an arbitrary reward family.
The unchanged causal search consumes the actual sequence of rewards, and the
unchanged trajectory construction uses this Q at the selected node.

To reuse the complete existing proof, the adapter equips X internally with
the full sigma algebra. This changes no set, arm, region, representative,
dissimilarity, mean, packing number or near-optimality dimension. All regions
and the reward-family map are measurable on this auxiliary domain. Applying
the existing theorem and reducing definitions yields the original action
function and the node kernel Q in the conclusion. The auxiliary measurable
space does not appear in the returned trajectory law. Lean checks this
transport definitionally; it is not a supplied equality or new probability
oracle. For an existing global kernel, `familyNodeLaw_eq_nodeLaw` is proved by
reflexivity, so the adapter recovers exactly the original trajectory.

The three new endpoints give (i) the complete expected pseudo-regret rate,
(ii) equality of actual and pseudo-regret expectations at every horizon, and
(iii) the complete actual-regret rate. Each rate chooses one positive gamma
before every N>=1 and retains every real exponent above the actual dimension,
the same log(max(N,2)), the same source-permitted fixed choices, and the
already explicit source repairs. No global-law measurability, confidence,
count, final rate or attained-maximizer premise is introduced.

## Source statement and explicit differences

Source: Bubeck, Munos, Stoltz and Szepesvari, *X-Armed Bandits*, JMLR12(2011),
Section2, Algorithm1, A1/A2, Definitions4-5 and Theorem6 / AppendixA.1.
[Published source](https://jmlr.org/papers/volume12/bubeck11a/bubeck11a.pdf).
Frozen SHA256: dcbbc42ae1ddc5a21153594a542d593d85b4f18913d9776a16221e2e31be68ef.

Under A1/A2 and bounded stationary rewards, the source rate is: for every real d strictly above the actual near-optimality
dimension, one environment-dependent gamma>0 bounds expected regret for every
positive horizon N by gamma N^((d+1)/(d+2)) log(N)^(1/(d+2)). The repaired
statement uses log(max(N,2)), including N=1, throughout the algorithm and bound.
It corrects root-child initialization and chronological indices, makes
log(0)=-infinity explicit in the dimension, and fixes source-permitted
representatives and left ties. It retains general asymmetric dissimilarity,
whole contained-ball packing, unachieved suprema and no compactness or metric
triangle inequality. Region measurability remains; global reward-family and
mean measurability are unnecessary along the countable representative range.

The inherited proof obtains adaptive conditional concentration from the actual
trajectory, bounds poor-node visits, derives packing growth from the actual
limsup dimension, partitions actual regret into three disjoint tree classes,
and optimizes an integer depth. No concentration/count/regret premise is
supplied to the terminal theorem. Equality of expected actual and pseudo-regret
uses the genuine first and subsequent reward laws and bounded integrability.

## Reuse and executable witness

The three actual parents are RegularCovering.expected_pseudoRegret_rate,
RegularCovering.expected_actual_eq_pseudoRegret and
RegularCovering.expected_actualRegret_rate. The adapter uses the existing
Covering, representative, arm and trajectory without duplicating their proofs.
Mathlib's measurable_of_countable, measurable_from_top and Markov-kernel
interfaces supply the probability construction. The full original HOO chain
has separate compiled-reference evidence and independent semantic review.

Tests/HOORewardFamilyCanary.lean imports the public root and applies the new
family terminal theorem to the infinite binary-arm model with distinct means
and non-Dirac rewards. Its dimension<=2 certificate is proved, so d=3 gives
N^(4/5) log(max(N,2))^(1/5) without an assumed dimension or rate. Another typed
consumer accepts an arbitrary family with given means and bounded support;
it imposes no global family measurability. No exact dimension or sharp-model
rate is claimed, and no concrete nonmeasurable-family example is claimed.

Independent acceptance of the original chain and prototype does not by itself
certify a production build. Production review and validation are separately
bound in the HOO production receipts. This is a source-repaired full endpoint,
not literal reproduction of every printed formula, acceptance of recent
comparison papers, an efficiency experiment, or whole-topic completion.

## Exact Lean statements and proofs

<details><summary>Shared reward-family module</summary>

```lean
import BanditRLProof.Algorithms.HOOActualRegret

/-! Arbitrary reward-family interface for the source-repaired HOO rate.
Only the countable representative-node law must be measurable. The internal
discrete-domain transport preserves the actual action and trajectory. -/
namespace BanditRLProof.HOO
open MeasureTheory ProbabilityTheory
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable def Covering.familyNodeLaw {X : Type*} (C : Covering X)
    (law : X → Measure ℝ) : Kernel Node ℝ where
  toFun v := law (C.representative v)
  measurable' := measurable_of_countable _

instance Covering.familyNodeLaw_markov {X : Type*} (C : Covering X)
    (law : X → Measure ℝ) [∀ x, IsProbabilityMeasure (law x)] :
    IsMarkovKernel (C.familyNodeLaw law) where
  isProbabilityMeasure v := inferInstanceAs (IsProbabilityMeasure (law (C.representative v)))

theorem Covering.familyNodeLaw_apply {X : Type*} (C : Covering X)
    (law : X → Measure ℝ) (v : Node) :
    C.familyNodeLaw law v = law (C.representative v) := rfl

theorem Covering.familyNodeLaw_eq_nodeLaw {X : Type*} [MeasurableSpace X]
    (C : Covering X) (law : Kernel X ℝ) :
    C.familyNodeLaw (fun x => law x) = C.nodeLaw law := rfl

noncomputable def RegularCovering.discrete {X : Type*} [MeasurableSpace X]
    (C : RegularCovering X) : @RegularCovering X ⊤ :=
  @RegularCovering.mk X ⊤ C.toCovering (fun _ => trivial)
    C.ell C.ell_nonneg C.ell_self C.nu1 C.nu2 C.rho C.nu1_pos C.nu2_pos
    C.rho_pos C.rho_lt_one C.diameter_bound C.center C.center_mem
    C.ball_subset C.balls_disjoint

noncomputable def familyDiscreteKernel {X : Type*} (law : X → Measure ℝ) :
    @Kernel X ℝ ⊤ (inferInstance : MeasurableSpace ℝ) := by
  letI : MeasurableSpace X := ⊤
  exact { toFun := law, measurable' := measurable_from_top }

instance familyDiscreteKernel_markov {X : Type*} (law : X → Measure ℝ)
    [∀ x, IsProbabilityMeasure (law x)] : IsMarkovKernel (familyDiscreteKernel law) where
  isProbabilityMeasure x := inferInstanceAs (IsProbabilityMeasure (law x))

theorem RegularCovering.expected_pseudoRegret_rate_family {X : Type*} [MeasurableSpace X]
    (C : RegularCovering X) (law : X → Measure ℝ) [∀ x, IsProbabilityMeasure (law x)]
    (f : X → ℝ) (best d : ℝ) (hmean : ∀ x, (∫ y, y ∂law x)=f x)
    (hf : ∀ x, f x≤best) (hfrange : ∀ x, f x ∈ Set.Icc (0:ℝ) 1)
    (hbest : regionSup f Set.univ=best) (hw : WeaklyLipschitz f C.ell best)
    (hbound : ∀ x, ∀ᵐ y ∂law x, y ∈ Set.Icc (0:ℝ) 1)
    (hd : C.nearOptimalityDimension f best (4*C.nu1/C.nu2) < (d:EReal)) :
    ∃ γ : ℝ, 0<γ ∧ ∀ N : ℕ, 1≤N →
      (∫ Y, (∑ n ∈ Finset.range N, (best-f (C.toCovering.arm C.nu1 C.rho Y n)))
        ∂trajectory C.nu1 C.rho (C.toCovering.familyNodeLaw law)) ≤
      γ*(N:ℝ)^((d+1)/(d+2))*(Real.log (max (N:ℝ) 2))^(1/(d+2)) := by
  exact @RegularCovering.expected_pseudoRegret_rate X ⊤ C.discrete (familyDiscreteKernel law) inferInstance f best d
    hmean hf hfrange hbest hw hbound hd

theorem RegularCovering.expected_actual_eq_pseudoRegret_family {X : Type*} [MeasurableSpace X]
    (C : RegularCovering X) (law : X → Measure ℝ) [∀ x, IsProbabilityMeasure (law x)]
    (f : X → ℝ) (best : ℝ) (hmean : ∀ x, (∫ y, y ∂law x)=f x)
    (hfrange : ∀ x, f x ∈ Set.Icc (0:ℝ) 1)
    (hbound : ∀ x, ∀ᵐ y ∂law x, y ∈ Set.Icc (0:ℝ) 1) (N : ℕ) :
    (∫ Y, (∑ n ∈ Finset.range N, (best-Y n))
      ∂trajectory C.nu1 C.rho (C.toCovering.familyNodeLaw law)) =
    (∫ Y, (∑ n ∈ Finset.range N, (best-f (C.toCovering.arm C.nu1 C.rho Y n)))
      ∂trajectory C.nu1 C.rho (C.toCovering.familyNodeLaw law)) := by
  exact @RegularCovering.expected_actual_eq_pseudoRegret X ⊤ C.discrete (familyDiscreteKernel law) inferInstance f best
    hmean hfrange hbound N

theorem RegularCovering.expected_actualRegret_rate_family {X : Type*} [MeasurableSpace X]
    (C : RegularCovering X) (law : X → Measure ℝ) [∀ x, IsProbabilityMeasure (law x)]
    (f : X → ℝ) (best d : ℝ) (hmean : ∀ x, (∫ y, y ∂law x)=f x)
    (hf : ∀ x, f x≤best) (hfrange : ∀ x, f x ∈ Set.Icc (0:ℝ) 1)
    (hbest : regionSup f Set.univ=best) (hw : WeaklyLipschitz f C.ell best)
    (hbound : ∀ x, ∀ᵐ y ∂law x, y ∈ Set.Icc (0:ℝ) 1)
    (hd : C.nearOptimalityDimension f best (4*C.nu1/C.nu2) < (d:EReal)) :
    ∃ γ : ℝ, 0<γ ∧ ∀ N : ℕ, 1≤N →
      (∫ Y, (∑ n ∈ Finset.range N, (best-Y n))
        ∂trajectory C.nu1 C.rho (C.toCovering.familyNodeLaw law)) ≤
      γ*(N:ℝ)^((d+1)/(d+2))*(Real.log (max (N:ℝ) 2))^(1/(d+2)) := by
  exact @RegularCovering.expected_actualRegret_rate X ⊤ C.discrete (familyDiscreteKernel law) inferInstance f best d
    hmean hf hfrange hbest hw hbound hd

end BanditRLProof.HOO

```

</details>
