# CUCB: reviewed full triggered-feedback regret chain

Source: Chen, Wang, Yuan and Wang, *Combinatorial Multi-Armed Bandit and Its Extension to Probabilistically Triggered Arms*, JMLR 17(50), 2016, Section 2, Algorithm 1, Theorems 1-2 and complete Section 3.1 proofs, printed pp.7-25. [Published PDF](https://jmlr.org/papers/volume17/14-298/14-298.pdf). Frozen SHA-256: `6a29fc188cd1490c53864eb4f839e572551c171388fc27ba256a7e61424e856c`.

The accepted claim is the full frozen CUCB contract with explicit model and proof deltas. It includes general finite feasible subset families, nonlinear monotone smooth reward scores, an approximation oracle and probabilistic triggering. It is not a top-k or deterministic-trigger-only substitute. This review does not accept the source's application reductions, unrestricted censoring or every result in the paper.

## Model, algorithm and assumption boundary

A finite nonempty family of distinct selected subsets acts on m bounded base arms. Each action has a nonempty possible-trigger set; never-triggerable arms have been removed. Actual minimum triggering probabilities p_i are positive and derived from the environment. Selected arms are observed with probability one. The environment kernel produces the observation mask, base outcomes in [0,1] and a nonnegative integrable total reward. Total reward need not be uniformly bounded and may be nonlinear.

For each action a and arm i the model explicitly requires

$$
\Pr_a(i\text{ observed},X_i\in B)=p_i^a D_i(B).
$$

The observed marginal D_i is fixed across actions. This makes the source's observed-sample assumption precise; arbitrary censoring based on the current value is not included. Cross-arm independence is unnecessary. The score family r_v(a) matches the actual reward mean at the true vector, is coordinatewise monotone and satisfies the source bounded-smoothness inequality on all possible triggered coordinates. Its modulus f is continuous and strictly increasing on nonnegative reals, f(0)=0. Every positive gap up to the largest gap must lie in the range of f. That last condition is explicit and is not inferred from strict increase alone.

CUCB starts counts at zero and empirical means at one, with no forced exploration schedule. At prefix length n, an unobserved arm has index one; an observed arm has index min(empirical mean + sqrt(3 log(n+1)/(2 count)),1). A fixed measurable oracle kernel has pointwise alpha-approximation success probability at least beta, with alpha,beta in (0,1]. It draws the action before fresh environment feedback. The same causal infinite trajectory is used for every horizon. The learner observes neither true gaps nor analysis counters.

## Exact performance statements

Write OPT=max_a r_mu(a), d(a)=alpha OPT-r_mu(a), Delta=max_a max(0,d(a)), p*=min_i p_i, and

$$
R(H)=H\alpha\beta\,\mathrm{OPT}-\mathbb E\sum_{t<H}\mathrm{reward}_t.
$$

This signed expected approximation regret may be negative. For positive gap d put u=f^{-1}(d) and

$$
\ell_H(d,p)=\log H\begin{cases}6/u^2,&p=1,\\
\max\{12/(u^2p),24/p\},&0<p<1.\end{cases}
$$

For each arm i having positive-gap possible actions, let d_i,min and d_i,max be their minimum and maximum gaps. Its refined contribution Q_i is d_i,min ell_H(d_i,min,p_i) plus the integral of ell_H(x,p_i) from d_i,min to d_i,max. Set Q_i=0 for an empty family. Theorem 1's accepted endpoint is, for every natural H>=1,

$$
R(H)\le\sum_i Q_i+\left[1+\frac{(2+\mathbf1_{p_*<1})\pi^2}{6}\right]m\Delta.
$$

When f(u)=gamma u^omega for every u>=0, gamma>0 and 0<omega<=1, Theorem 2 gives

$$
p_*=1:\quad R(H)\le\frac{2\gamma}{2-\omega}(6m\log H)^{\omega/2}H^{1-\omega/2}
 +(1+\pi^2/3)m\Delta,
$$

and

$$
p_*<1:\quad R(H)\le\frac{2\gamma}{2-\omega}(12m\log H/p_*)^{\omega/2}H^{1-\omega/2}
 +(1+\pi^2/2)m\Delta+\sum_i\frac{24\log H}{p_i}\Delta.
$$

H=1 is handled separately before positive-log optimization. Zero horizon has its own reward identity, and no bad actions imply R(H)<=0 for every H. No confidence or visit-count bound is an endpoint assumption.

## Proof and explicit repairs

Observed-marginal compatibility and bounded Hoeffding control give an exponential factor for masked centered outcomes. Integrating first over feedback conditional on the action, then over the actual oracle mixture, and finally through the trajectory's conditional law gives adaptive count-compensated concentration. Slicing actual counts and using both signs yields nice-event failure at most 2m/t^2. Count zero is treated directly.

The source's mixed-trigger threshold identity fails across p=1 and p<1. For analysis only, write ell_H(d,p_i)=log(H)c_i and charge an arm minimizing N_i/c_i over the possible-trigger set. Since c_i>0, N_i>log(H)c_i for that minimizer implies the same inequality for every member. This choice depends on past counters and the current action before current feedback. The learner is unchanged.

If C_t indicates a charge to i and Z_t=C_t times its observation indicator, the actual conditional factor satisfies, for every $\lambda\ge0$,

$$
\mathbb E[\exp((1-e^{-\lambda})p_i C_t-\lambda Z_t)\mid\text{past}]\le1.
$$

The proof retains the current-action mixture; the charge is not assumed known before the randomized action draw. Exponential accumulation gives the derived bound

$$
\Pr(N_i(n)\ge k,\ T_i(n)\le kp_i/2)\le e^{-kp_i/8}.
$$

For deterministic triggering the relevant counter inequality holds almost surely. For other arms, fixed-count slices use a deterministic extremal eligible action to avoid an extra action-count factor. Union over count slices gives m/t^2. Optimistic indices, smoothness and successful oracle output rule out a sufficiently sampled bad action on the good events. The combined tail sums to (2+1{p*<1})m pi^2/6.

Distinct charge times have distinct old integer counts. Hence the number of under-sampled charges with gap at least x is at most ell_H(x,p_i)+1. The finite layer-cake identity yields Q_i+d_i,max for each arm, retaining the zero-counter cost. It avoids incorrectly bounding each floor difference by an interval length. Integrability and the actual reward law give

$$
R(H)=\mathbb E\sum_{t<H}d(A_t)-H\alpha(1-\beta)\mathrm{OPT}.
$$

The retained signed credit cancels the expected oracle-failure term, completing Theorem 1 with its exact residual. For Theorem 2, a single common gap cutoff pays H a once across all arms. Integrating the power envelope and optimizing a gives both displayed leading terms; the probabilistic branch retains its per-arm logarithmic residual. The proof does not condition concentration on realized terminal counters. A finite-concavity theorem for actual counts is separately proved to satisfy the frozen obligation, but is not a dependency of this cutoff proof.

## Actual consumers, reuse and remaining scope

The 64-atom example has three noisy Bernoulli arms, two distinct two-arm actions and product rewards with means 1/8 and 3/8. Minimum trigger probabilities are (1/2,1,1/2). Its input-dependent exact oracle gives actual first-round regret 1/4 and consumes the full refined and probabilistic endpoints. Full observation recovers the deterministic-trigger theorem while keeping noisy rewards. A supplementary uniform randomized oracle has beta=1/2 and intentionally ignores its input; it is not a learning-improvement example. An alpha=1/3 instance covers the no-bad boundary.

Actual shared mathematical parents include the fixed and conditional MGF interfaces, finite gap layer-cake/cutoff lemmas, power-tail integration and cutoff normalization. Mathlib supplies trajectory construction, conditional distributions, Hoeffding, interval integration, real powers and the inverse-square sum. The finite sample law and randomized oracle reuse Thompson.uniformActionMeasure, a finite uniform PMF measure; this does not claim completion of the Thompson topic or an efficiency effect. Canonical declaration links on the topic page are reading references, not a dependency graph.

Independent reconstruction, source comparison and repair review accept the frozen chain with the explicit differences above. The distinct-selected-subset model excludes the source's parameterized duplicate-subset extension. Recent CMOSS review, final publication validation, descriptive ICLR evidence and all-topic evaluation remain separate. No merge, deployment or whole-topic completion is claimed.

## Exact model and terminal Lean

The following folded modules are copied exactly from the reviewed source. Their imports preserve the shared project's definitions and proof chain; no alternate library is introduced.

<details>
<summary>BanditRLProof/Algorithms/CUCBFeedbackModel.lean</summary>

```lean
import BanditRLProof.Algorithms.CUCBDeterministicTrigger
import BanditRLProof.Algorithms.CUCBNiceEvent

/-! Finite feasible superarms and primitive triggered-feedback laws.
Trigger minima are computed from actual environment probabilities. -/
namespace BanditRLProof.CUCB
open MeasureTheory ProbabilityTheory
set_option autoImplicit false

structure FeedbackModel (A : Type*) [MeasurableSpace A] (m : ℕ) where
  selected : A → Finset (Fin m)
  selected_injective : Function.Injective selected
  possible : A → Finset (Fin m)
  possible_nonempty : ∀a, (possible a).Nonempty
  selected_subset : ∀a, selected a⊆possible a
  triggerable : ∀i, ∃a, i∈possible a
  environment : Kernel A (Feedback m)
  environment_markov : IsMarkovKernel environment
  laws : Fin m → Measure UnitOutcome
  laws_probability : ∀i, IsProbabilityMeasure (laws i)
  observation_compatible : ∀a i, ObservationCompatible (environment a) (laws i) i
  possible_iff_positive : ∀a i, i∈possible a ↔ 0<(environment a (observedSet i)).toReal
  selected_observed : ∀a i, i∈selected a → environment a (observedSet i)=1
  reward_nonneg : ∀a, ∀ᵐ z ∂environment a, 0≤z.2.2
  reward_integrable : ∀a, Integrable (fun z => z.2.2) (environment a)

namespace FeedbackModel
variable {A : Type*} [MeasurableSpace A] {m : ℕ} (M : FeedbackModel A m)

instance environment_isMarkov : IsMarkovKernel M.environment := M.environment_markov
instance law_isProbability (i : Fin m) : IsProbabilityMeasure (M.laws i) := M.laws_probability i

noncomputable def trueInput : Input m := fun i => ⟨marginalMean (M.laws i), marginalMean_mem _⟩
noncomputable def expectedReward (a : A) : ℝ := ∫z, z.2.2 ∂M.environment a
noncomputable def triggerProbability (a : A) (i : Fin m) : ℝ :=
  (M.environment a (observedSet i)).toReal

theorem expectedReward_nonneg (a : A) : 0≤M.expectedReward a :=
  integral_nonneg_of_ae (M.reward_nonneg a)

theorem triggerProbability_le_one (a : A) (i : Fin m) : M.triggerProbability a i≤1 :=
  measureReal_le_one

theorem triggerProbability_pos (a : A) (i : Fin m) (hi : i∈M.possible a) :
    0<M.triggerProbability a i := (M.possible_iff_positive a i).1 hi

variable [Fintype A]

noncomputable def triggerActions (i : Fin m) : Finset A :=
  Finset.univ.filter (fun a => i∈M.possible a)

theorem mem_triggerActions (a : A) (i : Fin m) : a∈M.triggerActions i ↔ i∈M.possible a := by
  classical
  simp [triggerActions]

theorem triggerActions_nonempty (i : Fin m) : (M.triggerActions i).Nonempty := by
  obtain ⟨a, ha⟩ := M.triggerable i
  exact ⟨a, (M.mem_triggerActions a i).2 ha⟩

noncomputable def minTrigger (i : Fin m) : ℝ :=
  (M.triggerActions i).inf' (M.triggerActions_nonempty i) (fun a => M.triggerProbability a i)

theorem minTrigger_pos (i : Fin m) : 0<M.minTrigger i := by
  apply (Finset.lt_inf'_iff (M.triggerActions_nonempty i)).mpr
  intro a ha
  exact M.triggerProbability_pos a i ((M.mem_triggerActions a i).1 ha)

theorem minTrigger_le (a : A) (i : Fin m) (hi : i∈M.possible a) :
    M.minTrigger i≤M.triggerProbability a i :=
  Finset.inf'_le _ ((M.mem_triggerActions a i).2 hi)

theorem minTrigger_le_one (i : Fin m) : M.minTrigger i≤1 := by
  obtain ⟨a, ha⟩ := M.triggerable i
  exact (M.minTrigger_le a i ha).trans (M.triggerProbability_le_one a i)

/-- Source gaps will supply the two analysis fields; the trigger lower bound
is already fixed to the actual environment minimum, with its proof below. -/
noncomputable def chargeData (bad : A → Bool) (inverseGap : A → ℝ) : ChargeData A m where
  bad := bad
  triggers := M.possible
  nonempty := M.possible_nonempty
  inverseGap := inverseGap
  triggerLower := M.minTrigger

theorem chargeData_trigger_bound (bad : A → Bool) (inverseGap : A → ℝ) (i : Fin m) :
    ∀a, i∈(M.chargeData bad inverseGap).triggers a →
      (M.chargeData bad inverseGap).triggerLower i≤(M.environment a (observedSet i)).toReal :=
  fun a ha => M.minTrigger_le a i ha

variable [MeasurableSingletonClass A]

theorem deterministic_counter_bound (oracle : Kernel (Input m) A) [IsMarkovKernel oracle]
    (bad : A → Bool) (inverseGap : A → ℝ) (i : Fin m) (hp : M.minTrigger i=1) :
    ∀ᵐ Y ∂cucbTrajectory oracle M.environment, ∀n,
      (M.chargeData bad inverseGap).counters (fun t => (Y t).1) n i≤
        observationCount (fun t => (Y t).2) n i :=
  (M.chargeData bad inverseGap).counters_le_observations_ae_of_one oracle M.environment i
    (M.chargeData_trigger_bound bad inverseGap i) hp

variable [StandardBorelSpace A] [Nonempty A]

theorem charged_observation_tail (oracle : Kernel (Input m) A) [IsMarkovKernel oracle]
    (bad : A → Bool) (inverseGap : A → ℝ) (i : Fin m) (n : ℕ) (k : ℝ) (hk : 0≤k) :
    (cucbTrajectory oracle M.environment) {Y |
      k≤((M.chargeData bad inverseGap).counters (fun t => (Y t).1) n i : ℝ) ∧
      (observationCount (fun t => (Y t).2) n i : ℝ)≤k*M.minTrigger i/2} ≤
        ENNReal.ofReal (Real.exp (-k*M.minTrigger i/8)) :=
  (M.chargeData bad inverseGap).observation_below_charged_half oracle M.environment i
    (M.chargeData_trigger_bound bad inverseGap i) n k hk (M.minTrigger_pos i).le

omit [Fintype A] [MeasurableSingletonClass A] in
theorem nice_event_probability (oracle : Kernel (Input m) A) [IsMarkovKernel oracle] (n : ℕ) :
    (cucbTrajectory oracle M.environment) (NiceEvent (fun i => (M.trueInput i:ℝ)) n)ᶜ ≤
      ENNReal.ofReal (2*(m:ℝ)/((n:ℝ)+1)^2) :=
  niceEvent_complement_probability oracle M.environment M.laws M.observation_compatible n

end FeedbackModel
end BanditRLProof.CUCB

```

</details>

<details>
<summary>BanditRLProof/Algorithms/CUCBSourceModel.lean</summary>

```lean
import BanditRLProof.Algorithms.CUCBFeedbackModel

/-! The frozen full triggered-CUCB source model: arbitrary finite feasible
superarms, nonlinear smooth reward scores and randomized approximation oracle.
No confidence, counting or regret premise is part of this structure. -/
namespace BanditRLProof.CUCB
open MeasureTheory ProbabilityTheory
set_option autoImplicit false
variable {A : Type*} [Fintype A] [Nonempty A] {m : ℕ}

noncomputable def scoreOptimum (score : Input m → A → ℝ) (v : Input m) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (score v)

theorem score_le_optimum (score : Input m → A → ℝ) (v : Input m) (a : A) :
    score v a≤scoreOptimum score v := Finset.le_sup' _ (Finset.mem_univ a)

noncomputable def sourceGap (score : Input m → A → ℝ) (v : Input m) (α : ℝ) (a : A) : ℝ :=
  α*scoreOptimum score v-score v a

noncomputable def maxPositiveGap (score : Input m → A → ℝ) (v : Input m) (α : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun a => max 0 (sourceGap score v α a))

theorem gap_le_maxPositiveGap (score : Input m → A → ℝ) (v : Input m) (α : ℝ) (a : A) :
    sourceGap score v α a≤maxPositiveGap score v α :=
  (le_max_right (0:ℝ) (sourceGap score v α a)).trans
    (Finset.le_sup' (fun b => max 0 (sourceGap score v α b)) (Finset.mem_univ a))

variable [MeasurableSpace A]

structure SourceModel (M : FeedbackModel A m) where
  score : Input m → A → ℝ
  score_nonneg : ∀v a, 0≤score v a
  score_true : ∀a, score M.trueInput a=M.expectedReward a
  modulus : ℝ → ℝ
  modulus_zero : modulus 0=0
  modulus_continuous : ContinuousOn modulus (Set.Ici 0)
  modulus_strictMono : StrictMonoOn modulus (Set.Ici 0)
  score_monotone : ∀v w, (∀i, (v i:ℝ)≤(w i:ℝ)) → ∀a, score v a≤score w a
  score_smooth : ∀v w a L, 0≤L → (∀i∈M.possible a, |(v i:ℝ)-(w i:ℝ)|≤L) →
    |score v a-score w a|≤modulus L
  alpha : ℝ
  beta : ℝ
  alpha_mem : alpha ∈ Set.Ioc (0:ℝ) 1
  beta_mem : beta ∈ Set.Ioc (0:ℝ) 1
  oracle : Kernel (Input m) A
  oracle_markov : IsMarkovKernel oracle
  oracle_success : ∀v, ENNReal.ofReal beta ≤ oracle v {a | alpha*scoreOptimum score v≤score v a}
  inverse_range : ∀d, 0<d → d≤maxPositiveGap score M.trueInput alpha →
    ∃u, 0≤u ∧ modulus u=d

namespace SourceModel
variable {M : FeedbackModel A m} (S : SourceModel M)
instance oracle_isMarkov : IsMarkovKernel S.oracle := S.oracle_markov

noncomputable def gap (a : A) : ℝ := sourceGap S.score M.trueInput S.alpha a
noncomputable def bad (a : A) : Bool := decide (0<S.gap a)

noncomputable def inverseGap (a : A) : ℝ :=
  if h : 0<S.gap a then Classical.choose (S.inverse_range (S.gap a) h
    (gap_le_maxPositiveGap S.score M.trueInput S.alpha a)) else 0

theorem inverseGap_spec (a : A) (ha : 0<S.gap a) :
    0<S.inverseGap a ∧ S.modulus (S.inverseGap a)=S.gap a := by
  have h := Classical.choose_spec (S.inverse_range (S.gap a) ha
    (gap_le_maxPositiveGap S.score M.trueInput S.alpha a))
  rw [inverseGap, dif_pos ha]
  refine ⟨lt_of_le_of_ne h.1 ?_, h.2⟩
  intro hz
  rw [← hz, S.modulus_zero] at h
  linarith [h.2]

noncomputable def chargeData : ChargeData A m := M.chargeData S.bad S.inverseGap

theorem chargeData_sufficient (N : Fin m → ℕ) (a : A) (i : Fin m)
    (h : S.chargeData.choose N a=some i) (n : ℕ)
    (hi : samplingThreshold n (S.inverseGap a) (M.minTrigger i)<N i) :
    ∀j∈M.possible a, samplingThreshold n (S.inverseGap a) (M.minTrigger j)<N j := by
  have hb := (S.chargeData.choose_mem N a i h).1
  have hgap : 0<S.gap a := by simpa [chargeData, FeedbackModel.chargeData, bad] using hb
  exact S.chargeData.choose_sufficient N a i h (S.inverseGap_spec a hgap).1
    (fun j _ => M.minTrigger_pos j) n hi

theorem optimum_monotone (v w : Input m) (h : ∀i, (v i:ℝ)≤(w i:ℝ)) :
    scoreOptimum S.score v≤scoreOptimum S.score w := by
  apply Finset.sup'_le
  intro a ha
  exact (S.score_monotone v w h a).trans (score_le_optimum S.score w a)

theorem maxPositiveGap_eq_zero_of_no_bad (h : ∀a, S.gap a≤0) :
    maxPositiveGap S.score M.trueInput S.alpha=0 := by
  have he (a : A) : max 0 (sourceGap S.score M.trueInput S.alpha a)=0 :=
    max_eq_left (h a)
  simp [maxPositiveGap, he]

theorem counters_zero_of_no_bad (h : ∀a, S.gap a≤0) (actions : ℕ → A) (n : ℕ) (i : Fin m) :
    S.chargeData.counters actions n i=0 := by
  rw [ChargeData.counters_eq_sum]
  apply Finset.sum_eq_zero
  intro t ht
  have hb : S.bad (actions t)=false := by simp [bad, not_lt.mpr (h (actions t))]
  simp [ChargeData.choose, chargeData, FeedbackModel.chargeData, hb]

end SourceModel
end BanditRLProof.CUCB

```

</details>

<details>
<summary>BanditRLProof/Algorithms/CUCBRefinedRegret.lean</summary>

```lean
import BanditRLProof.Algorithms.CUCBUnderCountIntegral
import BanditRLProof.Algorithms.CUCBRegretTail

/-! The full refined integral approximation-regret endpoint, with the disclosed
normalized analysis-counter repair and the unchanged source CUCB learner. -/
namespace BanditRLProof.CUCB.SourceModel
open MeasureTheory ProbabilityTheory
set_option autoImplicit false
variable {A : Type*} [Fintype A] [Nonempty A] [MeasurableSpace A]
  [MeasurableSingletonClass A] [StandardBorelSpace A] {m : ℕ}
variable {M : FeedbackModel A m} (S : SourceModel M)

omit [StandardBorelSpace A] in
theorem expected_underSampledGap_le_refined (H : ℕ) (hH : 1≤H) :
    (∑n∈Finset.range H, ∫Y : ℕ → Round A m, S.underSampledGap H
      (S.chargeData.counters (fun t => (Y t).1) n) (Y n).1 ∂cucbTrajectory S.oracle M.environment) ≤
      (∑i:Fin m, S.armRefinedTerm H i)+(m:ℝ)*maxPositiveGap S.score M.trueInput S.alpha := by
  have hu := integrable_finset_sum (Finset.range H) (fun n _ => S.integrable_actual_underSampledGap H n)
  have h := integral_mono hu (integrable_const
    ((∑i:Fin m, S.armRefinedTerm H i)+(m:ℝ)*maxPositiveGap S.score M.trueInput S.alpha))
    (fun Y => S.sum_underSampledGap_le_refined H hH (fun t => (Y t).1))
  rw [integral_finset_sum _ (fun n _ => S.integrable_actual_underSampledGap H n)] at h
  simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using h

/-- Chen et al. JMLR 2016 Theorem 1, with the documented normalized charge repair.
The per-arm gap family is derived from actual bad actions and possible triggers;
an empty family contributes zero. No performance/count premise is assumed. -/
theorem theorem_one_refined_regret (H : ℕ) (hH : 1≤H) :
    S.approximationRegret H ≤ (∑i:Fin m, S.armRefinedTerm H i)+
      (1+(2+(if M.globalMinTrigger<1 then 1 else 0))*Real.pi^2/6)*
        (m:ℝ)*maxPositiveGap S.score M.trueInput S.alpha := by
  have h := S.approximationRegret_le_underSampled_add_source_tail H
  have hu := S.expected_underSampledGap_le_refined H hH
  calc
    _ ≤ _ := h.trans (add_le_add hu le_rfl)
    _ = _ := by ring

omit [MeasurableSingletonClass A] [StandardBorelSpace A] in
theorem armRefinedTerm_eq_zero_of_no_bad (H : ℕ) (h : ∀a, S.gap a≤0) (i : Fin m) :
    S.armRefinedTerm H i=0 := by
  classical
  have he : ¬(S.badActions i).Nonempty := by
    rintro ⟨a,ha⟩
    exact (not_lt.mpr (h a)) (Finset.mem_filter.mp ha).2.1
  simp [armRefinedTerm,he]

theorem approximationRegret_nonpos_of_no_bad (H : ℕ) (h : ∀a, S.gap a≤0) :
    S.approximationRegret H≤0 := by
  by_cases hH : 1≤H
  · have hr := S.theorem_one_refined_regret H hH
    simpa [S.armRefinedTerm_eq_zero_of_no_bad H h,S.maxPositiveGap_eq_zero_of_no_bad h] using hr
  · have he : H=0 := by omega
    rw [he,S.approximationRegret_zero]

end BanditRLProof.CUCB.SourceModel

```

</details>

<details>
<summary>BanditRLProof/Algorithms/CUCBPolynomialRegret.lean</summary>

```lean
import BanditRLProof.Algorithms.CUCBPolynomialIntegral
import BanditRLProof.PowerCutoffNormalization

/-! Exact source polynomial-smoothness endpoints, including small horizons. -/
namespace BanditRLProof.CUCB.SourceModel
open MeasureTheory ProbabilityTheory
set_option autoImplicit false
variable {A : Type*} [Fintype A] [Nonempty A] [MeasurableSpace A]
  [MeasurableSingletonClass A] [StandardBorelSpace A] {m : ℕ}
variable {M : FeedbackModel A m} (S : SourceModel M)

include M in
omit [Fintype A] [MeasurableSingletonClass A] [StandardBorelSpace A] in
theorem base_arm_count_pos : 0<m := by
  obtain ⟨i,_⟩ := M.arms_nonempty
  have h := i.isLt
  omega

omit [StandardBorelSpace A] in
theorem approximationRegret_le_linear_gap (H : ℕ) :
    S.approximationRegret H≤(H:ℝ)*maxPositiveGap S.score M.trueInput S.alpha := by
  have hg : ∀Y : ℕ → Round A m, (∑n∈Finset.range H, S.gap (Y n).1)≤
      (H:ℝ)*maxPositiveGap S.score M.trueInput S.alpha := by
    intro Y
    have h := Finset.sum_le_sum (s:=Finset.range H) (fun n _ =>
      gap_le_maxPositiveGap S.score M.trueInput S.alpha (Y n).1)
    simpa only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] using h
  have hi := integral_mono (integrable_finset_sum _ (fun n _ => S.integrable_actual_gap n))
    (integrable_const _) hg
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul] at hi
  obtain ⟨a⟩ := ‹Nonempty A›
  have ho : 0≤scoreOptimum S.score M.trueInput := (S.score_nonneg _ a).trans (score_le_optimum _ _ a)
  have hc : 0≤(H:ℝ)*S.alpha*(1-S.beta)*scoreOptimum S.score M.trueInput :=
    mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg H) S.alpha_mem.1.le)
      (sub_nonneg.mpr S.beta_mem.2)) ho
  rw [S.approximationRegret_eq_gap_sum]
  linarith

omit [StandardBorelSpace A] in
theorem approximationRegret_one_le (c : ℝ) (hc : 1≤c) :
    S.approximationRegret 1≤c*(m:ℝ)*maxPositiveGap S.score M.trueInput S.alpha := by
  have h := S.approximationRegret_le_linear_gap 1
  simp only [Nat.cast_one,one_mul] at h
  have hm : (1:ℝ)≤m := by exact_mod_cast (Nat.succ_le_of_lt (base_arm_count_pos (M:=M)))
  have hcm : (1:ℝ)≤c*(m:ℝ) := by nlinarith [mul_nonneg (sub_nonneg.mpr hc) (sub_nonneg.mpr hm)]
  exact h.trans (by nlinarith [mul_nonneg (sub_nonneg.mpr hcm) S.maxPositiveGap_nonneg])

theorem theorem_two_deterministic (H : ℕ) (hH : 1≤H) (hp : M.globalMinTrigger=1)
    (γ ω : ℝ) (hγ : 0<γ) (hω : 0<ω) (hω1 : ω≤1)
    (hf : ∀u, 0≤u → S.modulus u=γ*u^ω) :
    S.approximationRegret H≤(2*γ/(2-ω))*(6*(m:ℝ)*Real.log (H:ℝ))^(ω/2)*(H:ℝ)^(1-ω/2)+
      (1+Real.pi^2/3)*(m:ℝ)*maxPositiveGap S.score M.trueInput S.alpha := by
  by_cases hone : H=1
  · subst H
    simpa [Real.zero_rpow (show ω/2≠0 by positivity)] using
      S.approximationRegret_one_le (1+Real.pi^2/3) (by nlinarith [sq_nonneg Real.pi])
  have hHgt : 1<H := by omega
  have hN : 0<(H:ℝ) := by exact_mod_cast (show 0<H by omega)
  have hm : 0<(m:ℝ) := by exact_mod_cast (base_arm_count_pos (M:=M))
  have hlog : 0<Real.log (H:ℝ) := Real.log_pos (by exact_mod_cast hHgt)
  let q := 2/ω
  let C := 6*(m:ℝ)*Real.log (H:ℝ)
  let K := C*γ^q
  let a := (K/(H:ℝ))^(1/q)
  have hq : 1<q := (lt_div_iff₀ hω).mpr (by linarith)
  have hC : 0<C := by dsimp [C]; positivity
  have hK : 0<K := mul_pos hC (Real.rpow_pos_of_pos hγ _)
  have ha : 0<a := Real.rpow_pos_of_pos (div_pos hK hN) _
  have hopt : S.approximationRegret H≤q/(q-1)*((H:ℝ)*a)+
      (1+Real.pi^2/3)*(m:ℝ)*maxPositiveGap S.score M.trueInput S.alpha := by
    by_cases hlarge : maxPositiveGap S.score M.trueInput S.alpha≤a
    · have hr := S.approximationRegret_le_large_cutoff H a hlarge
      simp only [hp,lt_self_iff_false,ite_false,add_zero] at hr
      have hc : 1≤q/(q-1) := (le_div_iff₀ (by linarith)).mpr (by linarith)
      have hh := mul_le_mul_of_nonneg_right hc (mul_pos hN ha).le
      have hd := mul_nonneg (Nat.cast_nonneg (α:=ℝ) m) S.maxPositiveGap_nonneg
      nlinarith
    · have hr := S.polynomial_cutoff_regret_deterministic H hH hp γ ω hγ hω hω1 hf a
        ⟨ha,le_of_not_ge hlarge⟩
      have hr' : S.approximationRegret H≤(H:ℝ)*a+K*a^(1-q)/(q-1)+
          (1+Real.pi^2/3)*(m:ℝ)*maxPositiveGap S.score M.trueInput S.alpha := by
        dsimp [K,C,q]
        convert hr using 1
        ring
      rw [show (H:ℝ)*a+K*a^(1-q)/(q-1)=q/(q-1)*((H:ℝ)*a) from
        PowerTailIntegral.cutoff_objective K (H:ℝ) q hK hN hq] at hr'
      exact hr'
  have he := PowerTailIntegral.source_cutoff_normalization C (H:ℝ) γ ω hC hN hγ hω hω1
  change q/(q-1)*((H:ℝ)*a)=_ at he
  rw [he] at hopt
  exact hopt





theorem theorem_two_probabilistic (H : ℕ) (hH : 1≤H) (hp : M.globalMinTrigger<1)
    (γ ω : ℝ) (hγ : 0<γ) (hω : 0<ω) (hω1 : ω≤1)
    (hf : ∀u, 0≤u → S.modulus u=γ*u^ω) :
    S.approximationRegret H≤(2*γ/(2-ω))*(12*(m:ℝ)*Real.log (H:ℝ)/M.globalMinTrigger)^(ω/2)*
      (H:ℝ)^(1-ω/2)+(1+Real.pi^2/2)*(m:ℝ)*maxPositiveGap S.score M.trueInput S.alpha+
      ∑i:Fin m, (24*Real.log (H:ℝ)/M.minTrigger i)*maxPositiveGap S.score M.trueInput S.alpha := by
  by_cases hone : H=1
  · subst H
    simpa [Real.zero_rpow (show ω/2≠0 by positivity)] using
      S.approximationRegret_one_le (1+Real.pi^2/2) (by nlinarith [sq_nonneg Real.pi])
  have hHgt : 1<H := by omega
  have hN : 0<(H:ℝ) := by exact_mod_cast (show 0<H by omega)
  have hm : 0<(m:ℝ) := by exact_mod_cast (base_arm_count_pos (M:=M))
  have hlog : 0<Real.log (H:ℝ) := Real.log_pos (by exact_mod_cast hHgt)
  have hpstar := M.globalMinTrigger_pos
  let q := 2/ω
  let C := 12*(m:ℝ)*Real.log (H:ℝ)/M.globalMinTrigger
  let K := C*γ^q
  let a := (K/(H:ℝ))^(1/q)
  have hq : 1<q := (lt_div_iff₀ hω).mpr (by linarith)
  have hC : 0<C := by dsimp [C]; positivity
  have hK : 0<K := mul_pos hC (Real.rpow_pos_of_pos hγ _)
  have ha : 0<a := Real.rpow_pos_of_pos (div_pos hK hN) _
  have hE : 0≤∑i:Fin m, (24*Real.log (H:ℝ)/M.minTrigger i)*
      maxPositiveGap S.score M.trueInput S.alpha := by
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (div_nonneg (by positivity) (M.minTrigger_pos i).le) S.maxPositiveGap_nonneg
  have hopt : S.approximationRegret H≤q/(q-1)*((H:ℝ)*a)+
      (1+Real.pi^2/2)*(m:ℝ)*maxPositiveGap S.score M.trueInput S.alpha+
      ∑i:Fin m, (24*Real.log (H:ℝ)/M.minTrigger i)*maxPositiveGap S.score M.trueInput S.alpha := by
    by_cases hlarge : maxPositiveGap S.score M.trueInput S.alpha≤a
    · have hr := S.approximationRegret_le_large_cutoff H a hlarge
      simp only [hp,ite_true] at hr
      have hc : 1≤q/(q-1) := (le_div_iff₀ (by linarith)).mpr (by linarith)
      have hh := mul_le_mul_of_nonneg_right hc (mul_pos hN ha).le
      have hd := mul_nonneg (Nat.cast_nonneg (α:=ℝ) m) S.maxPositiveGap_nonneg
      nlinarith
    · have hr := S.polynomial_cutoff_regret_probabilistic H hH hp γ ω hγ hω hω1 hf a
        ⟨ha,le_of_not_ge hlarge⟩
      have hr' : S.approximationRegret H≤(H:ℝ)*a+K*a^(1-q)/(q-1)+
          (1+Real.pi^2/2)*(m:ℝ)*maxPositiveGap S.score M.trueInput S.alpha+
          ∑i:Fin m, (24*Real.log (H:ℝ)/M.minTrigger i)*maxPositiveGap S.score M.trueInput S.alpha := by
        dsimp [K,C,q]
        convert hr using 1
        ring
      rw [show (H:ℝ)*a+K*a^(1-q)/(q-1)=q/(q-1)*((H:ℝ)*a) from
        PowerTailIntegral.cutoff_objective K (H:ℝ) q hK hN hq] at hr'
      exact hr'
  have he := PowerTailIntegral.source_cutoff_normalization C (H:ℝ) γ ω hC hN hγ hω hω1
  change q/(q-1)*((H:ℝ)*a)=_ at he
  rw [he] at hopt
  exact hopt

end BanditRLProof.CUCB.SourceModel

```

</details>

