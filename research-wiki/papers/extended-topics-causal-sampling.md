# Causal intervention sampling: reviewed common-alphabet performance chain

This is a partial result for the frozen causal topic. The common finite alphabet
model below is independently reviewed. The separately reviewed [native heterogeneous bridge](extended-topics-causal-heterogeneous.md) and [exact noisy diagnostics](extended-topics-causal-noisy-diagnostics.md) are now available. The [parallel allocation and boundary witnesses](extended-topics-causal-parallel.md) are now independently reviewed. Remaining source audit and ICLR evidence remain open.

## Source and exact scope

Lattimore, Lattimore and Reid, *Causal Bandits: Learning Good Interventions via
Causal Inference*, NIPS 2016, Algorithm 2 (main p.5), Theorem 3 and Proposition 4
(main p.6), with the complete Theorem 3 proof in the official supplement p.14.
The pinned source hashes are in `docs/extended-topics/causal-source-hashes.json`.

Let A be a finite nonempty ordered action set, K its cardinality, and T>=1.
The DAG has topologically ordered nodes, local conditional tables on a common
finite inhabited alphabet V, and a distinguished node i with binary payoff
rewardBit(x_i). Actions replace non-reward-node tables with point masses and
leave node i untouched. Every finite space has measurable singletons. No
positive gap, unique optimum, or strictly positive allocation weight is assumed.

The full joint distribution is constructed from the tables. Its reward-parent
marginals P_a are known to the learner; the common reward table is unknown.
For a fixed allocation eta, Q=sum_a eta(a)P_a must cover every P_a support.
Define R_a=P_a/Q, m=max_a sum_z P_a(z)^2/Q(z), L=log(2TK), B=sqrt(mT/L).
Division outside support is totalized, but coverage is a separate hypothesis.

## Actual algorithm and proof

Each round samples a from eta, then a complete assignment from the intervened
DAG joint law. The T-fold product measure supplies independent fresh rounds.
Projection to the reward parents and payoff bit has the derived paired law
Q(z)r(y|z). The observed statistic is W_a=Y R_a(Z) 1{R_a(Z)<=B}; the estimate
is its sample average. The output is the least maximizer in the fixed order.
Neither a confidence event nor a successful recommendation is an input premise.

Integral transport and the paired-law identity prove 0<=W_a<=B,
E W_a^2<=m, and E W_a=mu_a-beta_a, with 0<=beta_a<=m/B.
The shared HeavyTail bounded-centering MGF and independent-sum MGF use tilt
1/(2B). With epsilon=sqrt(2mL/T)+3BL/T the signed exponent is at most -L;
two signs and K actions give failure probability at most 1/T.

Outside the bad event, empirical maximization gives regret <=2epsilon+m/B.
Every sample has regret in [0,1], so integrating its bound by this constant
plus the bad-event indicator yields

    E[mu_* - mu_recommendation]
      <= (2 sqrt(2)+7) sqrt(m log(2TK)/T) + 1/T,
    E[mu_* - mu_recommendation] <= 1.

The mean in this expression is proved equal to the intervention reward
integral. The inequality log(2TK)>=1/2 gives an explicit rate constant
3 sqrt(2)+7 after absorbing the residual. It does not use the false universal
inequality 1/T<=sqrt(m log(2TK)/T).

Uniform allocation covers all supports and m<=K, so its RHS can be relaxed to K.
Its actual threshold still uses m, not the substituted K. The attained optimal
allocation from the compact covered sublevel proof is another actual-law
instantiation. Minimizing m optimizes this design objective; no comparison of
the actual regrets of two different allocations is asserted.

## Source differences and unfinished obligations

The displayed coefficient and failure direction are explicit repairs to the
printed proof, independently reviewed mathematically. The algorithm and
truncation tuning are retained. This does not prove that a sharper constant
is impossible. Fixed total-order ties are made explicit.

The separately reviewed native heterogeneous bridge now preserves support, interventions, observations, estimates and regret for distinct nonempty finite node types. This file retains the common-alphabet producer it reuses. The Boolean readout is not arbitrary real-valued reward.
The learner definitions consume known parent laws and observed bits; there is
no separate cross-model reward-table-invariance theorem in this packet.

The concrete noisy X->W, X->Y, W->Y test constructs the joint law and derives
means 1/2, 3/10, 7/10, then instantiates the uniform all-horizon bound.
The separate exact diagnostic packet now proves concentrated coverage and m=8/3, biases, the conditional-observation contrast, exact tuned T=1 regret and an uncovered diagnostic. The separate [parallel witness packet](extended-topics-causal-parallel.md) now closes that obligation.
Compilation of these partial results does not complete the causal topic.

## Actual reuse and evidence

The chain reuses CausalOrderedLaw, CausalMarginalLaw, CausalImportance,
CausalAllocation and CausalOptimalAllocation, the shared FiniteRealArgmax,
HeavyTail.bounded_centering_mgf and HeavyTail.independent_sum_mgf, and Mathlib
finite product measures, coordinate independence and Bochner integration.
Reading links do not claim additional proof dependencies or a certified functor.

The historical sampling review and validation retain three invalid file hashes;
their original byte provenance is unresolved. They are preserved as historical
records, not used as current code bindings. Fresh distinct blind/source reviews
cover all seven sampling modules, their noisy canary, and all five foundations
at commit `132a8340f097b5e05bd17669980830b1f9c3d7e3`. Current bindings and
explicit source deltas are in `runs/extended-topics-20260920/causal-review-rebinding.json`.
The checker `tools/check_causal_review_bindings.py` verifies both commit and
working-tree bytes with CRLF/bare-CR to LF normalization only. It checks identity
and declared coverage, not the mathematical quality of review.

`designCost_convex` is a separately reviewed design-geometry result. The attained
optimizer proof uses compactness and continuity, not that convexity theorem;
its downstream regret consumer does not make convexity an endpoint dependency.
The optimizer is noncomputable classical choice, not a verified numerical solver.

## Exact Lean context, statements and proofs

The following module snapshots retain imports and section variables so the
finite-space and fixed-order assumptions remain visible.

<details>
<summary>CausalSampling - exact module</summary>

SHA256 (UTF-8, CRLF/bare-CR normalized to LF): `f9f321a43fa1985ea35f7316bfe1c334b1174e12fa13c56c86c08a41926cf5b7`

```lean
import BanditRLProof.Algorithms.CausalOptimalAllocation
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Independence.Basic

/-! Actual intervention/assignment rounds and their fixed-budget product law. -/
namespace BanditRLProof.Causal
open scoped Classical
open MeasureTheory ProbabilityTheory
set_option autoImplicit false

variable {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
variable {n : ℕ}
variable {V : Type*} [Fintype V] [Inhabited V]
variable [MeasurableSpace V] [MeasurableSingletonClass V]

noncomputable def GraphModel.roundLaw (g : GraphModel V n)
    (actions : A → Fin n → Option V) (eta : PMF A) : PMF (A × (Fin n → V)) :=
  eta.bind fun a => (joint (g.doModel (actions a)).table).map fun x => (a,x)

def GraphModel.observation (g : GraphModel V n) (rewardBit : V → Bool) (i : Fin n)
    (ax : A × (Fin n → V)) : g.ParentConfig i × Bool :=
  (g.parentConfig i (history ax.2 i), rewardBit (ax.2 i))

omit [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] in
theorem GraphModel.roundLaw_observation (g : GraphModel V n) (rewardBit : V → Bool)
    (actions : A → Fin n → Option V) (eta : PMF A)
    (i : Fin n) (hi : ∀ a, actions a i = none) :
    (g.roundLaw actions eta).map (g.observation rewardBit i) =
      pairedLaw (mixture eta (fun a => g.parentLaw (actions a) i)) (fun z => (g.parentTable i z).map rewardBit) := by
  have h := congrArg (fun p : PMF (g.ParentConfig i × V) =>
    p.map (fun zy => (zy.1, rewardBit zy.2)))
    (g.mixture_parent_joint actions eta i hi)
  simpa only [roundLaw, PMF.map_bind, PMF.map_comp, observation, Function.comp_def,
    mixture, pairedLaw] using h

noncomputable def GraphModel.sampleLaw (g : GraphModel V n)
    (actions : A → Fin n → Option V) (eta : PMF A) (T : ℕ) :
    Measure (Fin T → A × (Fin n → V)) :=
  Measure.pi fun _ : Fin T => (g.roundLaw actions eta).toMeasure

instance GraphModel.sampleLaw_isProbabilityMeasure (g : GraphModel V n)
    (actions : A → Fin n → Option V) (eta : PMF A) (T : ℕ) :
    IsProbabilityMeasure (g.sampleLaw actions eta T) := by
  unfold sampleLaw
  infer_instance

theorem GraphModel.sampleLaw_observation (g : GraphModel V n) (rewardBit : V → Bool)
    (actions : A → Fin n → Option V) (eta : PMF A) (T : ℕ)
    (i : Fin n) (hi : ∀ a, actions a i = none) (t : Fin T) :
    (g.sampleLaw actions eta T).map (fun w => g.observation rewardBit i (w t)) =
      (pairedLaw (mixture eta (fun a => g.parentLaw (actions a) i))
        (fun z => (g.parentTable i z).map rewardBit)).toMeasure := by
  change Measure.map (g.observation rewardBit i ∘
    (fun w : Fin T → A × (Fin n → V) => w t)) _ = _
  have ho : Measurable (g.observation (A := A) rewardBit i) := Measurable.of_discrete
  rw [← Measure.map_map ho (measurable_pi_apply t)]
  unfold sampleLaw
  rw [(measurePreserving_eval (fun _ : Fin T => (g.roundLaw actions eta).toMeasure) t).map_eq]
  rw [PMF.toMeasure_map (g.observation rewardBit i) (g.roundLaw actions eta) ho,
    g.roundLaw_observation rewardBit actions eta i hi]

theorem GraphModel.integral_sample_observation (g : GraphModel V n) (rewardBit : V → Bool)
    (actions : A → Fin n → Option V) (eta : PMF A) (T : ℕ)
    (i : Fin n) (hi : ∀ a, actions a i = none) (t : Fin T)
    (f : g.ParentConfig i × Bool → ℝ) :
    (∫ w, f (g.observation rewardBit i (w t)) ∂g.sampleLaw actions eta T) =
      ∫ zy, f zy ∂(pairedLaw (mixture eta (fun a => g.parentLaw (actions a) i))
        (fun z => (g.parentTable i z).map rewardBit)).toMeasure := by
  rw [← g.sampleLaw_observation rewardBit actions eta T i hi t]
  exact (integral_map Measurable.of_discrete.aemeasurable
    Measurable.of_discrete.aestronglyMeasurable).symm

noncomputable def GraphModel.sampleWeightedBit (g : GraphModel V n) (rewardBit : V → Bool)
    (actions : A → Fin n → Option V) (eta : PMF A) (i : Fin n)
    (a : A) (B : ℝ) {T : ℕ} (t : Fin T) (w : Fin T → A × (Fin n → V)) : ℝ :=
  weightedBit (g.parentLaw (actions a) i)
    (mixture eta (fun b => g.parentLaw (actions b) i)) B (g.observation rewardBit i (w t))

theorem GraphModel.sampleWeightedBit_independent (g : GraphModel V n) (rewardBit : V → Bool)
    (actions : A → Fin n → Option V) (eta : PMF A) (i : Fin n)
    (a : A) (B : ℝ) (T : ℕ) :
    iIndepFun (g.sampleWeightedBit rewardBit actions eta i a B (T := T))
      (g.sampleLaw actions eta T) := by
  exact iIndepFun_pi
    (μ := fun _ : Fin T => (g.roundLaw actions eta).toMeasure)
    (X := fun _ : Fin T => fun ax : A × (Fin n → V) =>
      weightedBit (g.parentLaw (actions a) i)
        (mixture eta (fun b => g.parentLaw (actions b) i)) B (g.observation rewardBit i ax))
    (fun _ => Measurable.of_discrete.aemeasurable)

theorem GraphModel.sampleWeightedBit_mean (g : GraphModel V n) (rewardBit : V → Bool)
    (actions : A → Fin n → Option V) (eta : PMF A)
    (i : Fin n) (hi : ∀ a, actions a i = none) (a : A) (B : ℝ)
    (T : ℕ) (t : Fin T) :
    (∫ w, g.sampleWeightedBit rewardBit actions eta i a B t w ∂g.sampleLaw actions eta T) =
      truncatedMean (g.parentLaw (actions a) i)
        (mixture eta (fun b => g.parentLaw (actions b) i))
        (fun z => mass ((g.parentTable i z).map rewardBit) true) B := by
  unfold sampleWeightedBit
  rw [g.integral_sample_observation rewardBit actions eta T i hi t, PMF.integral_eq_sum]
  simpa only [Fintype.sum_prod_type, smul_eq_mul, mass] using
    weightedBit_mean (g.parentLaw (actions a) i)
      (mixture eta (fun b => g.parentLaw (actions b) i)) (fun z => (g.parentTable i z).map rewardBit) B

theorem GraphModel.sampleWeightedBit_second_le (g : GraphModel V n) (rewardBit : V → Bool)
    (actions : A → Fin n → Option V) (eta : PMF A)
    (i : Fin n) (hi : ∀ a, actions a i = none)
    (hc : Covers (fun a => g.parentLaw (actions a) i)
      (mixture eta (fun a => g.parentLaw (actions a) i)))
    (a : A) (B : ℝ) (T : ℕ) (t : Fin T) :
    (∫ w, (g.sampleWeightedBit rewardBit actions eta i a B t w)^2 ∂g.sampleLaw actions eta T) ≤
      secondMoment (g.parentLaw (actions a) i)
        (mixture eta (fun b => g.parentLaw (actions b) i)) := by
  unfold sampleWeightedBit
  rw [g.integral_sample_observation rewardBit actions eta T i hi t
    (fun zy => (weightedBit (g.parentLaw (actions a) i)
      (mixture eta (fun b => g.parentLaw (actions b) i)) B zy)^2), PMF.integral_eq_sum]
  simpa only [Fintype.sum_prod_type, smul_eq_mul, mass] using
    weightedBit_second_le (fun a => g.parentLaw (actions a) i)
      (mixture eta (fun b => g.parentLaw (actions b) i)) hc a (fun z => (g.parentTable i z).map rewardBit) B

end BanditRLProof.Causal
```

</details>

<details>
<summary>CausalSampleMGF - exact module</summary>

SHA256 (UTF-8, CRLF/bare-CR normalized to LF): `a9e5e3c4dedaff1174bd7692b3556100d377d485825f89bef7c0def6f64b61f9`

```lean
import BanditRLProof.Algorithms.CausalSampling
import BanditRLProof.HeavyTailFixedTilt

/-! Centered MGF and signed sum tails on actual causal intervention samples. -/
namespace BanditRLProof.Causal
open scoped Classical
open MeasureTheory ProbabilityTheory
set_option autoImplicit false
set_option maxHeartbeats 800000

variable {A : Type*} [Fintype A] [Nonempty A]
variable [MeasurableSpace A] [MeasurableSingletonClass A] {n : ℕ}
variable {V : Type*} [Fintype V] [Inhabited V]
variable [MeasurableSpace V] [MeasurableSingletonClass V]

theorem GraphModel.sampleWeightedBit_signed_mgf (g : GraphModel V n) (rewardBit : V → Bool)
    (actions : A → Fin n → Option V) (eta : PMF A)
    (i : Fin n) (hi : ∀ a, actions a i = none)
    (hc : Covers (fun a => g.parentLaw (actions a) i)
      (mixture eta (fun a => g.parentLaw (actions a) i)))
    (a : A) (B : ℝ) (hB : 0 ≤ B) (T : ℕ) (t : Fin T)
    (sign tilt : ℝ) (hs : |sign| = 1) (hsmall : |tilt| * (2*B) ≤ 1) :
    Concentration.HasMGFUpperBoundAt
      (fun w => sign * (g.sampleWeightedBit rewardBit actions eta i a B t w -
        truncatedMean (g.parentLaw (actions a) i)
          (mixture eta (fun b => g.parentLaw (actions b) i))
          (fun z => mass ((g.parentTable i z).map rewardBit) true) B))
      tilt (tilt^2 * designCost (fun b => g.parentLaw (actions b) i) eta)
      (g.sampleLaw actions eta T) := by
  let W := g.sampleWeightedBit rewardBit actions eta i a B t
  have hbound : ∀ w, |sign * W w| ≤ B := by
    intro w
    have hb := weightedBit_bounds (g.parentLaw (actions a) i)
      (mixture eta (fun b => g.parentLaw (actions b) i)) B hB (g.observation rewardBit i (w t))
    change 0 ≤ W w ∧ W w ≤ B at hb
    rw [abs_mul, hs, one_mul, abs_of_nonneg hb.1]
    exact hb.2
  have hs2 : sign^2 = 1 := by
    calc
      sign^2 = |sign|^2 := (sq_abs sign).symm
      _ = 1 := by rw [hs]; norm_num
  have hsecond : (∫ w, (sign * W w)^2 ∂g.sampleLaw actions eta T) ≤
      designCost (fun b => g.parentLaw (actions b) i) eta := by
    simp only [mul_pow, hs2, one_mul]
    change (∫ w, (g.sampleWeightedBit rewardBit actions eta i a B t w)^2
      ∂g.sampleLaw actions eta T) ≤ _
    exact (g.sampleWeightedBit_second_le rewardBit actions eta i hi hc a B T t).trans
      (secondMoment_le_designCost (fun b => g.parentLaw (actions b) i) eta a)
  have h := HeavyTail.bounded_centering_mgf (g.sampleLaw actions eta T)
    (fun w => sign * W w) B _ tilt Measurable.of_discrete hbound hsecond hsmall
  simpa only [integral_const_mul, W, g.sampleWeightedBit_mean rewardBit actions eta i hi a B T t,
    mul_sub] using h

theorem GraphModel.sampleWeightedBit_signed_sum_mgf (g : GraphModel V n) (rewardBit : V → Bool)
    (actions : A → Fin n → Option V) (eta : PMF A)
    (i : Fin n) (hi : ∀ a, actions a i = none)
    (hc : Covers (fun a => g.parentLaw (actions a) i)
      (mixture eta (fun a => g.parentLaw (actions a) i)))
    (a : A) (B : ℝ) (hB : 0 ≤ B) (T : ℕ)
    (sign tilt : ℝ) (hs : |sign| = 1) (hsmall : |tilt| * (2*B) ≤ 1) :
    Concentration.HasMGFUpperBoundAt
      (fun w => ∑ t : Fin T, sign * (g.sampleWeightedBit rewardBit actions eta i a B t w -
        truncatedMean (g.parentLaw (actions a) i)
          (mixture eta (fun b => g.parentLaw (actions b) i))
          (fun z => mass ((g.parentTable i z).map rewardBit) true) B))
      tilt ((T:ℝ) * (tilt^2 * designCost (fun b => g.parentLaw (actions b) i) eta))
      (g.sampleLaw actions eta T) := by
  let c := truncatedMean (g.parentLaw (actions a) i)
    (mixture eta (fun b => g.parentLaw (actions b) i))
    (fun z => mass ((g.parentTable i z).map rewardBit) true) B
  let X := fun t : Fin T => fun w => sign * (g.sampleWeightedBit rewardBit actions eta i a B t w - c)
  have hind : iIndepFun X (g.sampleLaw actions eta T) :=
    (g.sampleWeightedBit_independent rewardBit actions eta i a B T).comp
      (fun _ x => sign * (x-c)) (fun _ => (measurable_id.sub measurable_const).const_mul sign)
  have h := HeavyTail.independent_sum_mgf (g.sampleLaw actions eta T) X Finset.univ tilt
    (fun _ => tilt^2 * designCost (fun b => g.parentLaw (actions b) i) eta)
    hind (fun _ => Measurable.of_discrete)
    (fun t _ => g.sampleWeightedBit_signed_mgf rewardBit actions eta i hi hc a B hB T t sign tilt hs hsmall)
  have hfun : (∑ t : Fin T, X t) = (fun w => ∑ t : Fin T, X t w) := by
    funext w
    simp only [Finset.sum_apply]
  rw [hfun] at h
  simpa only [X, c, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] using h

theorem GraphModel.sampleWeightedBit_signed_sum_tail (g : GraphModel V n) (rewardBit : V → Bool)
    (actions : A → Fin n → Option V) (eta : PMF A)
    (i : Fin n) (hi : ∀ a, actions a i = none)
    (hc : Covers (fun a => g.parentLaw (actions a) i)
      (mixture eta (fun a => g.parentLaw (actions a) i)))
    (a : A) (B : ℝ) (hB : 0 ≤ B) (T : ℕ)
    (sign tilt r : ℝ) (hs : |sign| = 1) (ht : 0 ≤ tilt)
    (hsmall : |tilt| * (2*B) ≤ 1) :
    (g.sampleLaw actions eta T).real {w | r ≤
      ∑ t : Fin T, sign * (g.sampleWeightedBit rewardBit actions eta i a B t w -
        truncatedMean (g.parentLaw (actions a) i)
          (mixture eta (fun b => g.parentLaw (actions b) i))
          (fun z => mass ((g.parentTable i z).map rewardBit) true) B)} ≤
      Real.exp (-tilt*r + (T:ℝ) * (tilt^2 * designCost (fun b => g.parentLaw (actions b) i) eta)) :=
  (g.sampleWeightedBit_signed_sum_mgf rewardBit actions eta i hi hc a B hB T sign tilt hs hsmall).measure_ge_le_exp_add r ht

end BanditRLProof.Causal
```

</details>

<details>
<summary>CausalTuning - exact module</summary>

SHA256 (UTF-8, CRLF/bare-CR normalized to LF): `cf0a682aeed3a37e4667654f8a021efc9b241da4a9b62b11850ddb8cdc422292`

```lean
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-! The fixed source tuning used for the causal importance estimator. -/
namespace BanditRLProof.Causal
set_option autoImplicit false

noncomputable def sourceThreshold (m T L : ℝ) : ℝ := Real.sqrt (m*T/L)

noncomputable def sourceRadius (m T L : ℝ) : ℝ :=
  Real.sqrt (2*m*L/T) + 3*sourceThreshold m T L*L/T

noncomputable def sourceLog (T K : ℕ) : ℝ := Real.log (2*(T:ℝ)*K)

theorem sourceLog_pos (T K : ℕ) (hT : 0 < T) (hK : 0 < K) : 0 < sourceLog T K := by
  have hT' : (1:ℝ) ≤ T := by exact_mod_cast hT
  have hK' : (1:ℝ) ≤ K := by exact_mod_cast hK
  apply Real.log_pos
  nlinarith

theorem sourceLog_union_budget (T K : ℕ) (hT : 0 < T) (hK : 0 < K) :
    (K:ℝ)*(2*Real.exp (-sourceLog T K)) = 1/(T:ℝ) := by
  have hT' : (0:ℝ) < T := by exact_mod_cast hT
  have hK' : (0:ℝ) < K := by exact_mod_cast hK
  rw [Real.exp_neg, sourceLog, Real.exp_log (by positivity)]
  field_simp

theorem sourceThreshold_pos (m T L : ℝ) (hm : 0 < m) (hT : 0 < T) (hL : 0 < L) :
    0 < sourceThreshold m T L := Real.sqrt_pos.2 (div_pos (mul_pos hm hT) hL)

theorem sourceThreshold_sq (m T L : ℝ) (hm : 0 ≤ m) (hT : 0 ≤ T) (hL : 0 ≤ L) :
    (sourceThreshold m T L)^2 = m*T/L := Real.sq_sqrt (div_nonneg (mul_nonneg hm hT) hL)

theorem sourceTilt_admissible (m T L : ℝ) (hm : 0 < m) (hT : 0 < T) (hL : 0 < L) :
    |1/(2*sourceThreshold m T L)| * (2*sourceThreshold m T L) ≤ 1 := by
  have hB := sourceThreshold_pos m T L hm hT hL
  rw [abs_of_pos (div_pos zero_lt_one (mul_pos (by norm_num) hB))]
  exact (div_mul_cancel₀ 1 (ne_of_gt (mul_pos (by norm_num) hB))).le

theorem sourceTilt_budget (m T L : ℝ) (hm : 0 < m) (hT : 0 < T) (hL : 0 < L) :
    T * ((1/(2*sourceThreshold m T L))^2*m) = L/4 := by
  have hB := sourceThreshold_pos m T L hm hT hL
  have hsq := sourceThreshold_sq m T L hm.le hT.le hL.le
  have hprod : (sourceThreshold m T L)^2 * L = m*T :=
    (eq_div_iff hL.ne').mp hsq
  field_simp
  nlinarith

theorem sourceTilt_exponent_le (m T L : ℝ) (hm : 0 < m) (hT : 0 < T) (hL : 0 < L) :
    -(1/(2*sourceThreshold m T L)) * (T*sourceRadius m T L) +
      T * ((1/(2*sourceThreshold m T L))^2*m) ≤ -L := by
  have hB := sourceThreshold_pos m T L hm hT hL
  have ht : 0 < 1/(2*sourceThreshold m T L) := by positivity
  have hr : 3*sourceThreshold m T L*L/T ≤ sourceRadius m T L := by
    unfold sourceRadius
    linarith [Real.sqrt_nonneg (2*m*L/T)]
  rw [sourceTilt_budget m T L hm hT hL]
  calc
    -(1/(2*sourceThreshold m T L)) * (T*sourceRadius m T L) + L/4 ≤
        -(1/(2*sourceThreshold m T L)) * (T*(3*sourceThreshold m T L*L/T)) + L/4 := by
      have h := mul_le_mul_of_nonneg_left hr hT.le
      nlinarith [mul_le_mul_of_nonpos_left h (neg_nonpos.mpr ht.le)]
    _ = -(5*L)/4 := by field_simp; ring
    _ ≤ -L := by linarith

theorem sourceThreshold_scale (m T L : ℝ) (hm : 0 < m) (hT : 0 < T) (hL : 0 < L) :
    sourceThreshold m T L * L / T = Real.sqrt (m*L/T) := by
  have hB := sourceThreshold_pos m T L hm hT hL
  have hsq := sourceThreshold_sq m T L hm.le hT.le hL.le
  have hrad := Real.sq_sqrt (show 0 ≤ m*L/T by positivity)
  have hleft : 0 ≤ sourceThreshold m T L * L / T := by positivity
  have heq : (sourceThreshold m T L * L / T)^2 = m*L/T := by
    rw [div_pow, mul_pow, hsq]
    field_simp
  nlinarith [Real.sqrt_nonneg (m*L/T)]

theorem sourceThreshold_bias_scale (m T L : ℝ) (hm : 0 < m) (hT : 0 < T) (hL : 0 < L) :
    m/sourceThreshold m T L = Real.sqrt (m*L/T) := by
  have hB := sourceThreshold_pos m T L hm hT hL
  have hsq := sourceThreshold_sq m T L hm.le hT.le hL.le
  rw [← sourceThreshold_scale m T L hm hT hL]
  apply (div_eq_iff hB.ne').mpr
  have hprod := (eq_div_iff hL.ne').mp hsq
  field_simp
  nlinarith [hprod]

theorem sourceRegret_scale (m T L : ℝ) (hm : 0 < m) (hT : 0 < T) (hL : 0 < L) :
    2*sourceRadius m T L + m/sourceThreshold m T L =
      (2*Real.sqrt 2+7)*Real.sqrt (m*L/T) := by
  have hroot : Real.sqrt (2*m*L/T) = Real.sqrt 2 * Real.sqrt (m*L/T) := by
    rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
    congr 1
    ring
  unfold sourceRadius
  rw [sourceThreshold_bias_scale m T L hm hT hL, hroot]
  have hscale := sourceThreshold_scale m T L hm hT hL
  calc
    _ = 2*(Real.sqrt 2*Real.sqrt (m*L/T) + 3*(sourceThreshold m T L*L/T)) + Real.sqrt (m*L/T) := by ring
    _ = _ := by rw [hscale]; ring

theorem sourceLog_half_le (T K : ℕ) (hT : 0 < T) (hK : 0 < K) :
    (1:ℝ)/2 ≤ sourceLog T K := by
  have ht : (1:ℝ) ≤ T := by exact_mod_cast hT
  have hk : (1:ℝ) ≤ K := by exact_mod_cast hK
  have h2 : (1:ℝ)/2 ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < 2)
    norm_num at h ⊢
    exact h
  exact h2.trans (Real.log_le_log (by norm_num) (by nlinarith))

theorem sourceResidual_le_scale (m : ℝ) (hm : 1 ≤ m) (T K : ℕ)
    (hT : 0 < T) (hK : 0 < K) :
    1/(T:ℝ) ≤ Real.sqrt 2 * Real.sqrt (m*sourceLog T K/T) := by
  have ht : (1:ℝ) ≤ T := by exact_mod_cast hT
  have ht0 : (0:ℝ) < T := by exact_mod_cast hT
  have hl := sourceLog_half_le T K hT hK
  have hml : (1:ℝ)/2 ≤ m*sourceLog T K := by nlinarith
  have hprod : 1 ≤ 2*m*sourceLog T K*(T:ℝ) := by nlinarith
  have hs := Real.sq_sqrt (show 0 ≤ m*sourceLog T K/T by positivity)
  have hs2 : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have hsq : (Real.sqrt 2 * Real.sqrt (m*sourceLog T K/T) * (T:ℝ))^2 =
      2*m*sourceLog T K*(T:ℝ) := by
    rw [mul_pow, mul_pow, hs2, hs]
    field_simp
  apply (div_le_iff₀ ht0).mpr
  have hnon : 0 ≤ Real.sqrt 2 * Real.sqrt (m*sourceLog T K/T) * (T:ℝ) := by positivity
  nlinarith

end BanditRLProof.Causal
```

</details>

<details>
<summary>CausalConfidence - exact module</summary>

SHA256 (UTF-8, CRLF/bare-CR normalized to LF): `18b2b906701db662aca30477dcba9e6452b61981058fcf7f6a3a841ef18f37b9`

```lean
import BanditRLProof.Algorithms.CausalSampleMGF
import BanditRLProof.Algorithms.CausalTuning

/-! Source-tuned confidence for the actual fixed-budget intervention estimator. -/
namespace BanditRLProof.Causal
open scoped Classical
open MeasureTheory ProbabilityTheory
set_option autoImplicit false
set_option maxHeartbeats 800000

variable {A : Type*} [Fintype A] [Nonempty A]
variable [MeasurableSpace A] [MeasurableSingletonClass A] {n : ℕ}
variable {V : Type*} [Fintype V] [Inhabited V]
variable [MeasurableSpace V] [MeasurableSingletonClass V]

noncomputable def GraphModel.sampleEstimate (g : GraphModel V n) (rewardBit : V → Bool)
    (actions : A → Fin n → Option V) (eta : PMF A) (i : Fin n)
    (a : A) (B : ℝ) {T : ℕ} (w : Fin T → A × (Fin n → V)) : ℝ :=
  (∑ t : Fin T, g.sampleWeightedBit rewardBit actions eta i a B t w) / T

noncomputable def GraphModel.estimateCenter (g : GraphModel V n) (rewardBit : V → Bool)
    (actions : A → Fin n → Option V) (eta : PMF A) (i : Fin n) (a : A) (B : ℝ) : ℝ :=
  truncatedMean (g.parentLaw (actions a) i)
    (mixture eta (fun b => g.parentLaw (actions b) i))
    (fun z => mass ((g.parentTable i z).map rewardBit) true) B

omit [Fintype A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A] in
theorem GraphModel.sampleEstimate_centered_sum (g : GraphModel V n) (rewardBit : V → Bool)
    (actions : A → Fin n → Option V) (eta : PMF A) (i : Fin n)
    (a : A) (B c sign : ℝ) (T : ℕ) (hT : 0 < T)
    (w : Fin T → A × (Fin n → V)) :
    (∑ t : Fin T, sign*(g.sampleWeightedBit rewardBit actions eta i a B t w-c)) =
      (T:ℝ) * (sign*(g.sampleEstimate rewardBit actions eta i a B w-c)) := by
  have hT' : (T:ℝ) ≠ 0 := by exact_mod_cast hT.ne'
  simp only [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, sampleEstimate]
  field_simp

theorem GraphModel.sampleEstimate_signed_tail (g : GraphModel V n) (rewardBit : V → Bool)
    (actions : A → Fin n → Option V) (eta : PMF A)
    (i : Fin n) (hi : ∀ a, actions a i = none)
    (hc : Covers (fun a => g.parentLaw (actions a) i)
      (mixture eta (fun a => g.parentLaw (actions a) i)))
    (a : A) (T : ℕ) (hT : 0 < T) (L : ℝ) (hL : 0 < L)
    (sign : ℝ) (hs : |sign| = 1) :
    let m := designCost (fun b => g.parentLaw (actions b) i) eta
    let B := sourceThreshold m T L
    (g.sampleLaw actions eta T).real {w | sourceRadius m T L ≤
      sign*(g.sampleEstimate rewardBit actions eta i a B w-g.estimateCenter rewardBit actions eta i a B)} ≤
      Real.exp (-L) := by
  dsimp only
  let m := designCost (fun b => g.parentLaw (actions b) i) eta
  let B := sourceThreshold m T L
  have hm : 0 < m := lt_of_lt_of_le zero_lt_one (designCost_ge_one _ eta hc)
  have hT' : (0:ℝ) < T := by exact_mod_cast hT
  have hB : 0 < B := sourceThreshold_pos m T L hm hT' hL
  have h := g.sampleWeightedBit_signed_sum_tail rewardBit actions eta i hi hc a B hB.le T
    sign (1/(2*B)) ((T:ℝ)*sourceRadius m T L) hs (by positivity)
    (sourceTilt_admissible m T L hm hT' hL)
  simp_rw [g.sampleEstimate_centered_sum rewardBit actions eta i a B _ sign T hT] at h
  have hevent : {w : Fin T → A × (Fin n → V) | (T:ℝ)*sourceRadius m T L ≤
      (T:ℝ)*(sign*(g.sampleEstimate rewardBit actions eta i a B w-g.estimateCenter rewardBit actions eta i a B))} =
      {w | sourceRadius m T L ≤
        sign*(g.sampleEstimate rewardBit actions eta i a B w-g.estimateCenter rewardBit actions eta i a B)} := by
    ext w
    simp only [Set.mem_setOf_eq, mul_le_mul_iff_right₀ hT']
  change (g.sampleLaw actions eta T).real {w | sourceRadius m T L ≤
    sign*(g.sampleEstimate rewardBit actions eta i a B w-g.estimateCenter rewardBit actions eta i a B)} ≤ _
  change (g.sampleLaw actions eta T).real {w | (T:ℝ)*sourceRadius m T L ≤
    (T:ℝ)*(sign*(g.sampleEstimate rewardBit actions eta i a B w-g.estimateCenter rewardBit actions eta i a B))} ≤ _ at h
  rw [hevent] at h
  exact h.trans (Real.exp_le_exp.mpr (sourceTilt_exponent_le m T L hm hT' hL))

theorem GraphModel.sampleEstimate_abs_tail (g : GraphModel V n) (rewardBit : V → Bool)
    (actions : A → Fin n → Option V) (eta : PMF A)
    (i : Fin n) (hi : ∀ a, actions a i = none)
    (hc : Covers (fun a => g.parentLaw (actions a) i)
      (mixture eta (fun a => g.parentLaw (actions a) i)))
    (a : A) (T : ℕ) (hT : 0 < T) (L : ℝ) (hL : 0 < L) :
    let m := designCost (fun b => g.parentLaw (actions b) i) eta
    let B := sourceThreshold m T L
    (g.sampleLaw actions eta T).real {w | sourceRadius m T L ≤
      |g.sampleEstimate rewardBit actions eta i a B w-g.estimateCenter rewardBit actions eta i a B|} ≤
      2*Real.exp (-L) := by
  dsimp only
  let m := designCost (fun b => g.parentLaw (actions b) i) eta
  let B := sourceThreshold m T L
  let X := fun w : Fin T → A × (Fin n → V) =>
    g.sampleEstimate rewardBit actions eta i a B w-g.estimateCenter rewardBit actions eta i a B
  have hp := g.sampleEstimate_signed_tail rewardBit actions eta i hi hc a T hT L hL 1 (by norm_num)
  have hn := g.sampleEstimate_signed_tail rewardBit actions eta i hi hc a T hT L hL (-1) (by norm_num)
  change (g.sampleLaw actions eta T).real {w | sourceRadius m T L ≤ |X w|} ≤ _
  calc
    _ ≤ (g.sampleLaw actions eta T).real
      ({w | sourceRadius m T L ≤ X w} ∪ {w | sourceRadius m T L ≤ -X w}) := by
      apply measureReal_mono _ (by finiteness)
      intro w hw
      rcases le_total (X w) 0 with hx | hx
      · exact Or.inr (by simpa only [Set.mem_setOf_eq, abs_of_nonpos hx] using hw)
      · exact Or.inl (by simpa only [Set.mem_setOf_eq, abs_of_nonneg hx] using hw)
    _ ≤ (g.sampleLaw actions eta T).real {w | sourceRadius m T L ≤ X w} +
      (g.sampleLaw actions eta T).real {w | sourceRadius m T L ≤ -X w} := measureReal_union_le _ _
    _ ≤ 2*Real.exp (-L) := by
      simp only [one_mul, neg_one_mul] at hp hn
      linarith

theorem GraphModel.sampleEstimate_simultaneous_tail (g : GraphModel V n) (rewardBit : V → Bool)
    (actions : A → Fin n → Option V) (eta : PMF A)
    (i : Fin n) (hi : ∀ a, actions a i = none)
    (hc : Covers (fun a => g.parentLaw (actions a) i)
      (mixture eta (fun a => g.parentLaw (actions a) i)))
    (T : ℕ) (hT : 0 < T) (L : ℝ) (hL : 0 < L) :
    let m := designCost (fun b => g.parentLaw (actions b) i) eta
    let B := sourceThreshold m T L
    (g.sampleLaw actions eta T).real {w | ∃ a : A, sourceRadius m T L ≤
      |g.sampleEstimate rewardBit actions eta i a B w-g.estimateCenter rewardBit actions eta i a B|} ≤
      (Fintype.card A:ℝ) * (2*Real.exp (-L)) := by
  dsimp only
  rw [show {w | ∃ a : A, sourceRadius (designCost (fun b => g.parentLaw (actions b) i) eta) T L ≤
      |g.sampleEstimate rewardBit actions eta i a (sourceThreshold (designCost (fun b => g.parentLaw (actions b) i) eta) T L) w-
       g.estimateCenter rewardBit actions eta i a (sourceThreshold (designCost (fun b => g.parentLaw (actions b) i) eta) T L)|} =
    ⋃ a : A, {w | sourceRadius (designCost (fun b => g.parentLaw (actions b) i) eta) T L ≤
      |g.sampleEstimate rewardBit actions eta i a (sourceThreshold (designCost (fun b => g.parentLaw (actions b) i) eta) T L) w-
       g.estimateCenter rewardBit actions eta i a (sourceThreshold (designCost (fun b => g.parentLaw (actions b) i) eta) T L)|}
    by ext w; simp]
  refine (measureReal_iUnion_fintype_le _).trans ?_
  calc
    _ ≤ ∑ _a : A, 2*Real.exp (-L) := Finset.sum_le_sum fun a _ =>
      g.sampleEstimate_abs_tail rewardBit actions eta i hi hc a T hT L hL
    _ = _ := by simp [nsmul_eq_mul]

theorem GraphModel.sampleEstimate_source_confidence (g : GraphModel V n) (rewardBit : V → Bool)
    (actions : A → Fin n → Option V) (eta : PMF A)
    (i : Fin n) (hi : ∀ a, actions a i = none)
    (hc : Covers (fun a => g.parentLaw (actions a) i)
      (mixture eta (fun a => g.parentLaw (actions a) i)))
    (T : ℕ) (hT : 0 < T) :
    let m := designCost (fun b => g.parentLaw (actions b) i) eta
    let L := sourceLog T (Fintype.card A)
    let B := sourceThreshold m T L
    (g.sampleLaw actions eta T).real {w | ∃ a : A, sourceRadius m T L ≤
      |g.sampleEstimate rewardBit actions eta i a B w-g.estimateCenter rewardBit actions eta i a B|} ≤
      1/(T:ℝ) := by
  have h := g.sampleEstimate_simultaneous_tail rewardBit actions eta i hi hc T hT
    (sourceLog T (Fintype.card A)) (sourceLog_pos T _ hT Fintype.card_pos)
  simpa only [sourceLog_union_budget T _ hT Fintype.card_pos] using h

end BanditRLProof.Causal
```

</details>

<details>
<summary>CausalRecommendation - exact module</summary>

SHA256 (UTF-8, CRLF/bare-CR normalized to LF): `165acdcfeca542cdb1c6abcfa3097c335c1c07f5efccc1b82299ed2731b1c4a8`

```lean
import BanditRLProof.Algorithms.CausalConfidence
import BanditRLProof.FiniteRealArgmax

/-! A fixed-order recommendation from observed estimates and its pathwise regret bound. -/
namespace BanditRLProof.Causal
open scoped Classical
open MeasureTheory
set_option autoImplicit false
set_option maxHeartbeats 800000

variable {A : Type*} [Fintype A] [Nonempty A] [LinearOrder A]
variable [MeasurableSpace A] [MeasurableSingletonClass A] {n : ℕ}
variable {V : Type*} [Fintype V] [Inhabited V]
variable [MeasurableSpace V] [MeasurableSingletonClass V]

noncomputable def maximizingActions (score : A → ℝ) : Finset A :=
  Finset.univ.filter (fun a => score a = score (FiniteRealArgmax.choose score))

theorem maximizingActions_nonempty (score : A → ℝ) : (maximizingActions score).Nonempty := by
  refine ⟨FiniteRealArgmax.choose score, ?_⟩
  simp [maximizingActions]

noncomputable def orderedArgmax (score : A → ℝ) : A :=
  (maximizingActions score).min' (maximizingActions_nonempty score)

theorem score_le_orderedArgmax (score : A → ℝ) (a : A) :
    score a ≤ score (orderedArgmax score) := by
  have h := Finset.min'_mem (maximizingActions score) (maximizingActions_nonempty score)
  have heq : score (orderedArgmax score) = score (FiniteRealArgmax.choose score) := by
    simpa only [maximizingActions, Finset.mem_filter, Finset.mem_univ, true_and] using h
  rw [heq]
  exact FiniteRealArgmax.score_le_choose score a

theorem orderedArgmax_le_of_maximal (score : A → ℝ) (a : A)
    (ha : ∀ b, score b ≤ score a) : orderedArgmax score ≤ a := by
  apply Finset.min'_le
  simp only [maximizingActions, Finset.mem_filter, Finset.mem_univ, true_and]
  exact le_antisymm (FiniteRealArgmax.score_le_choose score a) (ha _)

noncomputable def GraphModel.rewardMean (g : GraphModel V n) (rewardBit : V → Bool)
    (actions : A → Fin n → Option V) (i : Fin n) (a : A) : ℝ :=
  ∑ z, mass (g.parentLaw (actions a) i) z * mass ((g.parentTable i z).map rewardBit) true

theorem GraphModel.rewardMean_eq_integral (g : GraphModel V n) (rewardBit : V → Bool)
    (actions : A → Fin n → Option V) (i : Fin n) (a : A) (hi : actions a i = none) :
    g.rewardMean rewardBit actions i a =
      ∫ x, (if rewardBit (x i) then (1:ℝ) else 0) ∂(joint (g.doModel (actions a)).table).toMeasure := by
  let proj := fun x : Fin n → V => (g.parentConfig i (history x i), rewardBit (x i))
  let f := fun zy : g.ParentConfig i × Bool => if zy.2 then (1:ℝ) else 0
  have hmap : (joint (g.doModel (actions a)).table).toMeasure.map proj =
      (pairedLaw (g.parentLaw (actions a) i) (fun z => (g.parentTable i z).map rewardBit)).toMeasure := by
    rw [PMF.toMeasure_map proj _ Measurable.of_discrete]
    apply congrArg PMF.toMeasure
    have h := congrArg (fun p : PMF (g.ParentConfig i × V) =>
      p.map (fun zy => (zy.1, rewardBit zy.2)))
      (g.intervention_parent_joint (actions a) i hi)
    simpa only [PMF.map_bind, PMF.map_comp, Function.comp_def, pairedLaw, proj] using h
  have hint := integral_map (μ := (joint (g.doModel (actions a)).table).toMeasure)
    (φ := proj) (f := f) Measurable.of_discrete.aemeasurable
    Measurable.of_discrete.aestronglyMeasurable
  rw [hmap, PMF.integral_eq_sum] at hint
  have hsum : (∑ zy, ((pairedLaw (g.parentLaw (actions a) i) (fun z => (g.parentTable i z).map rewardBit)) zy).toReal • f zy) =
      g.rewardMean rewardBit actions i a := by
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, f, Bool.false_eq_true,
      if_false, Bool.true_eq, if_true, smul_eq_mul, mul_one, mul_zero, add_zero]
    change (∑ z, mass (pairedLaw (g.parentLaw (actions a) i) (fun z => (g.parentTable i z).map rewardBit)) (z,true)) = _
    simp only [pairedLaw_mass, rewardMean]
  rw [hsum] at hint
  exact hint

theorem GraphModel.rewardMean_bounds (g : GraphModel V n) (rewardBit : V → Bool)
    (actions : A → Fin n → Option V) (i : Fin n) (a : A) :
    0 ≤ g.rewardMean rewardBit actions i a ∧ g.rewardMean rewardBit actions i a ≤ 1 := by
  constructor
  · exact Finset.sum_nonneg fun z _ => mul_nonneg (mass_nonneg _ _) (mass_nonneg _ _)
  · calc
      _ ≤ ∑ z, mass (g.parentLaw (actions a) i) z := by
        apply Finset.sum_le_sum
        intro z _
        exact mul_le_of_le_one_right (mass_nonneg _ _) (mass_le_one _ _)
      _ = 1 := sum_mass _

noncomputable def GraphModel.sampleRecommendation (g : GraphModel V n) (rewardBit : V → Bool)
    (actions : A → Fin n → Option V) (eta : PMF A) (i : Fin n)
    (B : ℝ) {T : ℕ} (w : Fin T → A × (Fin n → V)) : A :=
  orderedArgmax (fun a => g.sampleEstimate rewardBit actions eta i a B w)

noncomputable def GraphModel.simpleRegret (g : GraphModel V n) (rewardBit : V → Bool)
    (actions : A → Fin n → Option V) (eta : PMF A) (i : Fin n)
    (B : ℝ) {T : ℕ} (w : Fin T → A × (Fin n → V)) : ℝ :=
  g.rewardMean rewardBit actions i (FiniteRealArgmax.choose (g.rewardMean rewardBit actions i)) -
    g.rewardMean rewardBit actions i (g.sampleRecommendation rewardBit actions eta i B w)

theorem GraphModel.simpleRegret_bounds (g : GraphModel V n) (rewardBit : V → Bool)
    (actions : A → Fin n → Option V) (eta : PMF A) (i : Fin n)
    (B : ℝ) {T : ℕ} (w : Fin T → A × (Fin n → V)) :
    0 ≤ g.simpleRegret rewardBit actions eta i B w ∧ g.simpleRegret rewardBit actions eta i B w ≤ 1 := by
  constructor
  · exact sub_nonneg.mpr (FiniteRealArgmax.score_le_choose (g.rewardMean rewardBit actions i) _)
  · have hb := g.rewardMean_bounds rewardBit actions i (FiniteRealArgmax.choose (g.rewardMean rewardBit actions i))
    have hr := g.rewardMean_bounds rewardBit actions i (g.sampleRecommendation rewardBit actions eta i B w)
    unfold simpleRegret
    linarith

theorem GraphModel.simpleRegret_le_on_confidence (g : GraphModel V n) (rewardBit : V → Bool)
    (actions : A → Fin n → Option V) (eta : PMF A) (i : Fin n)
    (hc : Covers (fun a => g.parentLaw (actions a) i)
      (mixture eta (fun a => g.parentLaw (actions a) i)))
    (B : ℝ) (hB : 0 < B) (epsilon : ℝ) {T : ℕ}
    (w : Fin T → A × (Fin n → V))
    (hw : ∀ a, |g.sampleEstimate rewardBit actions eta i a B w-g.estimateCenter rewardBit actions eta i a B| ≤ epsilon) :
    g.simpleRegret rewardBit actions eta i B w ≤
      2*epsilon + designCost (fun a => g.parentLaw (actions a) i) eta / B := by
  let best := FiniteRealArgmax.choose (g.rewardMean rewardBit actions i)
  let chosen := g.sampleRecommendation rewardBit actions eta i B w
  have hbest := (abs_le.mp (hw best)).1
  have hrec := (abs_le.mp (hw chosen)).2
  have hmax : g.sampleEstimate rewardBit actions eta i best B w ≤ g.sampleEstimate rewardBit actions eta i chosen B w :=
    score_le_orderedArgmax (fun a => g.sampleEstimate rewardBit actions eta i a B w) best
  have hmean (a : A) : g.estimateCenter rewardBit actions eta i a B +
      truncationBias (g.parentLaw (actions a) i)
        (mixture eta (fun a => g.parentLaw (actions a) i))
        (fun z => mass ((g.parentTable i z).map rewardBit) true) B = g.rewardMean rewardBit actions i a :=
    truncatedMean_add_bias (fun a => g.parentLaw (actions a) i) _ hc a _ B
  have hb0 := truncationBias_nonneg (g.parentLaw (actions chosen) i)
    (mixture eta (fun a => g.parentLaw (actions a) i))
    (fun z => mass ((g.parentTable i z).map rewardBit) true) (fun z => mass_nonneg _ _) B
  have hb := (truncationBias_le (g.parentLaw (actions best) i)
    (mixture eta (fun a => g.parentLaw (actions a) i))
    (fun z => mass ((g.parentTable i z).map rewardBit) true) (fun z => mass_le_one _ _) B hB).trans
    (div_le_div_of_nonneg_right
      (secondMoment_le_designCost (fun a => g.parentLaw (actions a) i) eta best) hB.le)
  have hmb := hmean best
  have hmr := hmean chosen
  change g.rewardMean rewardBit actions i best - g.rewardMean rewardBit actions i chosen ≤ _
  linarith

end BanditRLProof.Causal
```

</details>

<details>
<summary>CausalExpectedRegret - exact module</summary>

SHA256 (UTF-8, CRLF/bare-CR normalized to LF): `0eecb128db14117d39c598f7a4dd78b8753f28f4242d8ababb7aec98cddd13d3`

```lean
import BanditRLProof.Algorithms.CausalRecommendation

/-! Expected simple regret of the actual intervention sampler and recommendation.
The finite-budget residual is retained explicitly. -/
namespace BanditRLProof.Causal
open scoped Classical
open MeasureTheory ProbabilityTheory
set_option autoImplicit false
set_option maxHeartbeats 800000

variable {A : Type*} [Fintype A] [Nonempty A] [LinearOrder A]
variable [MeasurableSpace A] [MeasurableSingletonClass A] {n : ℕ}
variable {V : Type*} [Fintype V] [Inhabited V]
variable [MeasurableSpace V] [MeasurableSingletonClass V]

theorem GraphModel.expected_simpleRegret_le_tuned (g : GraphModel V n)
    (rewardBit : V → Bool) (actions : A → Fin n → Option V) (eta : PMF A)
    (i : Fin n) (hi : ∀ a, actions a i = none)
    (hc : Covers (fun a => g.parentLaw (actions a) i)
      (mixture eta (fun a => g.parentLaw (actions a) i)))
    (T : ℕ) (hT : 0 < T) :
    let m := designCost (fun a => g.parentLaw (actions a) i) eta
    let L := sourceLog T (Fintype.card A)
    let B := sourceThreshold m T L
    (∫ w, g.simpleRegret rewardBit actions eta i B w ∂g.sampleLaw actions eta T) ≤
      2*sourceRadius m T L + m/B + 1/(T:ℝ) := by
  dsimp only
  let m := designCost (fun a => g.parentLaw (actions a) i) eta
  let L := sourceLog T (Fintype.card A)
  let B := sourceThreshold m T L
  let eps := sourceRadius m T L
  let C := 2*eps+m/B
  let bad : Set (Fin T → A × (Fin n → V)) :=
    {w | ∃ a : A, eps ≤ |g.sampleEstimate rewardBit actions eta i a B w -
      g.estimateCenter rewardBit actions eta i a B|}
  have hm : 0 < m := lt_of_lt_of_le zero_lt_one (designCost_ge_one _ eta hc)
  have ht : (0:ℝ) < T := by exact_mod_cast hT
  have hL : 0 < L := sourceLog_pos T _ hT Fintype.card_pos
  have hB : 0 < B := sourceThreshold_pos m T L hm ht hL
  have heps : 0 ≤ eps := by
    dsimp [eps, sourceRadius]
    positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hbad : MeasurableSet bad := Set.to_countable _ |>.measurableSet
  have hpoint (w : Fin T → A × (Fin n → V)) :
      g.simpleRegret rewardBit actions eta i B w ≤ C + bad.indicator (fun _ => (1:ℝ)) w := by
    by_cases hw : w ∈ bad
    · rw [Set.indicator_of_mem hw]
      exact (g.simpleRegret_bounds rewardBit actions eta i B w).2.trans (by linarith)
    · rw [Set.indicator_of_notMem hw, add_zero]
      apply g.simpleRegret_le_on_confidence rewardBit actions eta i hc B hB eps w
      intro a
      exact (lt_of_not_ge (fun ha => hw ⟨a,ha⟩)).le
  have h := integral_mono (μ := g.sampleLaw actions eta T)
    (Integrable.of_finite) (Integrable.of_finite) hpoint
  rw [integral_add (integrable_const C) (Integrable.of_finite),
    integral_const, integral_indicator_const (1:ℝ) hbad] at h
  simp only [probReal_univ, smul_eq_mul, mul_one, one_mul] at h
  have hp := g.sampleEstimate_source_confidence rewardBit actions eta i hi hc T hT
  change (g.sampleLaw actions eta T).real bad ≤ 1/(T:ℝ) at hp
  exact h.trans (add_le_add le_rfl hp)

theorem GraphModel.expected_simpleRegret_bounds (g : GraphModel V n)
    (rewardBit : V → Bool) (actions : A → Fin n → Option V) (eta : PMF A)
    (i : Fin n) (B : ℝ) (T : ℕ) :
    0 ≤ (∫ w, g.simpleRegret rewardBit actions eta i B w ∂g.sampleLaw actions eta T) ∧
    (∫ w, g.simpleRegret rewardBit actions eta i B w ∂g.sampleLaw actions eta T) ≤ 1 := by
  constructor
  · exact integral_nonneg fun w => (g.simpleRegret_bounds rewardBit actions eta i B w).1
  · have h := integral_mono (μ := g.sampleLaw actions eta T)
      (Integrable.of_finite) (integrable_const (1:ℝ))
      (fun w => (g.simpleRegret_bounds rewardBit actions eta i B w).2)
    simpa using h

theorem GraphModel.expected_simpleRegret_source_bound (g : GraphModel V n)
    (rewardBit : V → Bool) (actions : A → Fin n → Option V) (eta : PMF A)
    (i : Fin n) (hi : ∀ a, actions a i = none)
    (hc : Covers (fun a => g.parentLaw (actions a) i)
      (mixture eta (fun a => g.parentLaw (actions a) i)))
    (T : ℕ) (hT : 0 < T) :
    let m := designCost (fun a => g.parentLaw (actions a) i) eta
    let L := sourceLog T (Fintype.card A)
    let B := sourceThreshold m T L
    (∫ w, g.simpleRegret rewardBit actions eta i B w ∂g.sampleLaw actions eta T) ≤
      (2*Real.sqrt 2+7)*Real.sqrt (m*L/T) + 1/(T:ℝ) := by
  have hm : 0 < designCost (fun a => g.parentLaw (actions a) i) eta :=
    lt_of_lt_of_le zero_lt_one (designCost_ge_one _ eta hc)
  have h := g.expected_simpleRegret_le_tuned rewardBit actions eta i hi hc T hT
  dsimp only at h ⊢
  rw [sourceRegret_scale _ _ _ hm (by exact_mod_cast hT)
    (sourceLog_pos T _ hT Fintype.card_pos)] at h
  exact h

theorem GraphModel.expected_simpleRegret_explicit_rate (g : GraphModel V n)
    (rewardBit : V → Bool) (actions : A → Fin n → Option V) (eta : PMF A)
    (i : Fin n) (hi : ∀ a, actions a i = none)
    (hc : Covers (fun a => g.parentLaw (actions a) i)
      (mixture eta (fun a => g.parentLaw (actions a) i)))
    (T : ℕ) (hT : 0 < T) :
    let m := designCost (fun a => g.parentLaw (actions a) i) eta
    let L := sourceLog T (Fintype.card A)
    let B := sourceThreshold m T L
    (∫ w, g.simpleRegret rewardBit actions eta i B w ∂g.sampleLaw actions eta T) ≤
      (3*Real.sqrt 2+7)*Real.sqrt (m*L/T) := by
  have h := g.expected_simpleRegret_source_bound rewardBit actions eta i hi hc T hT
  have hr := sourceResidual_le_scale _ (designCost_ge_one _ eta hc)
    T (Fintype.card A) hT Fintype.card_pos
  dsimp only at h ⊢
  linarith

end BanditRLProof.Causal
```

</details>

<details>
<summary>CausalAllocationRegret - exact module</summary>

SHA256 (UTF-8, CRLF/bare-CR normalized to LF): `95fd37703b483324520d91dd9810943687e55f91426027fb22ec53019fc76c6b`

```lean
import BanditRLProof.Algorithms.CausalExpectedRegret

/-! The actual learner under uniform and attained optimal covered allocations. -/
namespace BanditRLProof.Causal
open MeasureTheory ProbabilityTheory
set_option autoImplicit false

variable {A : Type*} [Fintype A] [Nonempty A] [LinearOrder A]
variable [MeasurableSpace A] [MeasurableSingletonClass A] {n : ℕ}
variable {V : Type*} [Fintype V] [Inhabited V]
variable [MeasurableSpace V] [MeasurableSingletonClass V]

theorem GraphModel.expected_simpleRegret_uniform (g : GraphModel V n)
    (rewardBit : V → Bool) (actions : A → Fin n → Option V)
    (i : Fin n) (hi : ∀ a, actions a i = none) (T : ℕ) (hT : 0 < T) :
    let eta := PMF.uniformOfFintype A
    let m := designCost (fun a => g.parentLaw (actions a) i) eta
    let L := sourceLog T (Fintype.card A)
    let B := sourceThreshold m T L
    (∫ w, g.simpleRegret rewardBit actions eta i B w ∂g.sampleLaw actions eta T) ≤
      (2*Real.sqrt 2+7)*Real.sqrt ((Fintype.card A:ℝ)*L/T) + 1/(T:ℝ) := by
  have h := g.expected_simpleRegret_source_bound rewardBit actions
    (PMF.uniformOfFintype A) i hi (uniform_covers _) T hT
  dsimp only at h ⊢
  refine h.trans (add_le_add ?_ le_rfl)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.sqrt_le_sqrt
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_right (uniform_designCost_le_card _)
    (sourceLog_pos T _ hT Fintype.card_pos).le

theorem GraphModel.expected_simpleRegret_optimal (g : GraphModel V n)
    (rewardBit : V → Bool) (actions : A → Fin n → Option V)
    (i : Fin n) (hi : ∀ a, actions a i = none) (T : ℕ) (hT : 0 < T) :
    let p := fun a => g.parentLaw (actions a) i
    let eta := optimalAllocation p
    let m := designCost p eta
    let L := sourceLog T (Fintype.card A)
    let B := sourceThreshold m T L
    (∫ w, g.simpleRegret rewardBit actions eta i B w ∂g.sampleLaw actions eta T) ≤
      (2*Real.sqrt 2+7)*Real.sqrt (m*L/T) + 1/(T:ℝ) :=
  g.expected_simpleRegret_source_bound rewardBit actions _ i hi
    (optimalAllocation_covers _) T hT

end BanditRLProof.Causal
```

</details>

<details>
<summary>Concrete partial canary - exact test module</summary>

SHA256: `a28badd553cfde40081b51888f9a0864c7609667dc552a6a01703cfec2bcdbb9`

```lean
import BanditRLProof.Algorithms.CausalAllocationRegret

/-! Frozen noisy X -> W, X -> Y, W -> Y graph. This file begins the concrete
canary; exact tuned one-round regret and design arithmetic remain obligations. -/
namespace Tests.CausalNoisyGraphCanary
open BanditRLProof.Causal MeasureTheory
open scoped Classical
set_option maxHeartbeats 800000

noncomputable def xLaw : PMF Bool := PMF.bernoulli (1/2) (by norm_num)

noncomputable def wLaw (x : Bool) : PMF Bool :=
  PMF.bernoulli (if x then 3/4 else 1/4) (by cases x <;> norm_num [div_le_iff₀])

noncomputable def yLaw (x w : Bool) : PMF Bool :=
  PMF.bernoulli (if x then (if w then 4/5 else 2/5) else (if w then 3/5 else 1/5))
    (by cases x <;> cases w <;> norm_num [div_le_iff₀])

noncomputable def noisyTables : Tables Bool 3 := fun i h =>
  if hi : i = 0 then xLaw
  else if hi1 : i = 1 then wLaw (h ⟨0, by omega⟩)
  else yLaw (h ⟨0, by omega⟩) (h ⟨1, by omega⟩)

noncomputable def noisyGraph : GraphModel Bool 3 where
  parents _ := Finset.univ
  table := noisyTables
  local_table := by
    intro i h h' heq
    have hh : h = h' := funext fun j => heq j (Finset.mem_univ _)
    rw [hh]

/-- The empty intervention is first in the fixed tie order. -/
def actions (a : Fin 3) (i : Fin 3) : Option Bool :=
  if i = 1 then (if a = 0 then none else some (a = 2)) else none

theorem reward_not_intervened (a : Fin 3) : actions a 2 = none := by
  simp [actions]

theorem actual_joint_factorization (a : Fin 3) (x : Fin 3 → Bool) :
    joint (noisyGraph.doModel (actions a)).table x =
      xLaw (x 0) *
        (if a = 0 then wLaw (x 0) (x 1) else if x 1 = (a = 2) then 1 else 0) *
        yLaw (x 0) (x 1) (x 2) := by
  rw [doModel_factorization]
  fin_cases a <;> simp [Fin.prod_univ_succ, actions, noisyGraph, noisyTables, history]
  <;> ring

def assignmentEquiv : (Fin 3 → Bool) ≃ Bool × Bool × Bool where
  toFun x := (x 0, x 1, x 2)
  invFun s := ![s.1,s.2.1,s.2.2]
  left_inv x := by funext i; fin_cases i <;> rfl
  right_inv s := by rcases s with ⟨x,w,y⟩; rfl

theorem reward_means (a : Fin 3) : noisyGraph.rewardMean id actions 2 a =
    if a = 0 then 1/2 else if a = 1 then 3/10 else 7/10 := by
  rw [noisyGraph.rewardMean_eq_integral id actions 2 a (reward_not_intervened a),
    PMF.integral_eq_sum]
  rw [← Equiv.sum_comp assignmentEquiv.symm]
  fin_cases a <;>
    norm_num [Fintype.sum_prod_type, Fintype.sum_bool, assignmentEquiv,
      actual_joint_factorization, xLaw, wLaw, yLaw, PMF.bernoulli_apply,
      smul_eq_mul, ENNReal.toReal_mul, Matrix.cons_val, Fin.reduceFinMk,
      NNReal.coe_sub] <;>
    norm_num [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
      Matrix.cons_val_zero, Matrix.cons_val_one, Fin.ext_iff, NNReal.coe_sub,
      ENNReal.toReal_mul] <;>
    rw [show (1 - 3/4 : NNReal) = 1/4 by
          apply Subtype.ext
          norm_num [NNReal.coe_sub_def],
        show (1 - 1/4 : NNReal) = 3/4 by
          apply Subtype.ext
          norm_num [NNReal.coe_sub_def]]
  norm_num

theorem uniform_actual_rate (T : ℕ) (hT : 0 < T) :
    let eta := PMF.uniformOfFintype (Fin 3)
    let m := designCost (fun a => noisyGraph.parentLaw (actions a) 2) eta
    let L := sourceLog T 3
    let B := sourceThreshold m T L
    (∫ w, noisyGraph.simpleRegret id actions eta 2 B w ∂noisyGraph.sampleLaw actions eta T) ≤
      (2*Real.sqrt 2+7)*Real.sqrt (3*L/T)+1/(T:ℝ) := by
  simpa only [Fintype.card_fin] using
    noisyGraph.expected_simpleRegret_uniform id actions 2 reward_not_intervened T hT

#print axioms actual_joint_factorization
#print axioms reward_means
#print axioms uniform_actual_rate
#print axioms GraphModel.expected_simpleRegret_source_bound
#print axioms GraphModel.expected_simpleRegret_explicit_rate

end Tests.CausalNoisyGraphCanary
```

</details>
