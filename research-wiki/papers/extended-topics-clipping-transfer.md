# Clipped-prefix transfer under a consumed-sample corruption budget

This is the explicitly reserved TRANSFER-CLIP adaptation in
`docs/extended-topics/PROTOCOL.md`, frozen at commit 5cbbe67 before implementation.
It is a library transfer case, not a theorem attributed to BCL13 or a published
corruption-robust bandit algorithm. The clean estimator changes from hard
deletion to clipping; the policy guarantee is outside this contract.

## Objects, assumptions and exact claim

Write $p=1+\epsilon$, $0\le\epsilon\le1$, $u>0$, and
$\operatorname{clip}_B(x)=\max(-B,\min(B,x))$. Independent measurable real
coordinates $X_s$ have a common mean $m$ and integrable raw $p$ moments bounded
by $u$. They need not be identically distributed. Define

\[
 L_t=4\log(\max(t,2)),\qquad
 B_{t,s}=\left(\frac{u(s+1)}{L_t}\right)^{1/p},\qquad
 r_{t,n}=8u^{1/p}(L_t/n)^{\epsilon/p}.
\]

The count $N(\omega)$ and perturbations $c_s(\omega)$ may depend on the entire
outcome and need not be measurable. A deterministic $C$ bounds every consumed
prefix: $\sum_{s<N(\omega)}|c_s(\omega)|\le C$ for every outcome. Then

\[
 \mu^*\left\{0<N\le t,\quad
 \left|\frac1N\sum_{s<N}\operatorname{clip}_{B_{t,s}}(X_s+c_s)-m\right|
 \ge r_{t,N}+\frac C N\right\}
 \le 2t e^{-L_t}.
\]

Here $\mu^*$ is finite outer measure, expressed in Lean as `Measure.real`.
For a measurable event it equals its probability. No stopping-time condition,
conditional IID assertion at $N$, clean-confidence premise, or adversary
measurability assumption is hidden. The clean coordinates themselves remain
independent: arbitrary dependence is permitted only in the count and corruption.
The endpoint derives first moments from the raw moment hypotheses.

## Mathematical derivation and actual reuse

Clipping is 1-Lipschitz, including across its boundary. Thus pointwise

\[
 |\operatorname{clip}_{B_s}(X_s+c_s)-\operatorname{clip}_{B_s}(X_s)|\le|c_s|,
 \qquad |\widehat m^{\rm corrupt}_n-\widehat m^{\rm clean}_n|\le C/n.
\]

The moment producers separately prove
$|X-\operatorname{clip}_B(X)|\le |X|^p/B^\epsilon$ and
$\operatorname{clip}_B(X)^2\le |X|^p B^{1-\epsilon}$. Integration gives bias
and second-moment bounds. The shared bounded-centering MGF and sum-tail
interfaces produce signed concentration; the triangle inequality and threshold
power-sum tuning give the clean fixed-prefix radius above. A union over the
$t$ deterministic positive lengths covers any $N\le t$, without claiming that
an adaptively selected sample size is independent of its observations.
Finally the corruption inequality implies that the displayed corrupted bad
event is contained in the clean bad event.

`observed_corrupted_clipped_mean_tail` reindexes actual selected observations
using `clipped_observed_prefix`. Clean and corrupted observations are compared
on the **same action trace**. The theorem may be applied to a trace driven by
corrupted observations, but it does not compare actions of clean and corrupted
runs of a policy. The stationary-product-arm version supplies coordinate
independence and moments from actual arm laws.

The compiled five-module graph records direct proof references, including the
terminal's calls to `scheduled_adaptive_clipped_mean_tail` and
`clipped_prefix_corruption_le`. Reuse evidence is in
`runs/extended-topics-20260919/clipping-reuse.json`. Its scope is direct references
from those modules with complete boundary nodes, not whole-library transitive
closure. There are no controlled runs or efficiency-effect estimates.

## Boundary cases and validation scope

At $t=0$ the positive-count event is empty. Zero counts are excluded from the
probability claim; Lean's totalized division does not create a statistical
zero-sample estimator. At $\epsilon=0$ the bound is valid but does not assert
shrinking confidence. Negative rewards are allowed; centered moment bounds
cannot replace raw moment bounds. The budget concerns the consumed prefix,
not all unobserved corruption coordinates.

The original noisy $N\in\{1,2\}$ canary has an empty bad event because its radius
is too wide. It remains a contract-assembly test, alongside an exact nonzero
boundary-crossing clipping calculation. The new named `long_corrupted_prefix`
uses the same noisy 0/2 arm, an outcome-dependent count9999 or10000, corruption
1/20000 on every consumed sample, and budget1. At t10000 the radius is about
0.687 and the failure bound is $2\times10^{-12}$; a finite all-zero clean prefix
has error near1. These numerical checks explain the stronger canary's scale;
they are not empirical coverage experiments or additional Lean conclusions.

Independent decoder/specification and proof reviews are recorded separately
from compilation. No corruption-robust regret, changed-policy coupling,
heavy-tailed topic completion, or all-ten ICLR evaluation is established here.

## Exact public endpoint and proof

<details><summary>Lean: raw moments to corrupted adaptive clipped confidence</summary>

```lean
import BanditRLProof.HeavyTailClippedScheduled
import BanditRLProof.HeavyTailArmLaw

/-! Raw-moment confidence under a pathwise corruption budget on the consumed
prefix. The count and corruption may depend on the entire outcome. -/
namespace BanditRLProof.HeavyTail
open MeasureTheory ProbabilityTheory

theorem integrable_of_raw_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (ε : ℝ)
    (hXm : Measurable X) (hε : 0 ≤ ε)
    (hm : Integrable (fun ω => |X ω|^(1+ε)) μ) : Integrable X μ := by
  apply ((integrable_const (1 : ℝ)).add hm).mono' hXm.aestronglyMeasurable
  exact ae_of_all _ fun ω => by
    change |X ω| ≤ 1 + |X ω|^(1+ε)
    by_cases hx : |X ω| ≤ 1
    · have hp := Real.rpow_nonneg (abs_nonneg (X ω)) (1+ε)
      linarith
    · have hp := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hx)
        (show (1 : ℝ) ≤ 1+ε by linarith)
      rw [Real.rpow_one] at hp
      linarith

/-- No clean-confidence or fluctuation premise: these are produced from the
independent raw-moment stream. Only the actually consumed prefix is budgeted. -/
theorem adaptive_corrupted_clipped_mean_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X c : ℕ → Ω → ℝ)
    (count : Ω → ℕ) (ε u mean C : ℝ) (t : ℕ)
    (hXm : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1) (hu0 : 0 < u)
    (hmean : ∀ i, (∫ ω, X i ω ∂μ) = mean)
    (hm : ∀ i, Integrable (fun ω => |X i ω|^(1+ε)) μ)
    (hu : ∀ i, (∫ ω, |X i ω|^(1+ε) ∂μ) ≤ u)
    (hC : ∀ ω, (∑ s ∈ Finset.range (count ω), |c s ω|) ≤ C) :
    μ.real {ω | 0 < count ω ∧ count ω ≤ t ∧
      confidenceRadius ε u t (count ω) + C / count ω ≤
        |prefixMean (fun s => clip (sampleThreshold ε u t s) (X s ω + c s ω))
          (count ω) - mean|} ≤ t * (2 * Real.exp (-confidenceLog t)) := by
  have htail := scheduled_adaptive_clipped_mean_tail μ X count ε u mean t
    hXm hi hε0 hε hu0 (fun i => integrable_of_raw_moment μ (X i) ε (hXm i) hε0 (hm i))
    hmean hm hu
  refine (measureReal_mono ?_ (measure_ne_top _ _)).trans htail
  intro ω hω
  refine ⟨hω.1, hω.2.1, ?_⟩
  have hp := clipped_prefix_corruption_le (fun s => X s ω) (fun s => c s ω)
    (sampleThreshold ε u t) (count ω) C (hC ω)
  have ht := abs_sub_le
    (prefixMean (fun s => clip (sampleThreshold ε u t s) (X s ω + c s ω)) (count ω))
    (prefixMean (fun s => clip (sampleThreshold ε u t s) (X s ω)) (count ω)) mean
  change confidenceRadius ε u t (count ω) ≤
    |prefixMean (fun s => clip (sampleThreshold ε u t s) (X s ω)) (count ω) - mean|
  linarith [hω.2.2]

/-- Confidence for the actual clipped observations along an arbitrary action
trace, including a policy driven by corrupted observations. This compares clean
and corrupted rewards along that same trace, not two different policies. -/
theorem observed_corrupted_clipped_mean_tail {Ω : Type*} [MeasurableSpace Ω] {K : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (action : Ω → ActionTrace (Fin K)) (stream corruption : Ω → UCB.ArmRewardStream K)
    (arm : Fin K) (ε u mean C : ℝ) (t : ℕ)
    (hXm : ∀ i, Measurable (fun ω => stream ω i arm))
    (hi : iIndepFun (fun i ω => stream ω i arm) μ)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1) (hu0 : 0 < u)
    (hmean : ∀ i, (∫ ω, stream ω i arm ∂μ) = mean)
    (hm : ∀ i, Integrable (fun ω => |stream ω i arm|^(1+ε)) μ)
    (hu : ∀ i, (∫ ω, |stream ω i arm|^(1+ε) ∂μ) ≤ u)
    (hC : ∀ ω, (∑ s ∈ Finset.range (pullCount (action ω) arm t),
      |corruption ω s arm|) ≤ C) :
    μ.real {ω | 0 < pullCount (action ω) arm t ∧ pullCount (action ω) arm t ≤ t ∧
      confidenceRadius ε u t (pullCount (action ω) arm t) +
        C / pullCount (action ω) arm t ≤
      |sumRewards (action ω)
        (fun s => clip (sampleThreshold ε u t (pullCount (action ω) (action ω s) s))
          (UCB.rewardFromArmStream action
            (fun ω j a => stream ω j a + corruption ω j a) ω s)) arm t /
        pullCount (action ω) arm t - mean|} ≤
      t * (2 * Real.exp (-confidenceLog t)) := by
  have htail := adaptive_corrupted_clipped_mean_tail μ
    (fun i ω => stream ω i arm) (fun i ω => corruption ω i arm)
    (fun ω => pullCount (action ω) arm t) ε u mean C t
    hXm hi hε0 hε hu0 hmean hm hu hC
  simpa only [prefixMean,
    clipped_observed_prefix action stream corruption (fun j _ => sampleThreshold ε u t j)]
    using htail

/-- Stationary arm laws supply the coordinate independence and moments for the
reserved transfer endpoint. No confidence bound is supplied by the caller. -/
theorem arm_corrupted_clipped_mean_tail {K : ℕ}
    (ν : Kernel (Fin K) ℝ) [IsMarkovKernel ν]
    (arm : Fin K) (count : UCB.ArmRewardStream K → ℕ)
    (c : ℕ → UCB.ArmRewardStream K → ℝ) (ε u C : ℝ) (t : ℕ)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1) (hu0 : 0 < u)
    (hm : Integrable (fun x : ℝ => |x|^(1+ε)) (ν arm))
    (hu : (∫ x, |x|^(1+ε) ∂ν arm) ≤ u)
    (hC : ∀ stream, (∑ s ∈ Finset.range (count stream), |c s stream|) ≤ C) :
    (UCB.armStreamMeasure ν).real {stream | 0 < count stream ∧ count stream ≤ t ∧
      confidenceRadius ε u t (count stream) + C / count stream ≤
      |prefixMean (fun s => clip (sampleThreshold ε u t s) (stream s arm + c s stream))
        (count stream) - ∫ x, x ∂ν arm|} ≤ t * (2 * Real.exp (-confidenceLog t)) := by
  apply adaptive_corrupted_clipped_mean_tail (UCB.armStreamMeasure ν)
    (fun s stream => stream s arm) c count ε u _ C t
    (fun i => (measurable_pi_apply arm).comp (measurable_pi_apply i))
  · simpa only [sub_zero] using UCB.iIndepFun_armStreamMeasure_coord_sub ν arm 0
  · exact hε0
  · exact hε
  · exact hu0
  · exact fun i => arm_coordinate_integral ν arm i _ measurable_id
  · exact fun i => arm_coordinate_integrable ν arm i _ hm
  · intro i
    rw [arm_coordinate_integral ν arm i (fun x : ℝ => |x|^(1+ε)) (by fun_prop)]
    exact hu
  · exact hC

end BanditRLProof.HeavyTail

```
</details>
