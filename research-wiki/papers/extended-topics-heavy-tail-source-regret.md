# Corrected regret for the unchanged source-parameter robust UCB

Source: Bubeck, Cesa-Bianchi and Lugosi, Bandits With Heavy Tail, IEEE TIT
59(11), 2013, Figure1 p7712, Lemma1 pp7713-7714, and Theorem1 p7714.
Frozen published PDF SHA256:
df94efa3708dab85063d6c7a04e0812f264c1c6f13a284017eb2efeed5077ef3.

## Source statement and explicit correction

The printed gap-dependent endpoint is

    sum_(Delta_i>0) [8(4u/Delta_i)^(1/epsilon) log(T)+5Delta_i].

For the literal radius-four source policy this coefficient has an independently
checked finite counterexample on deterministic rewards0,-1 at T=2^50. That
counterexample's complete Lean certificate is still an obligation. The theorem
on this page proves a separately labelled corrected bound for the UNCHANGED
source policy. It does not silently certify the printed coefficient or replace
that outstanding formal-obstruction obligation.

The policy uses paper-round r^(-2), source sample-index hard deletion, radius4,
round-robin unpulled-arm tie resolution, and least-encoded later ties. See the
source-schedule reader for exact observed-history construction and semantic
review. It is fixed independently of analysis horizon T.

## Actual model and endpoint

Let K>0 be finite. Each arm has a stationary probability reward law on the real
line, and the independent product arm streams feed the causal policy's next
unused coordinates. Assume u>0, 0<epsilon<=1, and integrable raw p moments with
E|X_i|^p<=u, p=1+epsilon. First moments are DERIVED using
|x|<=1+|x|^p; they are not hidden endpoint assumptions. Means are arm-law
integrals, mu_* is their maximum, Delta_i=mu_*-mu_i, and R_T is expected
pseudo-regret, not a high-probability or realized-noise guarantee.

Set

    L_T=2log(max(T,1)),
    A_i=L_T / [Delta_i/(8u^(1/p))]^(p/epsilon), for Delta_i>0.

For every natural horizon T the actual Lean endpoint is

    R_T <= sum_(Delta_i>0) Delta_i*(A_i+5).

For positive T its leading summand equals

    2*8^(p/epsilon)*(u/Delta_i)^(1/epsilon)*log(T).

At epsilon1 this is128u log(T)/Delta_i, versus the rejected printed32u log(T)/Delta_i.
The additive5Delta_i is retained. The T=0 logarithm uses max(T,1), and T=0/1
are handled directly by count<=T. No inverse-gap expression is evaluated as an
assumption for a zero-gap arm; the final sum is explicitly filtered to positive
gaps. No confidence, expected-count, or main regret assumption is supplied to
the endpoint.

## Proof from the actual algorithm

For t<T, the policy uses L_t=2log(t+1)<=L_T. For positive gap define the integer
cutoff ell_i=ceil(A_i). At T>=2 this cutoff is positive. If N_i(t)>=ell_i,
real-power monotonicity gives2r_i(t)<=Delta_i. The exact ceiling is sufficient:
no extra one is inserted into the cutoff.

Use the complements of the CLOSED best-arm lower and comparison-arm upper bad
events. These imply strict inequalities mu_*-mhat_*<r_* and mhat_i-mu_i<r_i.
Actual index maximality then gives Delta_i<2r_i whenever arm i is selected.
Thus selection with count>=ell_i implies one of these two signed bad events.
The source confidence producers derive their probabilities from raw moments,
with no stopping-time/IID assertion about the adaptive count. Each signed time
budget is at most2, giving total budget4 for this fixed arm/best-arm pair.

The shared pathwise threshold-count lemma bounds count by ell_i plus the sum
of indicators of selections at already-large count. During round-robin
initialization the selected arm has prior count0, so it cannot enter that
large-count sum. Measurability of the actual selectors/actions permits the
indicator integral identity. Integration and the two signed budgets yield

    E N_i(T)<=ceil(A_i)+4<=A_i+5.

For T=0/1 use the pointwise count<=T and A_i>=0. Count integrability follows
from the same bound and action measurability. The shared regret decomposition
writes expected pseudo-regret as the sum of gap times expected count. Choose
an actual finite best arm, split zero gaps before inversion, and substitute
the count bound for each positive gap. This closes the performance chain.

## Reuse, review and remaining boundary

Actual reused local producers include SourcePolicy's causal history and signed
confidence chain, the generic lintegral_pullCount_threshold, raw-moment first
moment derivation, and integral_realMeanRegret_eq_sum_gap_mul_integral_pullCount.
The source cutoff adapts existing real-power inversion while strict signed
events remove the conservative extra cutoff term. Mathlib supplies ceiling,
integration, finite sum and real-power interfaces. This is a formal dependency
composition, not an efficiency experiment or a new conceptual functor.

The old conservative radius8/time^-4 regret theorem remains separate. The new
result preserves the source algorithm and changes its guarantee explicitly.
The finite counterexample, remaining source transitive audits, clipping-transfer
acceptance, topic mappings and all-ten ICLR evidence are still required.

## Exact Lean endpoint and proof

Namespace BanditRLProof.HeavyTail.SourcePolicy; open MeasureTheory ProbabilityTheory.
Definitions horizonLog, gapBudget, robustAction and the stationary arm-stream
measure are as specified above and in the source-schedule page.

<details>
<summary>robust_expected_regret</summary>

```lean
theorem robust_expected_regret (hK : 0 < K)
    (ν : Kernel (Fin K) ℝ) [IsMarkovKernel ν] (ε u : ℝ) (T : ℕ)
    (hε0 : 0 < ε) (hε : ε ≤ 1) (hu0 : 0 < u)
    (hm : ∀ a, Integrable (fun x : ℝ => |x|^(1+ε)) (ν a))
    (hu : ∀ a, (∫ x, |x|^(1+ε) ∂ν a) ≤ u) :
    (∫ stream, realMeanRegret (realKernelMean ν) (robustAction hK ε u stream) T
      ∂UCB.armStreamMeasure ν) ≤
    ∑ arm ∈ Finset.univ.filter (fun arm : Fin K => 0 < realMeanGap (realKernelMean ν) arm),
      realMeanGap (realKernelMean ν) arm *
        (gapBudget ε u (realMeanGap (realKernelMean ν) arm) T + 5) := by
  have hX : ∀ a, Integrable (fun x : ℝ => x) (ν a) := fun a =>
    integrable_id_of_raw_moment (ν a) ε hε0.le (hm a)
  rw [integral_realMeanRegret_eq_sum_gap_mul_integral_pullCount
    (UCB.armStreamMeasure ν) (realKernelMean ν) (robustAction hK ε u) T
    (fun arm => robust_integrable_count hK ν arm ε u T), Finset.sum_filter]
  apply Finset.sum_le_sum
  intro arm _
  have he : realMeanGap (realKernelMean ν) arm =
      realKernelMean ν (ETC.realKernelBestArm hK ν) - realKernelMean ν arm := by
    rw [realMeanGap, ETC.ciSup_realKernelMean_eq_realKernelBestArm hK ν]
  have hg : 0 ≤ realMeanGap (realKernelMean ν) arm := by
    rw [he]
    exact sub_nonneg.mpr (ETC.realKernelMean_le_realKernelBestArm hK ν arm)
  by_cases hp : 0 < realMeanGap (realKernelMean ν) arm
  · rw [if_pos hp]
    apply mul_le_mul_of_nonneg_left _ hg
    rw [he]
    exact robust_integral_count_le_budget hK ν (ETC.realKernelBestArm hK ν) arm ε u T hε0 hε hu0
      (by simpa only [he, realKernelMean] using hp) hX hm hu
  · rw [if_neg hp]
    have hz : realMeanGap (realKernelMean ν) arm = 0 := le_antisymm (not_lt.mp hp) hg
    simp [hz]
```

</details>
