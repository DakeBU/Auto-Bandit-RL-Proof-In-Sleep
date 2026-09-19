# Source-schedule robust UCB: adaptive confidence and finite event budgets

Source: Bubeck, Cesa-Bianchi and Lugosi, Bandits With Heavy Tail, IEEE TIT
59(11), 2013, Figure1 p7712 and sample-index truncated estimator/Lemma1
pp7713-7714. Frozen published PDF SHA256:
df94efa3708dab85063d6c7a04e0812f264c1c6f13a284017eb2efeed5077ef3.

## Actual algorithm and source mapping

Paper round r starts at1; Lean decision time t=r-1 starts at0. There are t
previous observations. For t>=1, use L_t=2log(t+1)=log(r^2), exactly the
Figure1 delta=r^(-2) schedule. With p=1+epsilon and q=epsilon/p, define

    B_(t,s)=(u(s+1)/L_t)^(1/p),
    r_(t,n)=4 u^(1/p) (L_t/n)^q.

For each arm, re-evaluate all of its previous observations at the current t's
sample-ordinal thresholds. Discard an outlier entirely and divide by the full
pull count. Do not confuse this with clipping or thresholds frozen at arrival.
The index is this truncated mean plus r_(t,N_i(t)). The first K choices are
round-robin. This specifies a tie choice among source unpulled-arm infinite
indices; after initialization all arm counts are positive. Subsequent ties are
resolved by the least encoded maximizer. The policy is fixed independently of
analysis horizon T. Neither the arm choice nor its index reads a future reward.

The code uses the existing ArmStreamPolicy finite-history recursion and next
unused arm-coordinate reward construction. The history-to-latent-prefix
identity is an actual pathwise theorem. The canonical independent arm-stream
measure is generated from stationary arm kernels; only the inspected arm's
raw moment assumptions are needed for its confidence claim.

## Assumptions and exact confidence endpoint

K>0, epsilon in [0,1], u>0, integrable first and raw p moments, and
E|X_i|^p<=u. The log-confidence extension epsilon=0 gives a nonshrinking radius;
it is not an inverse-epsilon regret result. The generic sequence theorem allows
independent nonidentical laws sharing the same mean and moment bound. The arm
specialization is stationary iid within each arm on the product stream space.

At t>=K, each signed closed deviation event for an individual arm obeys

    P(mhat_i(t)-mu_i >= r_(t,N_i(t))) <= t exp(-5L_t/4),
    P(mu_i-mhat_i(t) >= r_(t,N_i(t))) <= t exp(-5L_t/4).

These are separate one-sided claims. The actual new time-budget endpoints are

    sum_(t<T) P(t>=K and mhat_i(t)-mu_i >= r_(t,N_i(t))) <=2,
    sum_(t<T) P(t>=K and mu_i-mhat_i(t) >= r_(t,N_i(t))) <=2.

No confidence premise is supplied to these endpoints. The arm law's raw moment
and integrability assumptions produce the probabilities through the actual
policy and history. A best-arm lower event and one fixed comparison-arm upper
event therefore cost at most4 in total. This is not a claim of a budget4
simultaneously over all arms or for an unconstrained randomly chosen arm.

## Proof and hidden regularity

Previous work proved the identical radius-four fixed-prefix event at probability
exp(-5L/4), using the raw-variable 3/4 exponential remainder and then centering.
For any count N in1..t, its bad event is contained in the union over all t
fixed prefix sizes. Every prefix uses the same deterministic evaluation-time
L_t. Finite measure subadditivity gives t exp(-5L_t/4). The count itself is
never asserted IID, independent of the stream, or a stopping time.

The generic arbitrary-count statement is an outer-measure inequality: it needs
no count measurability because the underlying measure is finite. The actual
finite-history policy has proved measurable selectors/actions, so ordinary
measurable policy events are available. At t=0 the positive-count restricted
event is empty; no positive-log concentration is applied there.

For t>=1,

    t exp(-5L_t/4) = t/(sqrt(t+1))^5
      <=1/(sqrt(t+1))^3
      <=2(1/sqrt(t)-1/sqrt(t+1)).

The last inequality follows by rationalizing the inverse-square-root difference
and using sqrt(t)<=sqrt(t+1). Summing telescopes to a value <=2. The t=0 term
is zero. Summing the per-round actual-policy confidence inequalities proves
the two finite-budget endpoints.

## Explicit deltas and remaining boundary

The source schedule, estimator and radius are retained with explicit tie rules.
The stronger tail exponent, closed bad events, epsilon=0 extension and the
finite signed budget2 are derived strengthening/repair results, not quoted
printed claims. The source's displayed summation proof is not silently accepted.
The old conservative radius8/time^-4 policy remains a separate declaration.

No complete original-policy regret bound or printed regret coefficient is
claimed. The twice-radius gap threshold still needs adjudication; topic
acceptance and the full all-ten ICLR evidence remain open.

## Actual reuse and graph semantics

Reused local parents include source_truncated_mean_upper_tail_log_sharp,
truncate_neg, arm_coordinate_integral/integrable, the historyTruncatedMean
and truncated_observed_sum infrastructure, ArmStreamPolicy, and the existing
measurable least-encoded argmax. Mathlib supplies finite measure subadditivity,
monotonicity, sqrt/rpow/exp identities and finite sums. The finite-union pattern
adapts scheduled_adaptive_mean_tail, without importing its altered schedule.
No new conceptual functor or efficiency claim is established. The new policy
is an explicit configuration of shared history/action infrastructure.

## Exact Lean endpoints

Scoped namespaces and definitions above are retained in the linked modules.

<details>
<summary>source_adaptive_mean_upper_tail</summary>

```lean
theorem source_adaptive_mean_upper_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (count : Ω → ℕ) (ε u mean : ℝ) (t : ℕ)
    (hXm : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1) (hu : 0 < u)
    (hX : ∀ i, Integrable (X i) μ)
    (hmean : ∀ i, (∫ ω, X i ω ∂μ) = mean)
    (hm : ∀ i, Integrable (fun ω => |X i ω|^(1+ε)) μ)
    (hraw : ∀ i, (∫ ω, |X i ω|^(1+ε) ∂μ) ≤ u) :
    μ.real {ω | 0 < count ω ∧ count ω ≤ t ∧
      sourceConfidenceRadius ε u t (count ω) ≤
        (∑ s ∈ Finset.range (count ω),
          truncate (sourceTruncationThreshold ε u (sourceConfidenceLog t) s) (X s ω)) /
            count ω - mean} ≤ t*Real.exp (-(5/4 : ℝ)*sourceConfidenceLog t) := by
  by_cases ht : t = 0
  · subst t
    have hempty : ∀ ω, ¬(0 < count ω ∧ count ω ≤ 0) := by intro ω; omega
    simp only [← and_assoc, hempty, false_and, Set.setOf_false, measureReal_empty,
      Nat.cast_zero, zero_mul, le_refl]
  have htpos : 0 < t := Nat.pos_of_ne_zero ht
  let E := fun k => {ω | sourceConfidenceRadius ε u t (k+1) ≤
    (∑ s ∈ Finset.range (k+1),
      truncate (sourceTruncationThreshold ε u (sourceConfidenceLog t) s) (X s ω)) /
        ((k+1 : ℕ) : ℝ) - mean}
  have hs : {ω | 0 < count ω ∧ count ω ≤ t ∧
      sourceConfidenceRadius ε u t (count ω) ≤
        (∑ s ∈ Finset.range (count ω),
          truncate (sourceTruncationThreshold ε u (sourceConfidenceLog t) s) (X s ω)) /
            count ω - mean} ⊆ ⋃ k ∈ Finset.range t, E k := by
    intro ω hω
    rcases hω with ⟨hpos, hle, hbad⟩
    apply Set.mem_iUnion.mpr ⟨count ω - 1, ?_⟩
    apply Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
    have he : count ω - 1 + 1 = count ω := by omega
    simpa only [E, Set.mem_setOf_eq, he] using hbad
  calc
    _ ≤ μ.real (⋃ k ∈ Finset.range t, E k) := measureReal_mono hs (measure_ne_top _ _)
    _ ≤ ∑ k ∈ Finset.range t, μ.real (E k) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _k ∈ Finset.range t, Real.exp (-(5/4 : ℝ)*sourceConfidenceLog t) := by
      apply Finset.sum_le_sum
      intro k _
      exact source_truncated_mean_upper_tail_log_sharp μ X ε u (sourceConfidenceLog t)
        mean (k+1) (by omega) hXm hi hε0 hε hu (sourceConfidenceLog_pos t htpos)
        hX hmean hm hraw
    _ = _ := by simp
```

</details>

<details>
<summary>source_schedule_tail_sum_le_two</summary>

```lean
theorem source_schedule_tail_sum_le_two (T : ℕ) :
    (∑ t ∈ Finset.range T, t*Real.exp (-(5/4 : ℝ)*sourceConfidenceLog t)) ≤ 2 := by
  have hshift : ∀ n : ℕ,
      (∑ s ∈ Finset.range n, (s+1 : ℝ)*Real.exp (-(5/4 : ℝ)*sourceConfidenceLog (s+1))) ≤
        2*(1-1/Real.sqrt ((n : ℝ)+1)) := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have h := source_schedule_tail_le_telescope (n+1) (by omega)
      push_cast at h ⊢
      linarith
  cases T with
  | zero => simp
  | succ n =>
    rw [Finset.sum_range_succ']
    have h := hshift n
    push_cast
    simp only [zero_mul, add_zero]
    exact h.trans (by
      have : 0 ≤ 1/Real.sqrt ((n : ℝ)+1) := by positivity
      linarith)
```

</details>

<details>
<summary>robustMean_upper_tail_sum</summary>

```lean
theorem robustMean_upper_tail_sum (hK : 0 < K) (ν : Kernel (Fin K) ℝ) [IsMarkovKernel ν]
    (arm : Fin K) (ε u : ℝ) (T : ℕ)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1) (hu0 : 0 < u)
    (hX : Integrable (fun x : ℝ => x) (ν arm))
    (hm : Integrable (fun x : ℝ => |x|^(1+ε)) (ν arm))
    (hu : (∫ x, |x|^(1+ε) ∂ν arm) ≤ u) :
    (∑ t ∈ Finset.range T, (UCB.armStreamMeasure ν).real {stream | K ≤ t ∧
      sourceConfidenceRadius ε u t (pullCount (robustAction hK ε u stream) arm t) ≤
        robustMean hK ε u stream arm t - ∫ x, x ∂ν arm}) ≤ 2 := by
  apply le_trans (Finset.sum_le_sum fun t _ => ?_) (source_schedule_tail_sum_le_two T)
  by_cases ht : K ≤ t
  · simpa only [ht, true_and] using
      robustMean_upper_tail hK ν arm ε u t ht hε0 hε hu0 hX hm hu
  · simp only [ht, false_and, Set.setOf_false, measureReal_empty]
    positivity
```

</details>

<details>
<summary>robustMean_lower_tail_sum</summary>

```lean
theorem robustMean_lower_tail_sum (hK : 0 < K) (ν : Kernel (Fin K) ℝ) [IsMarkovKernel ν]
    (arm : Fin K) (ε u : ℝ) (T : ℕ)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1) (hu0 : 0 < u)
    (hX : Integrable (fun x : ℝ => x) (ν arm))
    (hm : Integrable (fun x : ℝ => |x|^(1+ε)) (ν arm))
    (hu : (∫ x, |x|^(1+ε) ∂ν arm) ≤ u) :
    (∑ t ∈ Finset.range T, (UCB.armStreamMeasure ν).real {stream | K ≤ t ∧
      sourceConfidenceRadius ε u t (pullCount (robustAction hK ε u stream) arm t) ≤
        (∫ x, x ∂ν arm) - robustMean hK ε u stream arm t}) ≤ 2 := by
  apply le_trans (Finset.sum_le_sum fun t _ => ?_) (source_schedule_tail_sum_le_two T)
  by_cases ht : K ≤ t
  · simpa only [ht, true_and] using
      robustMean_lower_tail hK ν arm ε u t ht hε0 hε hu0 hX hm hu
  · simp only [ht, false_and, Set.setOf_false, measureReal_empty]
    positivity
```

</details>

## Independent semantic acceptance

PacketE blind reconstruction exposed an omitted threshold definition in the
review packet; that context was added and the independent decoder re-read it.
Independent source review then accepted the exact Figure1 policy correspondence
with the tie/index conventions above and the explicit derived confidence
strengthening. Separate proof-method review accepted the frozen implementation.
No source or repair review certifies a regret theorem. Final joint gate evidence
is bound in runs/extended-topics-20260919/source-schedule-validation.json.
