import BanditRLProof.Algorithms.UCBRealHistoryIndex
import BanditRLProof.ProbabilityUnionBound
import Mathlib.Probability.IdentDistrib

/-!
# Fixed-count peeling for native Real UCB rewards

This module isolates the law transport used by the pinned LML UCB proof. A
`FixedArmPrefixSource` records the pathwise fact that rewards selected from one
arm are the prefix of an arm-indexed reward stream. The main theorems peel the
random pull count into finitely many fixed counts and transport every fixed
prefix event through an `IdentDistrib` stream law.
-/

namespace BanditRLProof

open MeasureTheory ProbabilityTheory

namespace UCB

universe u v

/-- A table containing one infinite reward stream for every finite arm. -/
abbrev ArmRewardStream (K : Nat) := Nat -> Fin K -> Real

/-- Sum of the first `k` rewards in one arm's stream. -/
def armPrefixSum {K : Nat} (arm : Fin K) (k : Nat)
    (stream : ArmRewardStream K) : Real :=
  (Finset.range k).sum (fun i => stream i arm)

/-- A fixed-arm prefix sum is measurable on the full stream space. -/
theorem measurable_armPrefixSum {K : Nat} (arm : Fin K) (k : Nat) :
    Measurable (armPrefixSum arm k) := by
  unfold armPrefixSum
  refine Finset.measurable_sum _ ?_
  intro i _hi
  exact (measurable_pi_apply arm).comp (measurable_pi_apply i)

/--
Pathwise source contract behind fixed-count peeling.

For each sample point, arm, and horizon, the selected reward sum must be the
prefix sum of that arm's latent stream at the realized pull count.
-/
structure FixedArmPrefixSource
    {Omega : Type u} {K : Nat} [MeasurableSpace Omega]
    (action : Omega -> ActionTrace (Fin K))
    (reward : Omega -> RewardTrace Real) where
  armStream : Omega -> ArmRewardStream K
  measurable_armStream_coord : forall i arm,
    Measurable (fun omega => armStream omega i arm)
  sumRewards_eq_armPrefixSum : forall omega arm n,
    sumRewards (action omega) (reward omega) arm n =
      UCB.armPrefixSum arm (pullCount (action omega) arm n) (armStream omega)

/-- The complete latent arm stream supplied by a source is measurable. -/
theorem FixedArmPrefixSource.measurable_armStream
    {Omega : Type u} {K : Nat} [MeasurableSpace Omega]
    {action : Omega -> ActionTrace (Fin K)}
    {reward : Omega -> RewardTrace Real}
    (source : FixedArmPrefixSource action reward) :
    Measurable source.armStream := by
  exact measurable_pi_lambda _ (fun i =>
    measurable_pi_lambda _ (fun arm =>
      source.measurable_armStream_coord i arm))

/-- Every fixed prefix sum read from a source is measurable. -/
theorem FixedArmPrefixSource.measurable_armPrefixSum
    {Omega : Type u} {K : Nat} [MeasurableSpace Omega]
    {action : Omega -> ActionTrace (Fin K)}
    {reward : Omega -> RewardTrace Real}
    (source : FixedArmPrefixSource action reward)
    (arm : Fin K) (k : Nat) :
    Measurable (fun omega => UCB.armPrefixSum arm k (source.armStream omega)) := by
  exact (UCB.measurable_armPrefixSum arm k).comp source.measurable_armStream

/--
Pathwise fixed-count peeling.

The adaptive `(pullCount, sumRewards)` event is covered by the finite union of
fixed-prefix events for counts at most `n`. This is an outer-measure bound, so
the event set itself need not be measurable.
-/
theorem measure_pullCount_prod_sumRewards_mem_le_of_fixedArmPrefixSource
    {Omega : Type u} {K : Nat} [MeasurableSpace Omega]
    (mu : Measure Omega)
    (action : Omega -> ActionTrace (Fin K))
    (reward : Omega -> RewardTrace Real)
    (source : FixedArmPrefixSource action reward)
    (arm : Fin K) (n : Nat) (s : Set (Nat × Real))
    [DecidablePred (fun k : Nat => k ∈ Prod.fst '' s)] :
    mu {omega |
        (pullCount (action omega) arm n,
          sumRewards (action omega) (reward omega) arm n) ∈ s} ≤
      ((Finset.range (n + 1)).filter
        (fun k => k ∈ Prod.fst '' s)).sum (fun k =>
          mu {omega |
            UCB.armPrefixSum arm k (source.armStream omega) ∈
              Prod.mk k ⁻¹' s}) := by
  classical
  let counts := (Finset.range (n + 1)).filter
    (fun k => k ∈ Prod.fst '' s)
  let fixedEvent := fun k : Nat =>
    {omega : Omega |
      UCB.armPrefixSum arm k (source.armStream omega) ∈ Prod.mk k ⁻¹' s}
  have hsubset :
      {omega : Omega |
        (pullCount (action omega) arm n,
          sumRewards (action omega) (reward omega) arm n) ∈ s} ⊆
        ⋃ k ∈ counts, fixedEvent k := by
    intro omega homega
    let k := pullCount (action omega) arm n
    have hk_le : k ≤ n := pullCount_le_time (action omega) arm n
    have hk_pair :
        (k, UCB.armPrefixSum arm k (source.armStream omega)) ∈ s := by
      simpa [k, source.sumRewards_eq_armPrefixSum omega arm n] using homega
    have hk_fst : k ∈ Prod.fst '' s := by
      refine ⟨(k, UCB.armPrefixSum arm k (source.armStream omega)), hk_pair, ?_⟩
      rfl
    have hk_counts : k ∈ counts := by
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hk_le), hk_fst⟩
    simp only [Set.mem_iUnion]
    exact ⟨k, ⟨hk_counts, hk_pair⟩⟩
  calc
    mu {omega |
        (pullCount (action omega) arm n,
          sumRewards (action omega) (reward omega) arm n) ∈ s} ≤
        mu (⋃ k ∈ counts, fixedEvent k) :=
      measure_mono hsubset
    _ ≤ counts.sum (fun k => mu (fixedEvent k)) :=
      ProbabilityUnionBound.measure_biUnion_finset_le mu counts fixedEvent
    _ = ((Finset.range (n + 1)).filter
        (fun k => k ∈ Prod.fst '' s)).sum (fun k =>
          mu {omega |
            UCB.armPrefixSum arm k (source.armStream omega) ∈
              Prod.mk k ⁻¹' s}) := by
      simp only [counts, fixedEvent]

/--
Fixed-count peeling with law transport to a canonical arm-reward stream.

One `IdentDistrib` hypothesis for the complete latent stream supplies every
fixed-prefix law by measurable composition. This is the local counterpart of
the law-transport step in LML `prob_pullCount_prod_sumRewards_mem_le`.
-/
theorem measure_pullCount_prod_sumRewards_mem_le_of_fixedArmPrefixSource_identDistrib
    {Omega : Type u} {Xi : Type v} {K : Nat}
    [MeasurableSpace Omega] [MeasurableSpace Xi]
    (mu : Measure Omega) (nu : Measure Xi)
    (action : Omega -> ActionTrace (Fin K))
    (reward : Omega -> RewardTrace Real)
    (source : FixedArmPrefixSource action reward)
    (canonicalStream : Xi -> ArmRewardStream K)
    (hstreamLaw : IdentDistrib source.armStream canonicalStream mu nu)
    (arm : Fin K) (n : Nat) (s : Set (Nat × Real))
    [DecidablePred (fun k : Nat => k ∈ Prod.fst '' s)]
    (hs : MeasurableSet s) :
    mu {omega |
        (pullCount (action omega) arm n,
          sumRewards (action omega) (reward omega) arm n) ∈ s} ≤
      ((Finset.range (n + 1)).filter
        (fun k => k ∈ Prod.fst '' s)).sum (fun k =>
          nu {xi |
            UCB.armPrefixSum arm k (canonicalStream xi) ∈
              Prod.mk k ⁻¹' s}) := by
  classical
  calc
    mu {omega |
        (pullCount (action omega) arm n,
          sumRewards (action omega) (reward omega) arm n) ∈ s} ≤
      ((Finset.range (n + 1)).filter
        (fun k => k ∈ Prod.fst '' s)).sum (fun k =>
          mu {omega |
            UCB.armPrefixSum arm k (source.armStream omega) ∈
              Prod.mk k ⁻¹' s}) :=
      UCB.measure_pullCount_prod_sumRewards_mem_le_of_fixedArmPrefixSource
        mu action reward source arm n s
    _ = ((Finset.range (n + 1)).filter
        (fun k => k ∈ Prod.fst '' s)).sum (fun k =>
          nu {xi |
            UCB.armPrefixSum arm k (canonicalStream xi) ∈
              Prod.mk k ⁻¹' s}) := by
      apply Finset.sum_congr rfl
      intro k _hk
      have hkLaw : IdentDistrib
          (fun omega => UCB.armPrefixSum arm k (source.armStream omega))
          (fun xi => UCB.armPrefixSum arm k (canonicalStream xi)) mu nu := by
        simpa [Function.comp_def] using
          hstreamLaw.comp (UCB.measurable_armPrefixSum arm k)
      exact hkLaw.measure_mem_eq
        (hs.preimage (measurable_const.prodMk measurable_id))

end UCB
end BanditRLProof
