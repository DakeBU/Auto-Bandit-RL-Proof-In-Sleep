import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Fintype.Basic
import BanditRLProof.Algorithms.ETCMeasurability

/-!
# ETC concrete argmax commit oracle

This file promotes the concrete finite-argmax ETC commit-oracle route into a
compiled deterministic leaf.  It only constructs a score-maximizing oracle over
`Fin K -> Rat` and proves the maximality certificate consumed by the existing
wrong-commit event wrappers.
-/

namespace BanditRLProof
namespace ETC

private theorem score_le_foldl_select
    {K : Nat} (scores : Fin K -> Rat) (init : Fin K) :
    forall l : List (Fin K),
      (forall a : Fin K, List.Mem a l ->
        scores a <=
          scores
            (l.foldl
              (fun best arm : Fin K =>
                if scores best < scores arm then arm else best)
              init)) /\
      scores init <=
        scores
          (l.foldl
            (fun best arm : Fin K =>
              if scores best < scores arm then arm else best)
            init)
  | [] => by
      exact And.intro
        (by
          intro _ ha
          cases ha)
        (by
          simp)
  | arm :: rest => by
      let select :=
        fun best arm : Fin K =>
          if scores best < scores arm then arm else best
      let next := select init arm
      have ih := score_le_foldl_select (scores := scores) next rest
      have harm_next : scores arm <= scores next := by
        exact if hlt : scores init < scores arm then
          by
            simp [next, select, hlt]
        else
          by
            simp [next, select, hlt, le_of_not_gt hlt]
      exact And.intro
        (by
          intro a ha
          cases ha with
          | head =>
              exact le_trans harm_next ih.2
          | tail _ ha =>
              exact ih.1 a ha)
        (by
          have hinit_next : scores init <= scores next := by
            exact if hlt : scores init < scores arm then
              by
                simpa [next, select, hlt] using le_of_lt hlt
            else
              by
                simp [next, select, hlt]
          exact le_trans hinit_next ih.2)

/--
A concrete ETC commit oracle that selects a score-maximizing arm from `Fin K`.

The selector scans `List.finRange K` and keeps the previous arm on ties, giving
a deterministic total oracle whenever `hK : 0 < K` supplies the initial arm.
This is the compiled `ETC-COMMIT-ORACLE-CONCRETE-ARGMAX` leaf.
-/
noncomputable def argmaxCommitOracle
    {K : Nat} (hK : 0 < K) : ETC.CommitOracle K where
  choose scores :=
    (List.finRange K).foldl
      (fun best arm : Fin K =>
        if scores best < scores arm then arm else best)
      (Fin.mk 0 hK)
  card := "finite_rat_argmax_commit"

/--
The concrete ETC argmax oracle returns an arm whose score dominates every arm.

This is the maximality certificate needed by the already compiled abstract
commit-oracle wrong-event and probability consumers.  It does not introduce
measures, empirical-mean construction, concentration, filtration, or final ETC
regret.
-/
theorem argmaxCommitOracle_choose_spec
    {K : Nat} (hK : 0 < K)
    (scores : Fin K -> Rat) (a : Fin K) :
    scores a <= scores ((ETC.argmaxCommitOracle hK).choose scores) := by
  unfold argmaxCommitOracle
  dsimp
  exact
    (score_le_foldl_select
      (scores := scores)
      (init := Fin.mk 0 hK)
      (List.finRange K)).1 a (List.mem_finRange a)

/--
The concrete argmax oracle instantiates the existing deterministic wrong-commit
event reduction.

This wrapper records that the new concrete oracle feeds directly into the
previous abstract `CommitOracle` consumer.  It remains a deterministic set
inclusion, with no probability or concentration assumptions.
-/
theorem wrong_commit_subset_exists_empMean_ge_bestArm_of_argmaxOracle
    {Omega : Type u} {K : Nat}
    (hK : 0 < K)
    (model : FiniteBanditModel K)
    (empMean : Omega -> Fin K -> Rat) :
    Set.Subset
      {omega : Omega |
        (ETC.argmaxCommitOracle hK).choose (empMean omega) =
          model.bestArm -> False}
      {omega : Omega |
        exists a : Fin K, (a = model.bestArm -> False) /\
          empMean omega a >= empMean omega model.bestArm} := by
  exact
    ETC.wrong_commit_subset_exists_empMean_ge_bestArm_of_commitOracle
      model
      (ETC.argmaxCommitOracle hK)
      empMean
      (by
        intro scores a
        exact ETC.argmaxCommitOracle_choose_spec hK scores a)

/--
The concrete argmax oracle-selected wrong-commit event is bounded by the
filtered finite sum of abstract non-best pairwise tail bounds.

This is the `ETC-COMMIT-ORACLE-CONCRETE-FILTERED-SUM-PAIRWISE-TAIL` leaf.  It
only specializes the already compiled abstract oracle filtered-sum consumer to
`ETC.argmaxCommitOracle`; it does not prove pairwise tails, add concentration,
introduce filtration, or prove final ETC regret.
-/
theorem prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_pairwise_tail
    {Omega : Type u} {K : Nat}
    [MeasurableSpace Omega]
    (hK : 0 < K)
    (mu : MeasureTheory.Measure Omega)
    (model : FiniteBanditModel K)
    (empMean : Omega -> Fin K -> Rat)
    (tail : Fin K -> ENNReal)
    (hpair_tail :
      forall a : Fin K, (a = model.bestArm -> False) ->
        mu {omega : Omega |
          empMean omega a >= empMean omega model.bestArm} <= tail a) :
    mu {omega : Omega |
        (ETC.argmaxCommitOracle hK).choose (empMean omega) =
          model.bestArm -> False} <=
    ((Finset.univ : Finset (Fin K)).filter
      (fun a : Fin K => a = model.bestArm -> False)).sum tail := by
  exact
    ETC.prob_commitOracle_ne_bestArm_le_filtered_sum_pairwise_tail
      mu
      model
      (ETC.argmaxCommitOracle hK)
      empMean
      tail
      (by
        intro scores a
        exact ETC.argmaxCommitOracle_choose_spec hK scores a)
      hpair_tail

end ETC
end BanditRLProof
