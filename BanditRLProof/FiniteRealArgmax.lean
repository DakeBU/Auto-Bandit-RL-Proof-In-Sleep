import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import BanditRLProof.MeasurableLocalQuantities

/-!
# Measurable finite Real argmax

This module provides a fixed-enumeration maximizer for Real-valued scores on a
nonempty finite type.  Unlike a bare `Classical.choose` over existence of a
maximum, the explicit fold remains measurable when every score coordinate is
measurable in an external parameter.
-/

open MeasureTheory

universe u v

namespace BanditRLProof
namespace FiniteRealArgmax

private theorem score_le_foldl_select
    {K : Nat} (scores : Fin K -> Real) (init : Fin K) :
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
      exact And.intro (by intro _ ha; cases ha) (by simp)
  | arm :: rest => by
      let select := fun best arm : Fin K =>
        if scores best < scores arm then arm else best
      let next := select init arm
      have ih := score_le_foldl_select (scores := scores) next rest
      have harm_next : scores arm <= scores next := by
        exact if hlt : scores init < scores arm then
          by simp [next, select, hlt]
        else
          by simp [next, select, hlt, le_of_not_gt hlt]
      exact And.intro
        (by
          intro a ha
          cases ha with
          | head => exact le_trans harm_next ih.2
          | tail _ ha => exact ih.1 a ha)
        (by
          have hinit_next : scores init <= scores next := by
            exact if hlt : scores init < scores arm then
              by simpa [next, select, hlt] using le_of_lt hlt
            else
              by simp [next, select, hlt]
          exact le_trans hinit_next ih.2)

private noncomputable def chooseFin {K : Nat} (hK : 0 < K)
    (scores : Fin K -> Real) : Fin K :=
  (List.finRange K).foldl
    (fun best arm : Fin K =>
      if scores best < scores arm then arm else best)
    (Fin.mk 0 hK)

private theorem score_le_chooseFin {K : Nat} (hK : 0 < K)
    (scores : Fin K -> Real) (a : Fin K) :
    scores a <= scores (chooseFin hK scores) := by
  exact
    (score_le_foldl_select
      (scores := scores) (init := Fin.mk 0 hK) (List.finRange K)).1
      a (List.mem_finRange a)

private theorem measurable_selected_score
    {Omega : Type u} {K : Nat} [MeasurableSpace Omega]
    (scores : Omega -> Fin K -> Real)
    (hscores : forall a : Fin K,
      Measurable (fun omega : Omega => scores omega a))
    (best : Omega -> Fin K) (hbest : Measurable best) :
    Measurable (fun omega : Omega => scores omega (best omega)) := by
  classical
  have hsum : Measurable (fun omega : Omega =>
      (Finset.univ : Finset (Fin K)).sum (fun a =>
        if best omega = a then scores omega a else 0)) := by
    refine Finset.measurable_sum _ ?_
    intro a _ha
    exact Measurable.ite
      (measurableSet_eq_fun hbest measurable_const)
      (hscores a) measurable_const
  convert hsum using 1
  funext omega
  simp

private theorem measurable_foldl_select
    {Omega : Type u} {K : Nat} [MeasurableSpace Omega]
    (scores : Omega -> Fin K -> Real)
    (hscores : forall a : Fin K,
      Measurable (fun omega : Omega => scores omega a))
    (best : Omega -> Fin K) (hbest : Measurable best) :
    forall l : List (Fin K),
      Measurable (fun omega : Omega =>
        l.foldl
          (fun best arm : Fin K =>
            if scores omega best < scores omega arm then arm else best)
          (best omega))
  | [] => by simpa using hbest
  | arm :: rest => by
      have hselected : Measurable (fun omega : Omega =>
          scores omega (best omega)) :=
        measurable_selected_score scores hscores best hbest
      have hnext : Measurable (fun omega : Omega =>
          if scores omega (best omega) < scores omega arm then
            arm
          else
            best omega) :=
        Measurable.ite
          (measurableSet_lt hselected (hscores arm))
          measurable_const hbest
      simpa using
        (measurable_foldl_select scores hscores
          (fun omega : Omega =>
            if scores omega (best omega) < scores omega arm then
              arm
            else
              best omega)
          hnext rest)

private theorem measurable_chooseFin_of_forall_measurable
    {Omega : Type u} {K : Nat} [MeasurableSpace Omega]
    (hK : 0 < K) (scores : Omega -> Fin K -> Real)
    (hscores : forall a : Fin K,
      Measurable (fun omega : Omega => scores omega a)) :
    Measurable (fun omega : Omega => chooseFin hK (scores omega)) := by
  unfold chooseFin
  exact measurable_foldl_select scores hscores
    (fun _omega : Omega => Fin.mk 0 hK) measurable_const (List.finRange K)

/-- A fixed-enumeration maximizer on a nonempty finite type. -/
noncomputable def choose {alpha : Type v} [Fintype alpha] [Nonempty alpha]
    (scores : alpha -> Real) : alpha :=
  let equiv := Fintype.equivFin alpha
  equiv.symm
    (chooseFin (Fintype.card_pos_iff.mpr inferInstance)
      (fun index => scores (equiv.symm index)))

/-- Every score is bounded by the score selected by `choose`. -/
theorem score_le_choose {alpha : Type v} [Fintype alpha] [Nonempty alpha]
    (scores : alpha -> Real) (a : alpha) :
    scores a <= scores (choose scores) := by
  let equiv := Fintype.equivFin alpha
  have hmax := score_le_chooseFin
    (Fintype.card_pos_iff.mpr inferInstance)
    (fun index => scores (equiv.symm index)) (equiv a)
  simpa [choose, equiv] using hmax

/-- The fixed-enumeration maximizer is measurable in external parameters. -/
theorem measurable_choose_of_forall_measurable
    {Omega : Type u} {alpha : Type v}
    [MeasurableSpace Omega] [MeasurableSpace alpha]
    [Fintype alpha] [Nonempty alpha]
    (scores : Omega -> alpha -> Real)
    (hscores : forall a : alpha,
      Measurable (fun omega : Omega => scores omega a)) :
    Measurable (fun omega : Omega => choose (scores omega)) := by
  let equiv := Fintype.equivFin alpha
  have hfin : Measurable (fun omega : Omega =>
      chooseFin (Fintype.card_pos_iff.mpr inferInstance)
        (fun index => scores omega (equiv.symm index))) :=
    measurable_chooseFin_of_forall_measurable
      (Fintype.card_pos_iff.mpr inferInstance)
      (fun omega index => scores omega (equiv.symm index))
      (fun index => hscores (equiv.symm index))
  exact (measurable_of_finite equiv.symm).comp hfin

/-- Evaluation at a measurable finite-valued selector preserves measurability. -/
theorem measurable_selected_score_of_forall_measurable
    {Omega : Type u} {alpha : Type v}
    [MeasurableSpace Omega] [MeasurableSpace alpha]
    [Fintype alpha] [MeasurableSingletonClass alpha]
    (scores : Omega -> alpha -> Real)
    (hscores : forall a : alpha,
      Measurable (fun omega : Omega => scores omega a))
    (selected : Omega -> alpha) (hselected : Measurable selected) :
    Measurable (fun omega : Omega => scores omega (selected omega)) := by
  classical
  have hsum : Measurable (fun omega : Omega =>
      (Finset.univ : Finset alpha).sum (fun a =>
        if selected omega = a then scores omega a else 0)) := by
    refine Finset.measurable_sum _ ?_
    intro a _ha
    exact Measurable.ite
      (measurableSet_eq_fun hselected measurable_const)
      (hscores a) measurable_const
  convert hsum using 1
  funext omega
  simp

end FiniteRealArgmax
end BanditRLProof
