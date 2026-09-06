import Mathlib.Probability.Process.HittingTime

/-!
# Budget stopping-time wrappers

This module exposes a narrow Mathlib-backed stopping-time surface for
resource/budget processes.  It deliberately stays at the filtration foundation
layer: no knapsack model, policy construction, optional stopping theorem, or
regret theorem is introduced here.
-/

namespace BanditRLProof
namespace Budget

open MeasureTheory
open scoped MeasureTheory

/--
First time an accumulated `Nat` resource process reaches a budget.

This is a project-local name for Mathlib's `hittingAfter` specialized to the
upper set `{spent >= budget}` and start time `0`.
-/
noncomputable def budgetExhaustionTime
    {Omega : Type u}
    (spent : Nat -> Omega -> Nat) (budget : Nat) :
    Omega -> WithTop Nat :=
  MeasureTheory.hittingAfter spent (Set.Ici budget) (0 : Nat)

/--
An adapted accumulated-resource process has a budget-exhaustion stopping time.

This is the `STOPPING-TIME-BUDGET` wrapper over
`MeasureTheory.Adapted.isStoppingTime_hittingAfter`.
-/
theorem isStoppingTime_budgetExhaustionTime_of_adapted
    {Omega : Type u} [mOmega : MeasurableSpace Omega]
    {F : Filtration Nat mOmega}
    {spent : Nat -> Omega -> Nat} (budget : Nat)
    (hspent : Adapted F spent) :
    IsStoppingTime F (budgetExhaustionTime spent budget) := by
  unfold budgetExhaustionTime
  exact hspent.isStoppingTime_hittingAfter measurableSet_Ici

/--
At each horizon `n`, the event that the budget has already been exhausted is
measurable at filtration level `n`.
-/
theorem measurableSet_budgetExhaustionTime_le_of_adapted
    {Omega : Type u} [mOmega : MeasurableSpace Omega]
    {F : Filtration Nat mOmega}
    {spent : Nat -> Omega -> Nat} (budget n : Nat)
    (hspent : Adapted F spent) :
    MeasurableSet[F n]
      {omega | budgetExhaustionTime spent budget omega <= n} :=
  (isStoppingTime_budgetExhaustionTime_of_adapted
    (F := F) (spent := spent) budget hspent).measurableSet_le n

end Budget
end BanditRLProof
