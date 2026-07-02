import Mathlib.Data.Rat.Encodable
import Mathlib.MeasureTheory.MeasurableSpace.Basic

/-!
# Rat measurability wrappers

This module contains narrow measurability wrappers for the project's Rat-valued
bandit quantities. It deliberately does not choose probability, filtration, or
concentration assumptions.
-/

namespace BanditRLProof

/--
Division by a fixed rational is measurable on a measurable singleton Rat space.

This is the `RAT-MEASURABLE-DIV-CONST-OF-MEASURABLE-SINGLETON` wrapper. It is
kept separate from the ETC empirical-mean theorem so later leaves can decide
whether to consume it or keep an explicit division contract.
-/
theorem measurable_rat_div_const
    [MeasurableSpace Rat] [MeasurableSingletonClass Rat]
    (c : Rat) :
    Measurable (fun x : Rat => x / c) := by
  exact measurable_of_countable (fun x : Rat => x / c)

end BanditRLProof
