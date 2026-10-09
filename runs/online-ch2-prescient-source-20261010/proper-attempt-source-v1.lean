import BanditRLProof.OnlinePrescientBregmanRegret

/-!
Source-domain/properness and unique-update transports for the required Chapter2
prescient forward dependency in Orabona v10, Algorithm15.8/Theorem15.30.
The source guarantee concerns valid interior argmin runs. Closedness and strict
convexity are not universal attainment assumptions; the existing exponential
counterexample and Option failure boundary remain in force. Source wrappers
retain literal finite-dimensional/closedness premises. The same shared loss,
divergence, selector and recursion are reused. No new per-Book project.
See docs/contracts/online-ch2-prescient-source-v1/stabilized-v1.json.
-/

noncomputable section
open Set Finset
open BanditRL.OnlineBregman
set_option autoImplicit false

namespace BanditRL.OnlineConvex
variable {E : Type*}

theorem sourceProper_of_domain (f : E → EReal) (V : Set E)
    (hV : V.Nonempty) (hbot : ∀ z, f z ≠ ⊥)
    (hdom : V ⊆ effectiveDomain f) :
    SourceProper f := by
  refine ⟨hbot, ?_⟩
  obtain ⟨z, hz⟩ := hV
  exact ⟨z, (f z).toReal, (EReal.coe_toReal (ne_of_lt (hdom hz)) (hbot z)).symm⟩

end BanditRL.OnlineConvex
