import BanditRLProof.FiniteArmRewardKernelLaw

/-!
# Uniform variance proxies over finite context-action families

This module computes one common `NNReal` proxy for a finite context space and
finite arm set. It is independent of any particular bandit algorithm.
-/

namespace BanditRLProof
namespace Concentration

/-- The largest variance proxy over a finite context-action family. -/
noncomputable def finiteContextArmVarianceProxy
    {Context : Type} [Fintype Context] {K : Nat}
    (varianceProxy : Context -> Fin K -> NNReal) : NNReal :=
  Finset.univ.sup fun context => Finset.univ.sup (varianceProxy context)

/-- Every context-action proxy is bounded by the finite-family maximum. -/
theorem varianceProxy_le_finiteContextArmVarianceProxy
    {Context : Type} [Fintype Context] {K : Nat}
    (varianceProxy : Context -> Fin K -> NNReal)
    (context : Context) (arm : Fin K) :
    varianceProxy context arm <=
      finiteContextArmVarianceProxy varianceProxy := by
  apply le_trans
    (Finset.le_sup
      (s := (Finset.univ : Finset (Fin K)))
      (f := varianceProxy context)
      (Finset.mem_univ arm))
  exact Finset.le_sup
    (s := (Finset.univ : Finset Context))
    (f := fun context => Finset.univ.sup (varianceProxy context))
    (Finset.mem_univ context)

/-- A positive member makes the finite context-action maximum positive. -/
theorem finiteContextArmVarianceProxy_pos_of_exists
    {Context : Type} [Fintype Context] {K : Nat}
    (varianceProxy : Context -> Fin K -> NNReal)
    (hpos : exists context arm,
      0 < ((varianceProxy context arm : NNReal) : Real)) :
    0 < ((finiteContextArmVarianceProxy varianceProxy : NNReal) : Real) := by
  rcases hpos with ⟨context, arm, hproxy⟩
  have hle := varianceProxy_le_finiteContextArmVarianceProxy
    varianceProxy context arm
  exact hproxy.trans_le (by exact_mod_cast hle)

/--
The finite context-action maximum padded by one. This gives algorithms that
require a strictly positive tuning parameter a uniform proxy even when every
genuine variance proxy is zero.
-/
noncomputable def finiteContextArmPositiveVarianceProxy
    {Context : Type} [Fintype Context] {K : Nat}
    (varianceProxy : Context -> Fin K -> NNReal) : NNReal :=
  max 1 (finiteContextArmVarianceProxy varianceProxy)

/-- Every genuine proxy is bounded by the positive padded proxy. -/
theorem varianceProxy_le_finiteContextArmPositiveVarianceProxy
    {Context : Type} [Fintype Context] {K : Nat}
    (varianceProxy : Context -> Fin K -> NNReal)
    (context : Context) (arm : Fin K) :
    varianceProxy context arm <=
      finiteContextArmPositiveVarianceProxy varianceProxy := by
  exact
    (varianceProxy_le_finiteContextArmVarianceProxy
      varianceProxy context arm).trans (le_max_right _ _)

/-- The padded finite context-action proxy is always strictly positive. -/
theorem finiteContextArmPositiveVarianceProxy_pos
    {Context : Type} [Fintype Context] {K : Nat}
    (varianceProxy : Context -> Fin K -> NNReal) :
    0 < ((finiteContextArmPositiveVarianceProxy varianceProxy : NNReal) : Real) := by
  have hone :
      (1 : NNReal) <= finiteContextArmPositiveVarianceProxy varianceProxy :=
    le_max_left _ _
  exact zero_lt_one.trans_le (by exact_mod_cast hone)

end Concentration
end BanditRLProof
