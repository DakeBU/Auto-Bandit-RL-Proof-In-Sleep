import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-!
# Finite-prefix congruence for Ionescu-Tulcea trajectories

The infinite `Kernel.traj` construction has a finite marginal determined only
by the initial law and the step kernels used before the marginal endpoint.
These wrappers expose that fact in the form needed by environment-prefix
factorizations.
-/

namespace BanditRLProof

open MeasureTheory ProbabilityTheory

universe u

namespace KernelTrajectoryPrefix

/-- Two partial trajectories from time zero agree through `n` when their step
kernels agree strictly before `n`. -/
theorem partialTraj_zero_congr
    {X : Nat -> Type u} [forall n, MeasurableSpace (X n)]
    (kappa eta : (n : Nat) -> Kernel
      ((i : Finset.Iic n) -> X i) (X (n + 1)))
    [forall n, IsMarkovKernel (kappa n)]
    [forall n, IsMarkovKernel (eta n)]
    (n : Nat)
    (hstep : forall k, k < n -> kappa k = eta k) :
    Kernel.partialTraj kappa 0 n = Kernel.partialTraj eta 0 n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Kernel.partialTraj_succ_of_le (Nat.zero_le n),
        Kernel.partialTraj_succ_of_le (Nat.zero_le n),
        hstep n (Nat.lt_succ_self n),
        ih (fun k hk => hstep k (hk.trans (Nat.lt_succ_self n)))]

/-- The finite marginal of an Ionescu-Tulcea trajectory depends only on its
initial measure and the step kernels strictly before the endpoint. -/
theorem trajMeasure_map_frestrictLe_congr
    {X : Nat -> Type u} [forall n, MeasurableSpace (X n)]
    (mu0 nu0 : Measure (X 0))
    [IsProbabilityMeasure mu0] [IsProbabilityMeasure nu0]
    (kappa eta : (n : Nat) -> Kernel
      ((i : Finset.Iic n) -> X i) (X (n + 1)))
    [forall n, IsMarkovKernel (kappa n)]
    [forall n, IsMarkovKernel (eta n)]
    (n : Nat) (hinitial : mu0 = nu0)
    (hstep : forall k, k < n -> kappa k = eta k) :
    (Kernel.trajMeasure mu0 kappa).map (Preorder.frestrictLe n) =
      (Kernel.trajMeasure nu0 eta).map (Preorder.frestrictLe n) := by
  subst nu0
  rw [Kernel.trajMeasure, Kernel.trajMeasure,
    Measure.map_comp _ _ (Preorder.measurable_frestrictLe n),
    Measure.map_comp _ _ (Preorder.measurable_frestrictLe n),
    Kernel.traj_map_frestrictLe, Kernel.traj_map_frestrictLe,
    partialTraj_zero_congr kappa eta n hstep]

end KernelTrajectoryPrefix
end BanditRLProof
