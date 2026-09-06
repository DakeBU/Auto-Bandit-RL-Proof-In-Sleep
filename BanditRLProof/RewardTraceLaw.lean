import BanditRLProof.RewardKernel
import Mathlib.Probability.Process.FiniteDimensionalLaws

/-!
# Reward-trace law uniqueness

This module contains the process-law foundation shared by adaptive bandit
routes.  Initial reward marginals and successor regular conditional
distributions determine every finite prefix and hence the complete reward-trace
law.  The results are independent of any ETC/UCB/Thompson algorithm layer.
-/

namespace BanditRLProof
open MeasureTheory
open scoped ProbabilityTheory

namespace RewardKernel

/--
The zeroth coordinate of an Ionescu-Tulcea trajectory has the supplied initial
law.

This is a project-level wrapper over `trajMeasure`, `traj_map_frestrictLe`, and
`partialTraj_self`. It is general enough to be tracked as a Mathlib candidate.
-/
theorem trajMeasure_map_eval_zero
    {X : Nat -> Type*} [forall n, MeasurableSpace (X n)]
    (mu0 : Measure (X 0)) [IsProbabilityMeasure mu0]
    (kernel : (n : Nat) ->
      ProbabilityTheory.Kernel ((i : Finset.Iic n) -> X i) (X (n + 1)))
    [forall n, ProbabilityTheory.IsMarkovKernel (kernel n)] :
    Measure.map (fun trajectory : ((n : Nat) -> X n) => trajectory 0)
        (ProbabilityTheory.Kernel.trajMeasure mu0 kernel) = mu0 := by
  rw [ProbabilityTheory.Kernel.trajMeasure]
  rw [Measure.map_comp _ _ (measurable_pi_apply 0)]
  let evalPrefix : ((i : Finset.Iic 0) -> X i) -> X 0 :=
    fun history => history ⟨0, Finset.mem_Iic.mpr le_rfl⟩
  have heval : (fun trajectory : ((n : Nat) -> X n) => trajectory 0) =
      evalPrefix ∘ Preorder.frestrictLe 0 := by
    rfl
  have hrestrict : Measurable (Preorder.frestrictLe (π := X) 0) := by
    fun_prop
  have hevalPrefix : Measurable evalPrefix :=
    measurable_pi_apply
      (⟨0, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic 0)
  rw [heval,
    ProbabilityTheory.Kernel.map_comp_right _ hrestrict hevalPrefix,
    ProbabilityTheory.Kernel.traj_map_frestrictLe,
    ProbabilityTheory.Kernel.partialTraj_self,
    ProbabilityTheory.Kernel.id_map hevalPrefix,
    Measure.deterministic_comp_eq_map hevalPrefix,
    Measure.map_map hevalPrefix
      (MeasurableEquiv.piUnique (fun i : Finset.Iic 0 => X i)).symm.measurable]
  have hcomp : evalPrefix ∘
      (MeasurableEquiv.piUnique (fun i : Finset.Iic 0 => X i)).symm = id := by
    funext value
    rfl
  exact
    (congrArg (fun f => Measure.map f mu0) hcomp).trans Measure.map_id

/--
Finite reward-prefix law uniqueness from the initial marginal and successor
conditional distributions.

Only the conditional laws before `n` are required. The proof turns each
conditional-distribution identity into a joint prefix/next-reward law with
`condDistrib_ae_eq_iff_measure_eq_compProd`, then matches the corresponding
Ionescu-Tulcea recurrence.
-/
theorem rewardTrace_prefix_map_eq_trajMeasure_of_condDistrib
    {Omega Reward : Type*}
    [MeasurableSpace Omega]
    [MeasurableSpace Reward] [StandardBorelSpace Reward] [Nonempty Reward]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (mu0 : Measure Reward) [IsProbabilityMeasure mu0]
    (reward : Omega -> RewardTrace Reward)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (kernel : (n : Nat) ->
      ProbabilityTheory.Kernel ((i : Finset.Iic n) -> Reward) Reward)
    [forall n, ProbabilityTheory.IsMarkovKernel (kernel n)]
    (hzero : Measure.map (fun omega : Omega => reward omega 0) mu = mu0)
    (n : Nat)
    (hcond : forall i : Nat, i < n ->
      ProbabilityTheory.condDistrib
          (fun omega : Omega => reward omega (i + 1))
          (fun omega : Omega =>
            History.finiteRewardHistoryOfTrace (reward omega) i)
          mu =ᵐ[
            mu.map (fun omega : Omega =>
              History.finiteRewardHistoryOfTrace (reward omega) i)]
        kernel i) :
    Measure.map
        (fun omega : Omega =>
          History.finiteRewardHistoryOfTrace (reward omega) n) mu =
      Measure.map
        (fun trajectory : RewardTrace Reward =>
          History.finiteRewardHistoryOfTrace trajectory n)
        (ProbabilityTheory.Kernel.trajMeasure
          (X := fun _ : Nat => Reward) mu0 kernel) := by
  let trajMeasure := ProbabilityTheory.Kernel.trajMeasure
    (X := fun _ : Nat => Reward) mu0 kernel
  revert hcond
  induction n with
  | zero =>
      intro _hcond
      let singleton : Reward -> History.FiniteRewardHistory Reward 0 :=
        (MeasurableEquiv.piUnique
          (fun _i : Finset.Iic 0 => Reward)).symm
      let evalExternal : Omega -> Reward := fun omega => reward omega 0
      let evalCanonical : RewardTrace Reward -> Reward :=
        fun trajectory => trajectory 0
      let prefixExternal : Omega -> History.FiniteRewardHistory Reward 0 :=
        fun omega => History.finiteRewardHistoryOfTrace (reward omega) 0
      let prefixCanonical :
          RewardTrace Reward -> History.FiniteRewardHistory Reward 0 :=
        fun trajectory => History.finiteRewardHistoryOfTrace trajectory 0
      have hsingleton : Measurable singleton :=
        (MeasurableEquiv.piUnique
          (fun _i : Finset.Iic 0 => Reward)).symm.measurable
      have hevalExternal : Measurable evalExternal := hreward 0
      have hevalCanonical : Measurable evalCanonical := measurable_pi_apply 0
      have hprefixExternal : prefixExternal = singleton ∘ evalExternal := by
        funext omega
        funext i
        have hi : i.1 = 0 := Nat.eq_zero_of_le_zero (Finset.mem_Iic.mp i.2)
        simp [prefixExternal, singleton, evalExternal, hi]
      have hprefixCanonical : prefixCanonical = singleton ∘ evalCanonical := by
        funext trajectory
        funext i
        have hi : i.1 = 0 := Nat.eq_zero_of_le_zero (Finset.mem_Iic.mp i.2)
        simp [prefixCanonical, singleton, evalCanonical, hi]
      calc
        Measure.map prefixExternal mu =
            Measure.map (singleton ∘ evalExternal) mu := by rw [hprefixExternal]
        _ = Measure.map singleton (Measure.map evalExternal mu) := by
          exact (Measure.map_map hsingleton hevalExternal).symm
        _ = Measure.map singleton mu0 := by rw [hzero]
        _ = Measure.map singleton (Measure.map evalCanonical trajMeasure) := by
          rw [RewardKernel.trajMeasure_map_eval_zero]
        _ = Measure.map (singleton ∘ evalCanonical) trajMeasure := by
          exact Measure.map_map hsingleton hevalCanonical
        _ = Measure.map prefixCanonical trajMeasure := by rw [hprefixCanonical]
  | succ n ih =>
      intro hcond
      have ih := ih (fun i hi => hcond i (lt_trans hi (Nat.lt_succ_self n)))
      let prefixExternal : Omega -> History.FiniteRewardHistory Reward n :=
        fun omega => History.finiteRewardHistoryOfTrace (reward omega) n
      let prefixCanonical :
          RewardTrace Reward -> History.FiniteRewardHistory Reward n :=
        fun trajectory => History.finiteRewardHistoryOfTrace trajectory n
      let nextExternal : Omega -> Reward := fun omega => reward omega (n + 1)
      let nextCanonical : RewardTrace Reward -> Reward :=
        fun trajectory => trajectory (n + 1)
      let pairExternal : Omega -> History.FiniteRewardHistory Reward n × Reward :=
        fun omega => (prefixExternal omega, nextExternal omega)
      let pairCanonical :
          RewardTrace Reward -> History.FiniteRewardHistory Reward n × Reward :=
        fun trajectory => (prefixCanonical trajectory, nextCanonical trajectory)
      let extend :
          History.FiniteRewardHistory Reward n × Reward ->
            History.FiniteRewardHistory Reward (n + 1) :=
        fun value =>
          IicProdIoc (X := fun _ : Nat => Reward) n (n + 1)
            (value.1,
              (MeasurableEquiv.piSingleton
                (X := fun _ : Nat => Reward) n) value.2)
      have hprefixExternal : Measurable prefixExternal :=
        History.measurable_finiteRewardHistoryOfTrace reward hreward n
      have hprefixCanonical : Measurable prefixCanonical :=
        History.measurable_finiteRewardHistoryOfTrace
          (fun trajectory : RewardTrace Reward => trajectory)
          (fun t => measurable_pi_apply t) n
      have hnextExternal : Measurable nextExternal := hreward (n + 1)
      have hnextCanonical : Measurable nextCanonical := measurable_pi_apply (n + 1)
      have hpairExternal : Measurable pairExternal :=
        Measurable.prod hprefixExternal hnextExternal
      have hpairCanonical : Measurable pairCanonical :=
        Measurable.prod hprefixCanonical hnextCanonical
      have hextend : Measurable extend := by
        exact measurable_IicProdIoc.comp
          (Measurable.prod measurable_fst
            ((MeasurableEquiv.piSingleton
              (X := fun _ : Nat => Reward) n).measurable.comp measurable_snd))
      have hpairLaw : Measure.map pairExternal mu =
          Measure.map pairCanonical trajMeasure := by
        calc
          Measure.map pairExternal mu =
              Measure.map prefixExternal mu ⊗ₘ kernel n := by
            exact
              (ProbabilityTheory.condDistrib_ae_eq_iff_measure_eq_compProd
                prefixExternal hnextExternal.aemeasurable (kernel n)).mp
                (by simpa [prefixExternal, nextExternal, pairExternal] using
                  hcond n (Nat.lt_succ_self n))
          _ = Measure.map prefixCanonical trajMeasure ⊗ₘ kernel n := by
            rw [ih]
          _ = Measure.map pairCanonical trajMeasure := by
            have hprefix_eq : prefixCanonical = Preorder.frestrictLe n := by
              rfl
            have hpair_eq : pairCanonical =
                (fun trajectory : RewardTrace Reward =>
                  (Preorder.frestrictLe n trajectory, trajectory (n + 1))) := by
              rfl
            rw [hprefix_eq, hpair_eq]
            exact
              ProbabilityTheory.Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
                (X := fun _ : Nat => Reward)
                (μ₀ := mu0) (κ := kernel) (a := n)
      have hextendTrace : forall trace : RewardTrace Reward,
          extend
              (History.finiteRewardHistoryOfTrace trace n, trace (n + 1)) =
            History.finiteRewardHistoryOfTrace trace (n + 1) := by
        intro trace
        funext j
        by_cases hj : j.1 <= n
        · simp [extend, IicProdIoc, hj,
            History.finiteRewardHistoryOfTrace]
        · have hj_le : j.1 <= n + 1 := Finset.mem_Iic.mp j.2
          have hj_eq : j.1 = n + 1 := by omega
          simp [extend, IicProdIoc, MeasurableEquiv.piSingleton,
            History.finiteRewardHistoryOfTrace, hj_eq]
      have hextendExternal : forall omega : Omega,
          extend (pairExternal omega) =
            History.finiteRewardHistoryOfTrace (reward omega) (n + 1) := by
        intro omega
        change extend
            (History.finiteRewardHistoryOfTrace (reward omega) n,
              reward omega (n + 1)) = _
        exact hextendTrace (reward omega)
      have hextendCanonical : forall trajectory : RewardTrace Reward,
          extend (pairCanonical trajectory) =
            History.finiteRewardHistoryOfTrace trajectory (n + 1) := by
        intro trajectory
        change extend
            (History.finiteRewardHistoryOfTrace trajectory n,
              trajectory (n + 1)) = _
        exact hextendTrace trajectory
      calc
        Measure.map
            (fun omega : Omega =>
              History.finiteRewardHistoryOfTrace (reward omega) (n + 1)) mu =
            Measure.map (extend ∘ pairExternal) mu := by
          exact Measure.map_congr <| Filter.Eventually.of_forall <| fun omega =>
            (hextendExternal omega).symm
        _ = Measure.map extend (Measure.map pairExternal mu) := by
          exact (Measure.map_map hextend hpairExternal).symm
        _ = Measure.map extend (Measure.map pairCanonical trajMeasure) := by
          rw [hpairLaw]
        _ = Measure.map (extend ∘ pairCanonical) trajMeasure := by
          exact Measure.map_map hextend hpairCanonical
        _ = Measure.map
            (fun trajectory : RewardTrace Reward =>
              History.finiteRewardHistoryOfTrace trajectory (n + 1))
            trajMeasure := by
          exact Measure.map_congr <| Filter.Eventually.of_forall <| fun trajectory =>
            hextendCanonical trajectory

/--
The complete trace law is uniquely determined by its initial marginal and all
successor conditional distributions.

The finite-prefix theorem above handles every `Finset.Iic n`. Any finite set
of time coordinates embeds measurably into one such prefix, so the external
law and the Ionescu-Tulcea law have the same finite-dimensional marginals.
Mathlib's projective-limit uniqueness then identifies the full measures.
-/
theorem rewardTrace_map_eq_trajMeasure_of_condDistrib
    {Omega Reward : Type*}
    [MeasurableSpace Omega]
    [MeasurableSpace Reward] [StandardBorelSpace Reward] [Nonempty Reward]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (mu0 : Measure Reward) [IsProbabilityMeasure mu0]
    (reward : Omega -> RewardTrace Reward)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (kernel : (n : Nat) ->
      ProbabilityTheory.Kernel ((i : Finset.Iic n) -> Reward) Reward)
    [forall n, ProbabilityTheory.IsMarkovKernel (kernel n)]
    (hzero : Measure.map (fun omega : Omega => reward omega 0) mu = mu0)
    (hcond : forall i : Nat,
      ProbabilityTheory.condDistrib
          (fun omega : Omega => reward omega (i + 1))
          (fun omega : Omega =>
            History.finiteRewardHistoryOfTrace (reward omega) i)
          mu =ᵐ[mu.map (fun omega : Omega =>
            History.finiteRewardHistoryOfTrace (reward omega) i)]
        kernel i) :
    Measure.map reward mu =
      ProbabilityTheory.Kernel.trajMeasure
        (X := fun _ : Nat => Reward) mu0 kernel := by
  let trajMeasure := ProbabilityTheory.Kernel.trajMeasure
    (X := fun _ : Nat => Reward) mu0 kernel
  let finiteLaw := fun I : Finset Nat =>
    Measure.map I.restrict trajMeasure
  have hrewardTrace : Measurable reward :=
    measurable_pi_lambda _ hreward
  have hcanonical : MeasureTheory.IsProjectiveLimit trajMeasure finiteLaw := by
    intro I
    rfl
  have hexternal :
      MeasureTheory.IsProjectiveLimit (Measure.map reward mu) finiteLaw := by
    intro I
    let n := I.sup id
    have hi_le : forall i : I, i.1 <= n := by
      intro i
      simpa [n] using (Finset.le_sup (f := id) i.2)
    let select : History.FiniteRewardHistory Reward n -> ((i : I) -> Reward) :=
      fun history i =>
        history ⟨i.1, Finset.mem_Iic.mpr (hi_le i)⟩
    have hselect : Measurable select := by
      exact measurable_pi_lambda _ (fun i => measurable_pi_apply
        (⟨i.1, Finset.mem_Iic.mpr (hi_le i)⟩ : Finset.Iic n))
    have hprefixExternal : Measurable (fun omega : Omega =>
        History.finiteRewardHistoryOfTrace (reward omega) n) :=
      History.measurable_finiteRewardHistoryOfTrace reward hreward n
    have hprefixCanonical : Measurable (fun trajectory : RewardTrace Reward =>
        History.finiteRewardHistoryOfTrace trajectory n) :=
      History.measurable_finiteRewardHistoryOfTrace
        (fun trajectory : RewardTrace Reward => trajectory)
        (fun t => measurable_pi_apply t) n
    have hprefix := rewardTrace_prefix_map_eq_trajMeasure_of_condDistrib
      mu mu0 reward hreward kernel hzero n (fun i _hi => hcond i)
    have hfinite := congrArg (Measure.map select) hprefix
    rw [Measure.map_map hselect hprefixExternal,
      Measure.map_map hselect hprefixCanonical] at hfinite
    have hselectExternal : select ∘
        (fun omega : Omega =>
          History.finiteRewardHistoryOfTrace (reward omega) n) =
        fun omega => I.restrict (reward omega) := by
      funext omega i
      rfl
    have hselectCanonical : select ∘
        (fun trajectory : RewardTrace Reward =>
          History.finiteRewardHistoryOfTrace trajectory n) = I.restrict := by
      funext trajectory i
      rfl
    rw [hselectExternal, hselectCanonical] at hfinite
    rw [AEMeasurable.map_map_of_aemeasurable
      (Finset.measurable_restrict I).aemeasurable hrewardTrace.aemeasurable]
    exact hfinite
  simpa [trajMeasure] using hexternal.unique hcanonical

/--
Two complete traces are identically distributed when they share an initial
marginal and the same successor conditional-distribution kernels.
-/
theorem identDistrib_rewardTrace_of_common_condDistrib
    {Omega Xi Reward : Type*}
    [MeasurableSpace Omega] [MeasurableSpace Xi]
    [MeasurableSpace Reward] [StandardBorelSpace Reward] [Nonempty Reward]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (mu' : Measure Xi) [IsFiniteMeasure mu']
    (mu0 : Measure Reward) [IsProbabilityMeasure mu0]
    (reward : Omega -> RewardTrace Reward)
    (reward' : Xi -> RewardTrace Reward)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (hreward' : forall t : Nat,
      Measurable (fun xi : Xi => reward' xi t))
    (kernel : (n : Nat) ->
      ProbabilityTheory.Kernel ((i : Finset.Iic n) -> Reward) Reward)
    [forall n, ProbabilityTheory.IsMarkovKernel (kernel n)]
    (hzero : Measure.map (fun omega : Omega => reward omega 0) mu = mu0)
    (hzero' : Measure.map (fun xi : Xi => reward' xi 0) mu' = mu0)
    (hcond : forall i : Nat,
      ProbabilityTheory.condDistrib
          (fun omega : Omega => reward omega (i + 1))
          (fun omega : Omega =>
            History.finiteRewardHistoryOfTrace (reward omega) i)
          mu =ᵐ[mu.map (fun omega : Omega =>
            History.finiteRewardHistoryOfTrace (reward omega) i)]
        kernel i)
    (hcond' : forall i : Nat,
      ProbabilityTheory.condDistrib
          (fun xi : Xi => reward' xi (i + 1))
          (fun xi : Xi =>
            History.finiteRewardHistoryOfTrace (reward' xi) i)
          mu' =ᵐ[mu'.map (fun xi : Xi =>
            History.finiteRewardHistoryOfTrace (reward' xi) i)]
        kernel i) :
    ProbabilityTheory.IdentDistrib reward reward' mu mu' := by
  refine ⟨(measurable_pi_lambda _ hreward).aemeasurable,
    (measurable_pi_lambda _ hreward').aemeasurable, ?_⟩
  calc
    Measure.map reward mu =
        ProbabilityTheory.Kernel.trajMeasure
          (X := fun _ : Nat => Reward) mu0 kernel :=
      rewardTrace_map_eq_trajMeasure_of_condDistrib
        mu mu0 reward hreward kernel hzero hcond
    _ = Measure.map reward' mu' :=
      (rewardTrace_map_eq_trajMeasure_of_condDistrib
        mu' mu0 reward' hreward' kernel hzero' hcond').symm

end RewardKernel
end BanditRLProof
