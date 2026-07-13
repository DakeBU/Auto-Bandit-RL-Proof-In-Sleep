import BanditRLProof.Algorithms.ETCGeneratedHistoryPolicy
import BanditRLProof.Algorithms.ETCCondSubGaussianWitnesses
import BanditRLProof.ConcentrationSubGaussian
import BanditRLProof.MeasurableRegret

/-!
# Finite-arm reward laws for the generated-history ETC route

This module turns bounded arm-indexed probability laws with the finite-bandit
model means into the centered reward-kernel contract consumed by the canonical
ETC trajectory theorem. It then exposes the resulting conditional
sub-Gaussian MGF directly, without an abstract centered-law or variance-ceiling
argument.

It also assembles the complete selected centered-reward finite-sum tail, the
pairwise empirical-mean wrong-commit probability, and both max-gap and per-arm
Bochner expected-regret bounds for the generated ETC action under the canonical
trajectory. The first transport layer extends both bounds to external reward
processes with an equal exploration-prefix pushforward. The conditional-law
layer then derives that identity from an initial marginal plus successor
conditional-distribution laws for both bounds. The practical adapters state
the successor laws directly as the stationary laws of the scheduled
exploration arms for both bounds. The LML-shaped adapters further coarsen those
constant laws from complete action/reward histories to reward-only prefixes for
both bounds. The seed-shaped adapters then use exploration-action a.e. equality
to reduce action-dependent feedback kernels to those constant laws for both
bounds. These results do not prove the exact upstream LML theorem.
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
A constant conditional distribution given a fine conditioning variable stays
constant after projecting to any measurable coarser conditioning variable.

The proof uses the defining joint-law identity for `condDistrib`: the fine
joint law is a product because the kernel is constant, and mapping that product
by `(project, id)` gives the corresponding coarse joint law.
-/
theorem condDistrib_ae_eq_const_of_comp
    {Omega Fine Coarse Target : Type*}
    [MeasurableSpace Omega] [MeasurableSpace Fine]
    [MeasurableSpace Coarse] [MeasurableSpace Target]
    [StandardBorelSpace Target] [Nonempty Target]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (fine : Omega -> Fine) (hfine : Measurable fine)
    (coarse : Omega -> Coarse)
    (target : Omega -> Target) (htarget : Measurable target)
    (project : Fine -> Coarse) (hproject : Measurable project)
    (hcomp : coarse = project ∘ fine)
    (Q : Measure Target) [IsProbabilityMeasure Q]
    (hcond : ProbabilityTheory.condDistrib target fine mu =ᵐ[mu.map fine]
      ProbabilityTheory.Kernel.const Fine Q) :
    ProbabilityTheory.condDistrib target coarse mu =ᵐ[mu.map coarse]
      ProbabilityTheory.Kernel.const Coarse Q := by
  refine
    (ProbabilityTheory.condDistrib_ae_eq_iff_measure_eq_compProd
      coarse htarget.aemeasurable
      (ProbabilityTheory.Kernel.const Coarse Q)).mpr ?_
  have hfineJoint :
      Measure.map (fun omega : Omega => (fine omega, target omega)) mu =
        Measure.map fine mu ⊗ₘ ProbabilityTheory.Kernel.const Fine Q :=
    (ProbabilityTheory.condDistrib_ae_eq_iff_measure_eq_compProd
      fine htarget.aemeasurable
      (ProbabilityTheory.Kernel.const Fine Q)).mp hcond
  calc
    Measure.map (fun omega : Omega => (coarse omega, target omega)) mu =
        Measure.map (Prod.map project id)
          (Measure.map (fun omega : Omega => (fine omega, target omega)) mu) := by
      rw [Measure.map_map (hproject.prodMap measurable_id)
        (hfine.prod htarget)]
      congr 1
      funext omega
      rw [hcomp]
      rfl
    _ = Measure.map (Prod.map project id)
          (Measure.map fine mu ⊗ₘ ProbabilityTheory.Kernel.const Fine Q) := by
      rw [hfineJoint]
    _ = Measure.map (Prod.map project id) ((Measure.map fine mu).prod Q) := by
      rw [Measure.compProd_const]
    _ = (Measure.map project (Measure.map fine mu)).prod
          (Measure.map id Q) := by
      exact (Measure.map_prod_map (Measure.map fine mu) Q
        hproject measurable_id).symm
    _ = (Measure.map coarse mu).prod Q := by
      rw [Measure.map_map hproject hfine, Measure.map_id, hcomp]
    _ = Measure.map coarse mu ⊗ₘ
          ProbabilityTheory.Kernel.const Coarse Q := by
      rw [Measure.compProd_const]

/-- A constant conditional distribution determines the target marginal. -/
theorem map_eq_of_condDistrib_ae_eq_const
    {Omega Condition Target : Type*}
    [MeasurableSpace Omega] [MeasurableSpace Condition]
    [MeasurableSpace Target]
    [StandardBorelSpace Target] [Nonempty Target]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (condition : Omega -> Condition) (hcondition : Measurable condition)
    (target : Omega -> Target) (htarget : Measurable target)
    (Q : Measure Target) [IsProbabilityMeasure Q]
    (hcond : ProbabilityTheory.condDistrib target condition mu =ᵐ[mu.map condition]
      ProbabilityTheory.Kernel.const Condition Q) :
    Measure.map target mu = Q := by
  have hJoint :
      Measure.map (fun omega : Omega => (condition omega, target omega)) mu =
        Measure.map condition mu ⊗ₘ
          ProbabilityTheory.Kernel.const Condition Q :=
    (ProbabilityTheory.condDistrib_ae_eq_iff_measure_eq_compProd
      condition htarget.aemeasurable
      (ProbabilityTheory.Kernel.const Condition Q)).mp hcond
  letI : IsProbabilityMeasure (Measure.map condition mu) :=
    Measure.isProbabilityMeasure_map hcondition.aemeasurable
  calc
    Measure.map target mu =
        (Measure.map (fun omega : Omega =>
          (condition omega, target omega)) mu).snd := by
      exact (Measure.snd_map_prodMk hcondition).symm
    _ = (Measure.map condition mu ⊗ₘ
          ProbabilityTheory.Kernel.const Condition Q).snd := by
      rw [hJoint]
    _ = ((Measure.map condition mu).prod Q).snd := by
      rw [Measure.compProd_const]
    _ = Q := Measure.snd_prod

/--
An action-selected conditional kernel becomes constant when the selected value
is almost surely constant under the source process.

The selector equality is pushed to the conditioning-variable law with
`ae_map_iff`; the supplied pointwise kernel-selection identity then rewrites
the conditional kernel almost everywhere.
-/
theorem condDistrib_ae_eq_const_of_ae_eq_selected
    {Omega Fine Action Target : Type*}
    [MeasurableSpace Omega] [MeasurableSpace Fine]
    [MeasurableSpace Action] [MeasurableEq Action]
    [MeasurableSpace Target] [StandardBorelSpace Target] [Nonempty Target]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (fine : Omega -> Fine) (hfine : Measurable fine)
    (target : Omega -> Target)
    (selected : Fine -> Action) (hselected : Measurable selected)
    (kernel : ProbabilityTheory.Kernel Fine Target)
    (actionLaw : Action -> Measure Target)
    (selectedValue : Action)
    (hselectedValue :
      (fun omega : Omega => selected (fine omega)) =ᵐ[mu]
        fun _omega => selectedValue)
    (hkernel : forall value : Fine,
      kernel value = actionLaw (selected value))
    (hcond : ProbabilityTheory.condDistrib target fine mu =ᵐ[mu.map fine]
      kernel) :
    ProbabilityTheory.condDistrib target fine mu =ᵐ[mu.map fine]
      ProbabilityTheory.Kernel.const Fine (actionLaw selectedValue) := by
  have hselectedMap :
      (fun value : Fine => selected value) =ᵐ[mu.map fine]
        fun _value => selectedValue := by
    rw [Filter.EventuallyEq, ae_map_iff hfine.aemeasurable
      (measurableSet_eq_fun hselected measurable_const)]
    exact hselectedValue
  filter_upwards [hcond, hselectedMap] with value hvalue hselectedEq
  simpa [hkernel value, hselectedEq,
    ProbabilityTheory.Kernel.const_apply] using hvalue

end RewardKernel

namespace ETC

/--
Exact model means and direct per-arm sub-Gaussian witnesses turn finite-arm
probability laws into a context-independent centered reward-kernel law.

Unlike `finiteArmBoundedCenteredRewardKernelLaw`, this constructor does not
derive the MGF from common bounded support. The supplied proxy is shared by
all arms, matching the concentration contract of the LML ETC theorem while
retaining ABRL's current `Rat` reward trace.
-/
noncomputable def finiteArmCenteredRewardKernelLaw_of_hasSubgaussianMGF
    {K : Nat} {Context : Type}
    [MeasurableSpace Context]
    (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (sigma2 : NNReal)
    (hmean : forall arm, integral (armLaw arm)
      (fun reward : Rat => (((reward : Rat) : Real))) =
        (((model.mean arm : Rat) : Real)))
    (hsubG : forall arm, ProbabilityTheory.HasSubgaussianMGF
      (fun reward : Rat =>
        ((reward : Rat) : Real) - (((model.mean arm : Rat) : Real)))
      sigma2 (armLaw arm)) :
    RewardKernel.CenteredRewardKernelLaw
      (RewardKernel.contextIndependentOfActionLaws
        (Context := Context) armLaw hprob)
      (fun _ arm => model.mean arm)
      (fun _ _ => sigma2) where
  integrable := by
    intro context arm
    rw [RewardKernel.selectedMeasure_contextIndependentOfActionLaws]
    simpa [Rat.cast_sub] using (hsubG arm).integrable
  integral_eq_zero := by
    intro context arm
    haveI : IsProbabilityMeasure (armLaw arm) := hprob arm
    have hcenter := (hsubG arm).integrable
    have hconst : Integrable
        (fun _reward : Rat => (((model.mean arm : Rat) : Real)))
        (armLaw arm) := integrable_const _
    have hraw : Integrable
        (fun reward : Rat => (((reward : Rat) : Real))) (armLaw arm) := by
      convert hcenter.add hconst using 1
      funext reward
      simp
    rw [RewardKernel.selectedMeasure_contextIndependentOfActionLaws]
    simp_rw [Rat.cast_sub]
    rw [integral_sub hraw hconst, hmean arm]
    simp
  hasSubgaussianMGF := by
    intro context arm
    rw [RewardKernel.selectedMeasure_contextIndependentOfActionLaws]
    simpa [Rat.cast_sub] using hsubG arm

/--
Common boundedness and exact model means turn finite-arm probability laws into
a context-independent centered reward-kernel law.

The variance proxy is the common Hoeffding proxy for `[lo, hi]`. Raw reward
integrability follows from `Integrable.of_mem_Icc`; the centered MGF is the
Mathlib-backed bounded-variable wrapper in `ConcentrationSubGaussian`.
-/
noncomputable def finiteArmBoundedCenteredRewardKernelLaw
    {K : Nat} {Context : Type}
    [MeasurableSpace Context]
    (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (lo hi : Real)
    (hmeas : forall arm, AEMeasurable
      (fun reward : Rat => (((reward : Rat) : Real))) (armLaw arm))
    (hbound : forall arm, Filter.Eventually
      (fun reward : Rat => Set.Icc lo hi (((reward : Rat) : Real)))
      (ae (armLaw arm)))
    (hmean : forall arm, integral (armLaw arm)
      (fun reward : Rat => (((reward : Rat) : Real))) =
        (((model.mean arm : Rat) : Real))) :
    RewardKernel.CenteredRewardKernelLaw
      (RewardKernel.contextIndependentOfActionLaws
        (Context := Context) armLaw hprob)
      (fun _ arm => model.mean arm)
      (fun _ _ => Concentration.intervalVarianceProxy lo hi) where
  integrable := by
    intro context arm
    haveI : IsProbabilityMeasure (armLaw arm) := hprob arm
    have hraw : Integrable
        (fun reward : Rat => (((reward : Rat) : Real))) (armLaw arm) :=
      Integrable.of_mem_Icc lo hi (hmeas arm) (hbound arm)
    have hcenter := hraw.sub (integrable_const
      (((model.mean arm : Rat) : Real)))
    simpa [Rat.cast_sub] using hcenter
  integral_eq_zero := by
    intro context arm
    haveI : IsProbabilityMeasure (armLaw arm) := hprob arm
    have hraw : Integrable
        (fun reward : Rat => (((reward : Rat) : Real))) (armLaw arm) :=
      Integrable.of_mem_Icc lo hi (hmeas arm) (hbound arm)
    have hconst : Integrable
        (fun _reward : Rat => (((model.mean arm : Rat) : Real)))
        (armLaw arm) := integrable_const _
    rw [RewardKernel.selectedMeasure_contextIndependentOfActionLaws]
    simp_rw [Rat.cast_sub]
    rw [integral_sub hraw hconst, hmean arm]
    simp
  hasSubgaussianMGF := by
    intro context arm
    haveI : IsProbabilityMeasure (armLaw arm) := hprob arm
    rw [RewardKernel.selectedMeasure_contextIndependentOfActionLaws]
    simpa [Rat.cast_sub] using
      (Concentration.boundedCentered_hasSubgaussianMGF_of_mem_Icc_integral_eq
        (mu := armLaw arm)
        (X := fun reward : Rat => (((reward : Rat) : Real)))
        (lo := lo) (hi := hi)
        (mean := (((model.mean arm : Rat) : Real)))
        (hmeas arm) (hbound arm) (hmean arm))

/--
Canonical generated-history ETC conditional MGF from bounded finite-arm laws.

Because every arm uses the same interval `[lo, hi]`, the kernel variance proxy
is constant. The selected-history variance ceiling required by the generic
trajectory theorem is therefore discharged by reflexivity.
-/
theorem explorationArgmaxHistory_centeredReward_succ_hasCondSubgaussianMGF_of_boundedArmLaws
    {K : Nat} {Context : Type}
    [MeasurableSpace Context]
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (mu0 : Measure Rat) [IsProbabilityMeasure mu0]
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (lo hi : Real)
    (hmeas : forall arm, AEMeasurable
      (fun reward : Rat => (((reward : Rat) : Real))) (armLaw arm))
    (hbound : forall arm, Filter.Eventually
      (fun reward : Rat => Set.Icc lo hi (((reward : Rat) : Real)))
      (ae (armLaw arm)))
    (hmean : forall arm, integral (armLaw arm)
      (fun reward : Rat => (((reward : Rat) : Real))) =
        (((model.mean arm : Rat) : Real)))
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (hcontext : forall n : Nat, Measurable (context n))
    (i : Nat) :
    let rewardKernel := RewardKernel.contextIndependentOfActionLaws
      (Context := Context) armLaw hprob
    let policy := fun t => ETC.explorationArgmaxHistoryPolicy spec model t
    let state := fun t history => ETC.explorationArgmaxHistoryState t history
    let stepKernel :=
      RewardKernel.historyStepKernelFamily rewardKernel policy context state
        hcontext (fun t => ETC.measurable_explorationArgmaxHistoryState t)
    let trajMeasure :=
      ProbabilityTheory.Kernel.trajMeasure
        (X := fun _ : Nat => Rat) mu0 stepKernel
    let reward : RewardTrace Rat -> RewardTrace Rat := fun trajectory => trajectory
    let hreward : forall t : Nat,
        Measurable (fun trajectory : RewardTrace Rat => reward trajectory t) :=
      fun t => measurable_pi_apply t
    ProbabilityTheory.HasCondSubgaussianMGF
      ((History.historyFiltrationSucc
        (ConditionalExpectationReward.generatedActionFromRewardHistory
          policy state (ETC.exploreArm spec 0) reward)
        reward
        (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
          (policy := policy) (state := state)
          (defaultAction := ETC.exploreArm spec 0) (reward := reward)
          hreward (fun t => ETC.measurable_explorationArgmaxHistoryState t))
        hreward) i)
      ((History.historyFiltrationSucc
        (ConditionalExpectationReward.generatedActionFromRewardHistory
          policy state (ETC.exploreArm spec 0) reward)
        reward
        (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
          (policy := policy) (state := state)
          (defaultAction := ETC.exploreArm spec 0) (reward := reward)
          hreward (fun t => ETC.measurable_explorationArgmaxHistoryState t))
        hreward).le i)
      (fun trajectory : RewardTrace Rat =>
        (((reward trajectory (i + 1) -
          model.mean
            ((policy i).action
              (state i
                (History.finiteRewardHistoryOfTrace (reward trajectory) i))) :
          Rat) : Real)))
      (Concentration.intervalVarianceProxy lo hi) trajMeasure := by
  let rewardKernel := RewardKernel.contextIndependentOfActionLaws
    (Context := Context) armLaw hprob
  let law := finiteArmBoundedCenteredRewardKernelLaw
    (Context := Context) model armLaw hprob lo hi hmeas hbound hmean
  exact
    ETC.explorationArgmaxHistory_centeredReward_succ_hasCondSubgaussianMGF_trajMeasure
      spec model mu0 rewardKernel context hcontext
      (fun _ _ => Concentration.intervalVarianceProxy lo hi)
      law i (Concentration.intervalVarianceProxy lo hi)
      (fun _history => le_rfl)

/--
Canonical generated-history ETC successor conditional MGF from direct
finite-arm sub-Gaussian laws with a common variance proxy.

The theorem removes common bounded support from the canonical kernel route.
Its remaining contracts are exact model means, a shared per-arm MGF proxy,
and measurable history context; the reward trace is still `Rat`-valued.
-/
theorem explorationArgmaxHistory_centeredReward_succ_hasCondSubgaussianMGF_of_armLaws
    {K : Nat} {Context : Type}
    [MeasurableSpace Context]
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (mu0 : Measure Rat) [IsProbabilityMeasure mu0]
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (sigma2 : NNReal)
    (hmean : forall arm, integral (armLaw arm)
      (fun reward : Rat => (((reward : Rat) : Real))) =
        (((model.mean arm : Rat) : Real)))
    (hsubG : forall arm, ProbabilityTheory.HasSubgaussianMGF
      (fun reward : Rat =>
        ((reward : Rat) : Real) - (((model.mean arm : Rat) : Real)))
      sigma2 (armLaw arm))
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (hcontext : forall n : Nat, Measurable (context n))
    (i : Nat) :
    let rewardKernel := RewardKernel.contextIndependentOfActionLaws
      (Context := Context) armLaw hprob
    let policy := fun t => ETC.explorationArgmaxHistoryPolicy spec model t
    let state := fun t history => ETC.explorationArgmaxHistoryState t history
    let stepKernel :=
      RewardKernel.historyStepKernelFamily rewardKernel policy context state
        hcontext (fun t => ETC.measurable_explorationArgmaxHistoryState t)
    let trajMeasure :=
      ProbabilityTheory.Kernel.trajMeasure
        (X := fun _ : Nat => Rat) mu0 stepKernel
    let reward : RewardTrace Rat -> RewardTrace Rat := fun trajectory => trajectory
    let hreward : forall t : Nat,
        Measurable (fun trajectory : RewardTrace Rat => reward trajectory t) :=
      fun t => measurable_pi_apply t
    ProbabilityTheory.HasCondSubgaussianMGF
      ((History.historyFiltrationSucc
        (ConditionalExpectationReward.generatedActionFromRewardHistory
          policy state (ETC.exploreArm spec 0) reward)
        reward
        (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
          (policy := policy) (state := state)
          (defaultAction := ETC.exploreArm spec 0) (reward := reward)
          hreward (fun t => ETC.measurable_explorationArgmaxHistoryState t))
        hreward) i)
      ((History.historyFiltrationSucc
        (ConditionalExpectationReward.generatedActionFromRewardHistory
          policy state (ETC.exploreArm spec 0) reward)
        reward
        (ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
          (policy := policy) (state := state)
          (defaultAction := ETC.exploreArm spec 0) (reward := reward)
          hreward (fun t => ETC.measurable_explorationArgmaxHistoryState t))
        hreward).le i)
      (fun trajectory : RewardTrace Rat =>
        (((reward trajectory (i + 1) -
          model.mean
            ((policy i).action
              (state i
                (History.finiteRewardHistoryOfTrace (reward trajectory) i))) :
          Rat) : Real)))
      sigma2 trajMeasure := by
  let rewardKernel := RewardKernel.contextIndependentOfActionLaws
    (Context := Context) armLaw hprob
  let law := finiteArmCenteredRewardKernelLaw_of_hasSubgaussianMGF
    (Context := Context) model armLaw hprob sigma2 hmean hsubG
  exact
    ETC.explorationArgmaxHistory_centeredReward_succ_hasCondSubgaussianMGF_trajMeasure
      spec model mu0 rewardKernel context hcontext
      (fun _ _ => sigma2) law i sigma2 (fun _history => le_rfl)

/--
Canonical ETC Azuma-Hoeffding bound for the full centered reward sum, including
the actual reward at time zero.

The initial trajectory law is fixed to the law of `ETC.exploreArm spec 0`.
`RewardKernel.trajMeasure_map_eval_zero` transfers its bounded centered MGF to
the zeroth trajectory coordinate, while the generated-history kernel law gives
the successor conditional MGF witnesses. Unlike the earlier zero-initialized
sum-tail surface, this sum contains rewards at every index in `Finset.range n`.
-/
theorem explorationArgmaxHistory_centeredRewardProcess_sum_tail_ennreal_of_boundedArmLaws
    {K : Nat} {Context : Type}
    [MeasurableSpace Context]
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (lo hi : Real)
    (hmeas : forall arm, AEMeasurable
      (fun reward : Rat => (((reward : Rat) : Real))) (armLaw arm))
    (hbound : forall arm, Filter.Eventually
      (fun reward : Rat => Set.Icc lo hi (((reward : Rat) : Real)))
      (ae (armLaw arm)))
    (hmean : forall arm, integral (armLaw arm)
      (fun reward : Rat => (((reward : Rat) : Real))) =
        (((model.mean arm : Rat) : Real)))
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (hcontext : forall n : Nat, Measurable (context n))
    (n : Nat) {eps : Real} (heps : 0 <= eps) :
    let defaultAction := ETC.exploreArm spec 0
    let rewardKernel := RewardKernel.contextIndependentOfActionLaws
      (Context := Context) armLaw hprob
    let policy := fun t => ETC.explorationArgmaxHistoryPolicy spec model t
    let state := fun t history => ETC.explorationArgmaxHistoryState t history
    let stepKernel :=
      RewardKernel.historyStepKernelFamily rewardKernel policy context state
        hcontext (fun t => ETC.measurable_explorationArgmaxHistoryState t)
    let trajMeasure := ProbabilityTheory.Kernel.trajMeasure
      (X := fun _ : Nat => Rat) (armLaw defaultAction) stepKernel
    let reward : RewardTrace Rat -> RewardTrace Rat := fun trajectory => trajectory
    let Y : Nat -> RewardTrace Rat -> Real := fun t trajectory =>
      match t with
      | 0 => (((reward trajectory 0 - model.mean defaultAction : Rat) : Real))
      | i + 1 =>
          (((reward trajectory (i + 1) -
            model.mean
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace
                    (reward trajectory) i))) : Rat) : Real))
    let cY : Nat -> NNReal := fun _ =>
      Concentration.intervalVarianceProxy lo hi
    trajMeasure
        {trajectory |
          eps <= (Finset.range n).sum (fun t => Y t trajectory)} <=
      ENNReal.ofReal
        (Real.exp
          (-eps ^ 2 /
            (2 * (((Finset.range n).sum cY : NNReal) : Real)))) := by
  let defaultAction := ETC.exploreArm spec 0
  let rewardKernel := RewardKernel.contextIndependentOfActionLaws
    (Context := Context) armLaw hprob
  let policy := fun t => ETC.explorationArgmaxHistoryPolicy spec model t
  let state := fun t history => ETC.explorationArgmaxHistoryState t history
  let stepKernel :=
    RewardKernel.historyStepKernelFamily rewardKernel policy context state
      hcontext (fun t => ETC.measurable_explorationArgmaxHistoryState t)
  letI : IsProbabilityMeasure (armLaw defaultAction) := hprob defaultAction
  let trajMeasure := ProbabilityTheory.Kernel.trajMeasure
    (X := fun _ : Nat => Rat) (armLaw defaultAction) stepKernel
  let reward : RewardTrace Rat -> RewardTrace Rat := fun trajectory => trajectory
  have hreward : forall t : Nat,
      Measurable (fun trajectory : RewardTrace Rat => reward trajectory t) :=
    fun t => measurable_pi_apply t
  let action :=
    ConditionalExpectationReward.generatedActionFromRewardHistory
      policy state defaultAction reward
  have haction : forall t : Nat,
      Measurable (fun trajectory : RewardTrace Rat => action trajectory t) :=
    ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
      (policy := policy) (state := state)
      (defaultAction := defaultAction) (reward := reward)
      hreward (fun t => ETC.measurable_explorationArgmaxHistoryState t)
  let F := History.historyFiltrationSucc action reward haction hreward
  let Y : Nat -> RewardTrace Rat -> Real := fun t trajectory =>
    match t with
    | 0 => (((reward trajectory 0 - model.mean defaultAction : Rat) : Real))
    | i + 1 =>
        (((reward trajectory (i + 1) -
          model.mean
            ((policy i).action
              (state i
                (History.finiteRewardHistoryOfTrace
                  (reward trajectory) i))) : Rat) : Real))
  let Ysucc : Nat -> RewardTrace Rat -> Real := fun t trajectory =>
    match t with
    | 0 => 0
    | i + 1 =>
        (((reward trajectory (i + 1) -
          model.mean
            ((policy i).action
              (state i
                (History.finiteRewardHistoryOfTrace
                  (reward trajectory) i))) : Rat) : Real))
  let cY : Nat -> NNReal := fun _ =>
    Concentration.intervalVarianceProxy lo hi
  have hadaptedSucc : StronglyAdapted F Ysucc := by
    simpa [F, action, Ysucc, policy, state] using
      (ConditionalExpectationReward.generatedActionFromRewardHistory_centeredRewardSuccProcess_stronglyAdapted
        (policy := policy)
        (context := context)
        (state := state)
        (hcontext := hcontext)
        (hstate := fun t => ETC.measurable_explorationArgmaxHistoryState t)
        (mean := fun _ arm => model.mean arm)
        (hmean := (measurable_of_countable model.mean).comp measurable_snd)
        (defaultAction := defaultAction)
        (reward := reward)
        (hreward := hreward))
  have hadapted : StronglyAdapted F Y := by
    intro t
    cases t with
    | zero =>
        have hreward0 :
            @Measurable (RewardTrace Rat) Rat (F 0) inferInstance
              (fun trajectory => reward trajectory 0) := by
          simpa [F, History.historyFiltrationSucc_apply] using
            (History.measurable_reward_mem_historyFiltration_of_lt
              (mOmega := inferInstance) action reward haction hreward
              (Nat.zero_lt_succ 0))
        have hreward0_real :
            @Measurable (RewardTrace Rat) Real (F 0) inferInstance
              (fun trajectory => ((reward trajectory 0 : Rat) : Real)) :=
          (measurable_of_countable
            (fun value : Rat => ((value : Rat) : Real))).comp hreward0
        have hcentered := hreward0_real.sub_const
          (((model.mean defaultAction : Rat) : Real))
        simpa [Y, Rat.cast_sub] using hcentered.stronglyMeasurable
    | succ i =>
        simpa [Y, Ysucc] using hadaptedSucc (i + 1)
  have harm0 : ProbabilityTheory.HasSubgaussianMGF
      (fun rewardValue : Rat =>
        ((rewardValue : Rat) : Real) -
          (((model.mean defaultAction : Rat) : Real)))
      (Concentration.intervalVarianceProxy lo hi)
      (armLaw defaultAction) :=
    Concentration.boundedCentered_hasSubgaussianMGF_of_mem_Icc_integral_eq
      (mu := armLaw defaultAction)
      (X := fun rewardValue : Rat => (((rewardValue : Rat) : Real)))
      (lo := lo) (hi := hi)
      (mean := (((model.mean defaultAction : Rat) : Real)))
      (hmeas defaultAction) (hbound defaultAction) (hmean defaultAction)
  have hzero : ProbabilityTheory.HasSubgaussianMGF
      (Y 0) (cY 0) trajMeasure := by
    have hcoord : ProbabilityTheory.HasSubgaussianMGF
        ((fun rewardValue : Rat =>
            ((rewardValue : Rat) : Real) -
              (((model.mean defaultAction : Rat) : Real))) ∘
          (fun trajectory : RewardTrace Rat => trajectory 0))
        (Concentration.intervalVarianceProxy lo hi) trajMeasure := by
      apply ProbabilityTheory.HasSubgaussianMGF.of_map
        (Y := fun trajectory : RewardTrace Rat => trajectory 0)
        (X := fun rewardValue : Rat =>
          ((rewardValue : Rat) : Real) -
            (((model.mean defaultAction : Rat) : Real)))
        (measurable_pi_apply 0).aemeasurable
      rw [RewardKernel.trajMeasure_map_eval_zero]
      exact harm0
    simpa [Y, cY, reward, Function.comp_apply, Rat.cast_sub] using hcoord
  have hcond : forall i, i < n - 1 ->
      ProbabilityTheory.HasCondSubgaussianMGF
        (F i) (F.le i) (Y (i + 1)) (cY (i + 1)) trajMeasure := by
    intro i _hi
    have hmgf :=
      ETC.explorationArgmaxHistory_centeredReward_succ_hasCondSubgaussianMGF_of_boundedArmLaws
        spec model (armLaw defaultAction) armLaw hprob lo hi
        hmeas hbound hmean context hcontext i
    simpa [rewardKernel, policy, state, stepKernel, trajMeasure, reward,
      action, F, Y, cY, defaultAction] using hmgf
  have htail :=
    Concentration.condSubGaussian_sum_tail_ennreal_of_stronglyAdapted
      (mu := trajMeasure) (Y := Y) (cY := cY) (F := F)
      hadapted hzero n hcond heps
  simpa [defaultAction, rewardKernel, policy, state, stepKernel, trajMeasure,
    reward, action, F, Y, cY] using htail

/--
Bounded finite-arm laws provide the reward-level conditional sub-Gaussian
witness package used by the existing fixed-commit pairwise ETC tail route.

The ambient measure is the canonical generated-history trajectory. During the
exploration horizon its generated action prefix agrees with
`actionWithCommit spec model.bestArm`; the corresponding shifted history
filtrations therefore agree. This transports the canonical selected-reward
conditional MGF to the fixed-commit witness interface without assuming
coordinate independence.
-/
noncomputable def explorationArgmaxHistory_centeredRewardCondSubGaussianWitnesses_of_boundedArmLaws
    {K : Nat} {Context : Type}
    [MeasurableSpace Context]
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (lo hi : Real)
    (hmeas : forall arm, AEMeasurable
      (fun reward : Rat => (((reward : Rat) : Real))) (armLaw arm))
    (hbound : forall arm, Filter.Eventually
      (fun reward : Rat => Set.Icc lo hi (((reward : Rat) : Real)))
      (ae (armLaw arm)))
    (hmean : forall arm, integral (armLaw arm)
      (fun reward : Rat => (((reward : Rat) : Real))) =
        (((model.mean arm : Rat) : Real)))
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (hcontext : forall n : Nat, Measurable (context n))
    (hexplorationPulls_pos : 0 < spec.explorationPulls) :
    let defaultAction := ETC.exploreArm spec 0
    let rewardKernel := RewardKernel.contextIndependentOfActionLaws
      (Context := Context) armLaw hprob
    let policy := fun t => ETC.explorationArgmaxHistoryPolicy spec model t
    let state := fun t history => ETC.explorationArgmaxHistoryState t history
    let stepKernel :=
      RewardKernel.historyStepKernelFamily rewardKernel policy context state
        hcontext (fun t => ETC.measurable_explorationArgmaxHistoryState t)
    let trajMeasure := ProbabilityTheory.Kernel.trajMeasure
      (X := fun _ : Nat => Rat) (armLaw defaultAction) stepKernel
    let reward : RewardTrace Rat -> RewardTrace Rat := fun trajectory => trajectory
    let cReward : Fin K -> Nat -> NNReal := fun _ _ =>
      Concentration.intervalVarianceProxy lo hi
    let pairwiseProxy := ETC.centeredPairwiseRewardDiffVarianceProxy
      spec model model.bestArm cReward
    ETC.CenteredRewardCondSubGaussianWitnesses
      trajMeasure spec model model.bestArm reward
      (ETC.centeredDiffSubGaussianTail spec model pairwiseProxy) := by
  let defaultAction := ETC.exploreArm spec 0
  let rewardKernel := RewardKernel.contextIndependentOfActionLaws
    (Context := Context) armLaw hprob
  let policy := fun t => ETC.explorationArgmaxHistoryPolicy spec model t
  let state := fun t history => ETC.explorationArgmaxHistoryState t history
  let stepKernel :=
    RewardKernel.historyStepKernelFamily rewardKernel policy context state
      hcontext (fun t => ETC.measurable_explorationArgmaxHistoryState t)
  letI : IsProbabilityMeasure (armLaw defaultAction) := hprob defaultAction
  let trajMeasure := ProbabilityTheory.Kernel.trajMeasure
    (X := fun _ : Nat => Rat) (armLaw defaultAction) stepKernel
  let reward : RewardTrace Rat -> RewardTrace Rat := fun trajectory => trajectory
  have hreward : forall t : Nat,
      Measurable (fun trajectory : RewardTrace Rat => reward trajectory t) :=
    fun t => measurable_pi_apply t
  let action := ConditionalExpectationReward.generatedActionFromRewardHistory
    policy state defaultAction reward
  have haction : forall t : Nat,
      Measurable (fun trajectory : RewardTrace Rat => action trajectory t) :=
    ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
      (policy := policy) (state := state)
      (defaultAction := defaultAction) (reward := reward)
      hreward (fun t => ETC.measurable_explorationArgmaxHistoryState t)
  let fixedAction : RewardTrace Rat -> ActionTrace (Fin K) :=
    fun _trajectory => ETC.actionWithCommit spec model.bestArm
  have hfixedAction : forall t : Nat,
      Measurable (fun trajectory : RewardTrace Rat => fixedAction trajectory t) :=
    fun _t => measurable_const
  let cReward : Fin K -> Nat -> NNReal := fun _ _ =>
    Concentration.intervalVarianceProxy lo hi
  let pairwiseProxy := ETC.centeredPairwiseRewardDiffVarianceProxy
    spec model model.bestArm cReward
  refine {
    cReward := cReward
    hreward := hreward
    subG0 := ?_
    condSubG := ?_
    tail_bound := ?_
  }
  · intro b hb
    have hzero_lt : 0 < spec.explorationPulls * K :=
      Nat.mul_pos hexplorationPulls_pos spec.hK
    have hb_default : defaultAction = b := by
      have hfixed0 :=
        ETC.actionWithCommit_eq_exploreArm_of_lt
          spec model.bestArm hzero_lt
      exact hfixed0.symm.trans hb
    have harm0 : ProbabilityTheory.HasSubgaussianMGF
        (fun rewardValue : Rat =>
          ((rewardValue : Rat) : Real) -
            (((model.mean defaultAction : Rat) : Real)))
        (Concentration.intervalVarianceProxy lo hi)
        (armLaw defaultAction) :=
      Concentration.boundedCentered_hasSubgaussianMGF_of_mem_Icc_integral_eq
        (mu := armLaw defaultAction)
        (X := fun rewardValue : Rat => (((rewardValue : Rat) : Real)))
        (lo := lo) (hi := hi)
        (mean := (((model.mean defaultAction : Rat) : Real)))
        (hmeas defaultAction) (hbound defaultAction) (hmean defaultAction)
    have hcoord : ProbabilityTheory.HasSubgaussianMGF
        ((fun rewardValue : Rat =>
            ((rewardValue : Rat) : Real) -
              (((model.mean defaultAction : Rat) : Real))) ∘
          (fun trajectory : RewardTrace Rat => trajectory 0))
        (Concentration.intervalVarianceProxy lo hi) trajMeasure := by
      apply ProbabilityTheory.HasSubgaussianMGF.of_map
        (Y := fun trajectory : RewardTrace Rat => trajectory 0)
        (X := fun rewardValue : Rat =>
          ((rewardValue : Rat) : Real) -
            (((model.mean defaultAction : Rat) : Real)))
        (measurable_pi_apply 0).aemeasurable
      rw [RewardKernel.trajMeasure_map_eval_zero]
      exact harm0
    simpa [reward, cReward, hb_default, Function.comp_apply, Rat.cast_sub]
      using hcoord
  · intro i hi_idx b hb
    have ht : i + 1 < spec.explorationPulls * K := by omega
    have hb_explore : ETC.exploreArm spec (i + 1) = b := by
      simpa only [ETC.actionWithCommit_eq_exploreArm_of_lt
        spec model.bestArm ht] using hb
    have hfiltration :
        (History.historyFiltrationSucc action reward haction hreward i :
            MeasurableSpace (RewardTrace Rat)) =
          (History.historyFiltrationSucc fixedAction reward
            hfixedAction hreward i : MeasurableSpace (RewardTrace Rat)) := by
      apply History.historyFiltrationSucc_eq_of_action_eq_on_prefix
      intro trajectory t ht_le
      have ht_horizon : t < spec.explorationPulls * K := by omega
      simpa [action, fixedAction, policy, state, defaultAction, reward,
        ETC.explorationArgmaxGeneratedAction] using
        (ETC.explorationArgmaxGeneratedAction_eq_actionWithCommit_of_lt
          spec model model.bestArm trajectory hexplorationPulls_pos ht_horizon)
    have hmgf :=
      ETC.explorationArgmaxHistory_centeredReward_succ_hasCondSubgaussianMGF_of_boundedArmLaws
        spec model (armLaw defaultAction) armLaw hprob lo hi
        hmeas hbound hmean context hcontext i
    have hmgf' : ProbabilityTheory.HasCondSubgaussianMGF
        (History.historyFiltrationSucc action reward haction hreward i)
        ((History.historyFiltrationSucc action reward haction hreward).le i)
        (fun trajectory : RewardTrace Rat =>
          (((reward trajectory (i + 1) -
            model.mean
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace
                    (reward trajectory) i))) : Rat) : Real)))
        (Concentration.intervalVarianceProxy lo hi) trajMeasure := by
      simpa [rewardKernel, policy, state, stepKernel, trajMeasure, reward,
        action, defaultAction] using hmgf
    have hmgfFixed :=
      ProbabilityTheory.HasCondSubgaussianMGF.of_measurableSpace_eq
        (mu := trajMeasure)
        (m0 := History.historyFiltrationSucc action reward haction hreward i)
        (m1 := History.historyFiltrationSucc fixedAction reward
          hfixedAction hreward i)
        ((History.historyFiltrationSucc action reward haction hreward).le i)
        ((History.historyFiltrationSucc fixedAction reward
          hfixedAction hreward).le i)
        hfiltration hmgf'
    simpa [fixedAction, cReward, policy,
      ETC.explorationArgmaxHistoryPolicy, ht, hb_explore] using hmgfFixed
  · intro a _hne
    simp [ETC.centeredDiffSubGaussianTail, cReward]

/--
Direct common-sub-Gaussian arm laws provide the reward-level conditional
witness package used by the fixed-commit pairwise ETC tail route.

The initial witness is transported from the initial arm law. Successor
witnesses come from the generated-history kernel law and are moved to the
fixed `actionWithCommit` filtration using exploration-prefix action equality.
No bounded-support assumption or arm union is used.
-/
noncomputable def explorationArgmaxHistory_centeredRewardCondSubGaussianWitnesses_of_armLaws
    {K : Nat} {Context : Type}
    [MeasurableSpace Context]
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (sigma2 : NNReal)
    (hmean : forall arm, integral (armLaw arm)
      (fun reward : Rat => (((reward : Rat) : Real))) =
        (((model.mean arm : Rat) : Real)))
    (hsubG : forall arm, ProbabilityTheory.HasSubgaussianMGF
      (fun reward : Rat =>
        ((reward : Rat) : Real) - (((model.mean arm : Rat) : Real)))
      sigma2 (armLaw arm))
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (hcontext : forall n : Nat, Measurable (context n))
    (hexplorationPulls_pos : 0 < spec.explorationPulls) :
    let defaultAction := ETC.exploreArm spec 0
    let rewardKernel := RewardKernel.contextIndependentOfActionLaws
      (Context := Context) armLaw hprob
    let policy := fun t => ETC.explorationArgmaxHistoryPolicy spec model t
    let state := fun t history => ETC.explorationArgmaxHistoryState t history
    let stepKernel :=
      RewardKernel.historyStepKernelFamily rewardKernel policy context state
        hcontext (fun t => ETC.measurable_explorationArgmaxHistoryState t)
    let trajMeasure := ProbabilityTheory.Kernel.trajMeasure
      (X := fun _ : Nat => Rat) (armLaw defaultAction) stepKernel
    let reward : RewardTrace Rat -> RewardTrace Rat := fun trajectory => trajectory
    let cReward : Fin K -> Nat -> NNReal := fun _ _ => sigma2
    let pairwiseProxy := ETC.centeredPairwiseRewardDiffVarianceProxy
      spec model model.bestArm cReward
    ETC.CenteredRewardCondSubGaussianWitnesses
      trajMeasure spec model model.bestArm reward
      (ETC.centeredDiffSubGaussianTail spec model pairwiseProxy) := by
  let defaultAction := ETC.exploreArm spec 0
  let rewardKernel := RewardKernel.contextIndependentOfActionLaws
    (Context := Context) armLaw hprob
  let policy := fun t => ETC.explorationArgmaxHistoryPolicy spec model t
  let state := fun t history => ETC.explorationArgmaxHistoryState t history
  let stepKernel :=
    RewardKernel.historyStepKernelFamily rewardKernel policy context state
      hcontext (fun t => ETC.measurable_explorationArgmaxHistoryState t)
  letI : IsProbabilityMeasure (armLaw defaultAction) := hprob defaultAction
  let trajMeasure := ProbabilityTheory.Kernel.trajMeasure
    (X := fun _ : Nat => Rat) (armLaw defaultAction) stepKernel
  let reward : RewardTrace Rat -> RewardTrace Rat := fun trajectory => trajectory
  have hreward : forall t : Nat,
      Measurable (fun trajectory : RewardTrace Rat => reward trajectory t) :=
    fun t => measurable_pi_apply t
  let action := ConditionalExpectationReward.generatedActionFromRewardHistory
    policy state defaultAction reward
  have haction : forall t : Nat,
      Measurable (fun trajectory : RewardTrace Rat => action trajectory t) :=
    ConditionalExpectationReward.generatedActionFromRewardHistory_measurable
      (policy := policy) (state := state)
      (defaultAction := defaultAction) (reward := reward)
      hreward (fun t => ETC.measurable_explorationArgmaxHistoryState t)
  let fixedAction : RewardTrace Rat -> ActionTrace (Fin K) :=
    fun _trajectory => ETC.actionWithCommit spec model.bestArm
  have hfixedAction : forall t : Nat,
      Measurable (fun trajectory : RewardTrace Rat => fixedAction trajectory t) :=
    fun _t => measurable_const
  let cReward : Fin K -> Nat -> NNReal := fun _ _ => sigma2
  let pairwiseProxy := ETC.centeredPairwiseRewardDiffVarianceProxy
    spec model model.bestArm cReward
  refine {
    cReward := cReward
    hreward := hreward
    subG0 := ?_
    condSubG := ?_
    tail_bound := ?_
  }
  · intro b hb
    have hzero_lt : 0 < spec.explorationPulls * K :=
      Nat.mul_pos hexplorationPulls_pos spec.hK
    have hb_default : defaultAction = b := by
      have hfixed0 :=
        ETC.actionWithCommit_eq_exploreArm_of_lt
          spec model.bestArm hzero_lt
      exact hfixed0.symm.trans hb
    have hcoord : ProbabilityTheory.HasSubgaussianMGF
        ((fun rewardValue : Rat =>
            ((rewardValue : Rat) : Real) -
              (((model.mean defaultAction : Rat) : Real))) ∘
          (fun trajectory : RewardTrace Rat => trajectory 0))
        sigma2 trajMeasure := by
      apply ProbabilityTheory.HasSubgaussianMGF.of_map
        (Y := fun trajectory : RewardTrace Rat => trajectory 0)
        (X := fun rewardValue : Rat =>
          ((rewardValue : Rat) : Real) -
            (((model.mean defaultAction : Rat) : Real)))
        (measurable_pi_apply 0).aemeasurable
      rw [RewardKernel.trajMeasure_map_eval_zero]
      exact hsubG defaultAction
    simpa [reward, cReward, hb_default, Function.comp_apply, Rat.cast_sub]
      using hcoord
  · intro i hi_idx b hb
    have ht : i + 1 < spec.explorationPulls * K := by omega
    have hb_explore : ETC.exploreArm spec (i + 1) = b := by
      simpa only [ETC.actionWithCommit_eq_exploreArm_of_lt
        spec model.bestArm ht] using hb
    have hfiltration :
        (History.historyFiltrationSucc action reward haction hreward i :
            MeasurableSpace (RewardTrace Rat)) =
          (History.historyFiltrationSucc fixedAction reward
            hfixedAction hreward i : MeasurableSpace (RewardTrace Rat)) := by
      apply History.historyFiltrationSucc_eq_of_action_eq_on_prefix
      intro trajectory t ht_le
      have ht_horizon : t < spec.explorationPulls * K := by omega
      simpa [action, fixedAction, policy, state, defaultAction, reward,
        ETC.explorationArgmaxGeneratedAction] using
        (ETC.explorationArgmaxGeneratedAction_eq_actionWithCommit_of_lt
          spec model model.bestArm trajectory hexplorationPulls_pos ht_horizon)
    have hmgf :=
      ETC.explorationArgmaxHistory_centeredReward_succ_hasCondSubgaussianMGF_of_armLaws
        spec model (armLaw defaultAction) armLaw hprob sigma2
        hmean hsubG context hcontext i
    have hmgf' : ProbabilityTheory.HasCondSubgaussianMGF
        (History.historyFiltrationSucc action reward haction hreward i)
        ((History.historyFiltrationSucc action reward haction hreward).le i)
        (fun trajectory : RewardTrace Rat =>
          (((reward trajectory (i + 1) -
            model.mean
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace
                    (reward trajectory) i))) : Rat) : Real)))
        sigma2 trajMeasure := by
      simpa [rewardKernel, policy, state, stepKernel, trajMeasure, reward,
        action, defaultAction] using hmgf
    have hmgfFixed :=
      ProbabilityTheory.HasCondSubgaussianMGF.of_measurableSpace_eq
        (mu := trajMeasure)
        (m0 := History.historyFiltrationSucc action reward haction hreward i)
        (m1 := History.historyFiltrationSucc fixedAction reward
          hfixedAction hreward i)
        ((History.historyFiltrationSucc action reward haction hreward).le i)
        ((History.historyFiltrationSucc fixedAction reward
          hfixedAction hreward).le i)
        hfiltration hmgf'
    simpa [fixedAction, cReward, policy,
      ETC.explorationArgmaxHistoryPolicy, ht, hb_explore] using hmgfFixed
  · intro a _hne
    simp [ETC.centeredDiffSubGaussianTail, cReward]

/--
Canonical pairwise empirical-mean tail contract for the generated-history ETC
trajectory under bounded finite-arm reward laws.

This consumes the reward-level witness above through the existing centered
pairwise conditional sub-Gaussian adapter. The contract matches the exact
empirical means used by `explorationArgmaxCommit`.
-/
theorem explorationArgmaxHistory_pairwiseEmpMeanTailContract_of_boundedArmLaws
    {K : Nat} {Context : Type}
    [MeasurableSpace Context]
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (lo hi : Real)
    (hmeas : forall arm, AEMeasurable
      (fun reward : Rat => (((reward : Rat) : Real))) (armLaw arm))
    (hbound : forall arm, Filter.Eventually
      (fun reward : Rat => Set.Icc lo hi (((reward : Rat) : Real)))
      (ae (armLaw arm)))
    (hmean : forall arm, integral (armLaw arm)
      (fun reward : Rat => (((reward : Rat) : Real))) =
        (((model.mean arm : Rat) : Real)))
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (hcontext : forall n : Nat, Measurable (context n))
    (hexplorationPulls_pos : 0 < spec.explorationPulls) :
    let defaultAction := ETC.exploreArm spec 0
    let rewardKernel := RewardKernel.contextIndependentOfActionLaws
      (Context := Context) armLaw hprob
    let policy := fun t => ETC.explorationArgmaxHistoryPolicy spec model t
    let state := fun t history => ETC.explorationArgmaxHistoryState t history
    let stepKernel :=
      RewardKernel.historyStepKernelFamily rewardKernel policy context state
        hcontext (fun t => ETC.measurable_explorationArgmaxHistoryState t)
    let trajMeasure := ProbabilityTheory.Kernel.trajMeasure
      (X := fun _ : Nat => Rat) (armLaw defaultAction) stepKernel
    let reward : RewardTrace Rat -> RewardTrace Rat := fun trajectory => trajectory
    let cReward : Fin K -> Nat -> NNReal := fun _ _ =>
      Concentration.intervalVarianceProxy lo hi
    let pairwiseProxy := ETC.centeredPairwiseRewardDiffVarianceProxy
      spec model model.bestArm cReward
    ETC.PairwiseEmpMeanTailContract
      trajMeasure spec model model.bestArm reward
      (ETC.centeredDiffSubGaussianTail spec model pairwiseProxy) := by
  let defaultAction := ETC.exploreArm spec 0
  let rewardKernel := RewardKernel.contextIndependentOfActionLaws
    (Context := Context) armLaw hprob
  let policy := fun t => ETC.explorationArgmaxHistoryPolicy spec model t
  let state := fun t history => ETC.explorationArgmaxHistoryState t history
  let stepKernel :=
    RewardKernel.historyStepKernelFamily rewardKernel policy context state
      hcontext (fun t => ETC.measurable_explorationArgmaxHistoryState t)
  letI : IsProbabilityMeasure (armLaw defaultAction) := hprob defaultAction
  let trajMeasure := ProbabilityTheory.Kernel.trajMeasure
    (X := fun _ : Nat => Rat) (armLaw defaultAction) stepKernel
  let reward : RewardTrace Rat -> RewardTrace Rat := fun trajectory => trajectory
  let cReward : Fin K -> Nat -> NNReal := fun _ _ =>
    Concentration.intervalVarianceProxy lo hi
  let pairwiseProxy := ETC.centeredPairwiseRewardDiffVarianceProxy
    spec model model.bestArm cReward
  exact
    ETC.pairwiseEmpMeanTailContract_of_centeredDiffCondSubGaussianWitnesses
      trajMeasure spec model model.bestArm reward
      (ETC.centeredDiffSubGaussianTail spec model pairwiseProxy)
      hexplorationPulls_pos
      (ETC.centeredDiffCondSubGaussianWitnesses_of_centeredRewardCondSubGaussianWitnesses
        trajMeasure spec model model.bestArm reward
        (ETC.centeredDiffSubGaussianTail spec model pairwiseProxy)
        (ETC.explorationArgmaxHistory_centeredRewardCondSubGaussianWitnesses_of_boundedArmLaws
          spec model armLaw hprob lo hi hmeas hbound hmean
          context hcontext hexplorationPulls_pos))

/--
Canonical pairwise empirical-mean tail contract for generated-history ETC
under direct common-sub-Gaussian finite-arm laws.

This is the concentration endpoint of the direct-MGF leaf. It retains the
exact empirical means and fixed-commit one-sided pairwise process used by the
bounded route, but replaces common support by the caller's shared `sigma2`.
-/
theorem explorationArgmaxHistory_pairwiseEmpMeanTailContract_of_armLaws
    {K : Nat} {Context : Type}
    [MeasurableSpace Context]
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (sigma2 : NNReal)
    (hmean : forall arm, integral (armLaw arm)
      (fun reward : Rat => (((reward : Rat) : Real))) =
        (((model.mean arm : Rat) : Real)))
    (hsubG : forall arm, ProbabilityTheory.HasSubgaussianMGF
      (fun reward : Rat =>
        ((reward : Rat) : Real) - (((model.mean arm : Rat) : Real)))
      sigma2 (armLaw arm))
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (hcontext : forall n : Nat, Measurable (context n))
    (hexplorationPulls_pos : 0 < spec.explorationPulls) :
    let defaultAction := ETC.exploreArm spec 0
    let rewardKernel := RewardKernel.contextIndependentOfActionLaws
      (Context := Context) armLaw hprob
    let policy := fun t => ETC.explorationArgmaxHistoryPolicy spec model t
    let state := fun t history => ETC.explorationArgmaxHistoryState t history
    let stepKernel :=
      RewardKernel.historyStepKernelFamily rewardKernel policy context state
        hcontext (fun t => ETC.measurable_explorationArgmaxHistoryState t)
    let trajMeasure := ProbabilityTheory.Kernel.trajMeasure
      (X := fun _ : Nat => Rat) (armLaw defaultAction) stepKernel
    let reward : RewardTrace Rat -> RewardTrace Rat := fun trajectory => trajectory
    let cReward : Fin K -> Nat -> NNReal := fun _ _ => sigma2
    let pairwiseProxy := ETC.centeredPairwiseRewardDiffVarianceProxy
      spec model model.bestArm cReward
    ETC.PairwiseEmpMeanTailContract
      trajMeasure spec model model.bestArm reward
      (ETC.centeredDiffSubGaussianTail spec model pairwiseProxy) := by
  let defaultAction := ETC.exploreArm spec 0
  let rewardKernel := RewardKernel.contextIndependentOfActionLaws
    (Context := Context) armLaw hprob
  let policy := fun t => ETC.explorationArgmaxHistoryPolicy spec model t
  let state := fun t history => ETC.explorationArgmaxHistoryState t history
  let stepKernel :=
    RewardKernel.historyStepKernelFamily rewardKernel policy context state
      hcontext (fun t => ETC.measurable_explorationArgmaxHistoryState t)
  letI : IsProbabilityMeasure (armLaw defaultAction) := hprob defaultAction
  let trajMeasure := ProbabilityTheory.Kernel.trajMeasure
    (X := fun _ : Nat => Rat) (armLaw defaultAction) stepKernel
  let reward : RewardTrace Rat -> RewardTrace Rat := fun trajectory => trajectory
  let cReward : Fin K -> Nat -> NNReal := fun _ _ => sigma2
  let pairwiseProxy := ETC.centeredPairwiseRewardDiffVarianceProxy
    spec model model.bestArm cReward
  exact
    ETC.pairwiseEmpMeanTailContract_of_centeredDiffCondSubGaussianWitnesses
      trajMeasure spec model model.bestArm reward
      (ETC.centeredDiffSubGaussianTail spec model pairwiseProxy)
      hexplorationPulls_pos
      (ETC.centeredDiffCondSubGaussianWitnesses_of_centeredRewardCondSubGaussianWitnesses
        trajMeasure spec model model.bestArm reward
        (ETC.centeredDiffSubGaussianTail spec model pairwiseProxy)
        (ETC.explorationArgmaxHistory_centeredRewardCondSubGaussianWitnesses_of_armLaws
          spec model armLaw hprob sigma2 hmean hsubG
          context hcontext hexplorationPulls_pos))

/--
Canonical generated-history ETC probability bound for committing to one fixed
non-best arm under direct common-sub-Gaussian finite-arm laws.

The theorem consumes the direct-MGF pairwise empirical-mean contract. It keeps
the single concrete commit fiber and therefore introduces no arm union.
-/
theorem explorationArgmaxHistory_prob_commit_eq_arm_le_pairwiseTail_of_armLaws
    {K : Nat} {Context : Type}
    [MeasurableSpace Context]
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (sigma2 : NNReal)
    (hmean : forall arm, integral (armLaw arm)
      (fun reward : Rat => (((reward : Rat) : Real))) =
        (((model.mean arm : Rat) : Real)))
    (hsubG : forall arm, ProbabilityTheory.HasSubgaussianMGF
      (fun reward : Rat =>
        ((reward : Rat) : Real) - (((model.mean arm : Rat) : Real)))
      sigma2 (armLaw arm))
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (hcontext : forall n : Nat, Measurable (context n))
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    (a : Fin K)
    (hne : a = model.bestArm -> False) :
    let defaultAction := ETC.exploreArm spec 0
    let rewardKernel := RewardKernel.contextIndependentOfActionLaws
      (Context := Context) armLaw hprob
    let policy := fun t => ETC.explorationArgmaxHistoryPolicy spec model t
    let state := fun t history => ETC.explorationArgmaxHistoryState t history
    let stepKernel :=
      RewardKernel.historyStepKernelFamily rewardKernel policy context state
        hcontext (fun t => ETC.measurable_explorationArgmaxHistoryState t)
    let trajMeasure := ProbabilityTheory.Kernel.trajMeasure
      (X := fun _ : Nat => Rat) (armLaw defaultAction) stepKernel
    let cReward : Fin K -> Nat -> NNReal := fun _ _ => sigma2
    let pairwiseProxy := ETC.centeredPairwiseRewardDiffVarianceProxy
      spec model model.bestArm cReward
    trajMeasure
        {trajectory : RewardTrace Rat |
          ETC.explorationArgmaxCommit spec model trajectory = a} <=
      ETC.centeredDiffSubGaussianTail spec model pairwiseProxy a := by
  let defaultAction := ETC.exploreArm spec 0
  let rewardKernel := RewardKernel.contextIndependentOfActionLaws
    (Context := Context) armLaw hprob
  let policy := fun t => ETC.explorationArgmaxHistoryPolicy spec model t
  let state := fun t history => ETC.explorationArgmaxHistoryState t history
  let stepKernel :=
    RewardKernel.historyStepKernelFamily rewardKernel policy context state
      hcontext (fun t => ETC.measurable_explorationArgmaxHistoryState t)
  letI : IsProbabilityMeasure (armLaw defaultAction) := hprob defaultAction
  let trajMeasure := ProbabilityTheory.Kernel.trajMeasure
    (X := fun _ : Nat => Rat) (armLaw defaultAction) stepKernel
  let reward : RewardTrace Rat -> RewardTrace Rat := fun trajectory => trajectory
  let cReward : Fin K -> Nat -> NNReal := fun _ _ => sigma2
  let pairwiseProxy := ETC.centeredPairwiseRewardDiffVarianceProxy
    spec model model.bestArm cReward
  have hcontract :=
    ETC.explorationArgmaxHistory_pairwiseEmpMeanTailContract_of_armLaws
      spec model armLaw hprob sigma2 hmean hsubG
      context hcontext hexplorationPulls_pos
  have hprobability :=
    ETC.prob_argmaxCommitOracle_eq_arm_le_pairwise_tail_of_contract
      model.hK trajMeasure spec model model.bestArm reward
      (ETC.centeredDiffSubGaussianTail spec model pairwiseProxy)
      hcontract a hne
  simpa [ETC.explorationArgmaxCommit, ETC.fixedProductArgmaxCommit,
    reward, pairwiseProxy, cReward, trajMeasure, stepKernel,
    policy, state, rewardKernel, defaultAction] using hprobability

/--
Canonical generated-history ETC probability bound for committing to one fixed
non-best arm under bounded finite-arm reward laws.

The event is the actual concrete empirical-mean argmax fiber. Its probability
is bounded by the matching one-sided centered pairwise tail, with no union over
the other arms. This is the armwise probability source required by the
gap-weighted Bochner assembly.
-/
theorem explorationArgmaxHistory_prob_commit_eq_arm_le_pairwiseTail_of_boundedArmLaws
    {K : Nat} {Context : Type}
    [MeasurableSpace Context]
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (lo hi : Real)
    (hmeas : forall arm, AEMeasurable
      (fun reward : Rat => (((reward : Rat) : Real))) (armLaw arm))
    (hbound : forall arm, Filter.Eventually
      (fun reward : Rat => Set.Icc lo hi (((reward : Rat) : Real)))
      (ae (armLaw arm)))
    (hmean : forall arm, integral (armLaw arm)
      (fun reward : Rat => (((reward : Rat) : Real))) =
        (((model.mean arm : Rat) : Real)))
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (hcontext : forall n : Nat, Measurable (context n))
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    (a : Fin K)
    (hne : a = model.bestArm -> False) :
    let defaultAction := ETC.exploreArm spec 0
    let rewardKernel := RewardKernel.contextIndependentOfActionLaws
      (Context := Context) armLaw hprob
    let policy := fun t => ETC.explorationArgmaxHistoryPolicy spec model t
    let state := fun t history => ETC.explorationArgmaxHistoryState t history
    let stepKernel :=
      RewardKernel.historyStepKernelFamily rewardKernel policy context state
        hcontext (fun t => ETC.measurable_explorationArgmaxHistoryState t)
    let trajMeasure := ProbabilityTheory.Kernel.trajMeasure
      (X := fun _ : Nat => Rat) (armLaw defaultAction) stepKernel
    let cReward : Fin K -> Nat -> NNReal := fun _ _ =>
      Concentration.intervalVarianceProxy lo hi
    let pairwiseProxy := ETC.centeredPairwiseRewardDiffVarianceProxy
      spec model model.bestArm cReward
    trajMeasure
        {trajectory : RewardTrace Rat |
          ETC.explorationArgmaxCommit spec model trajectory = a} <=
      ETC.centeredDiffSubGaussianTail spec model pairwiseProxy a := by
  let defaultAction := ETC.exploreArm spec 0
  let rewardKernel := RewardKernel.contextIndependentOfActionLaws
    (Context := Context) armLaw hprob
  let policy := fun t => ETC.explorationArgmaxHistoryPolicy spec model t
  let state := fun t history => ETC.explorationArgmaxHistoryState t history
  let stepKernel :=
    RewardKernel.historyStepKernelFamily rewardKernel policy context state
      hcontext (fun t => ETC.measurable_explorationArgmaxHistoryState t)
  letI : IsProbabilityMeasure (armLaw defaultAction) := hprob defaultAction
  let trajMeasure := ProbabilityTheory.Kernel.trajMeasure
    (X := fun _ : Nat => Rat) (armLaw defaultAction) stepKernel
  let reward : RewardTrace Rat -> RewardTrace Rat := fun trajectory => trajectory
  let cReward : Fin K -> Nat -> NNReal := fun _ _ =>
    Concentration.intervalVarianceProxy lo hi
  let pairwiseProxy := ETC.centeredPairwiseRewardDiffVarianceProxy
    spec model model.bestArm cReward
  have hcontract :=
    ETC.explorationArgmaxHistory_pairwiseEmpMeanTailContract_of_boundedArmLaws
      spec model armLaw hprob lo hi hmeas hbound hmean
      context hcontext hexplorationPulls_pos
  have hprobability :=
    ETC.prob_argmaxCommitOracle_eq_arm_le_pairwise_tail_of_contract
      model.hK trajMeasure spec model model.bestArm reward
      (ETC.centeredDiffSubGaussianTail spec model pairwiseProxy)
      hcontract a hne
  simpa [ETC.explorationArgmaxCommit, ETC.fixedProductArgmaxCommit,
    reward, pairwiseProxy, cReward, trajMeasure, stepKernel,
    policy, state, rewardKernel, defaultAction] using hprobability

/--
Canonical generated-history ETC wrong-commit probability bound from bounded
finite-arm laws.

The event is the actual empirical-mean argmax commit used by the generated ETC
policy. Its probability is bounded by the finite union of the canonical
centered pairwise sub-Gaussian tails. This is a one-horizon, one-sided,
union-bounded result; it does not yet assemble expected regret or transport to
an externally supplied environment law.
-/
theorem explorationArgmaxHistory_prob_wrongCommit_le_pairwiseTailSum_of_boundedArmLaws
    {K : Nat} {Context : Type}
    [MeasurableSpace Context]
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (lo hi : Real)
    (hmeas : forall arm, AEMeasurable
      (fun reward : Rat => (((reward : Rat) : Real))) (armLaw arm))
    (hbound : forall arm, Filter.Eventually
      (fun reward : Rat => Set.Icc lo hi (((reward : Rat) : Real)))
      (ae (armLaw arm)))
    (hmean : forall arm, integral (armLaw arm)
      (fun reward : Rat => (((reward : Rat) : Real))) =
        (((model.mean arm : Rat) : Real)))
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (hcontext : forall n : Nat, Measurable (context n))
    (hexplorationPulls_pos : 0 < spec.explorationPulls) :
    let defaultAction := ETC.exploreArm spec 0
    let rewardKernel := RewardKernel.contextIndependentOfActionLaws
      (Context := Context) armLaw hprob
    let policy := fun t => ETC.explorationArgmaxHistoryPolicy spec model t
    let state := fun t history => ETC.explorationArgmaxHistoryState t history
    let stepKernel :=
      RewardKernel.historyStepKernelFamily rewardKernel policy context state
        hcontext (fun t => ETC.measurable_explorationArgmaxHistoryState t)
    let trajMeasure := ProbabilityTheory.Kernel.trajMeasure
      (X := fun _ : Nat => Rat) (armLaw defaultAction) stepKernel
    let cReward : Fin K -> Nat -> NNReal := fun _ _ =>
      Concentration.intervalVarianceProxy lo hi
    let pairwiseProxy := ETC.centeredPairwiseRewardDiffVarianceProxy
      spec model model.bestArm cReward
    trajMeasure
        {trajectory : RewardTrace Rat |
          ETC.explorationArgmaxCommit spec model trajectory = model.bestArm -> False} <=
      ((Finset.univ : Finset (Fin K)).filter
        (fun a : Fin K => a = model.bestArm -> False)).sum
        (ETC.centeredDiffSubGaussianTail spec model pairwiseProxy) := by
  let defaultAction := ETC.exploreArm spec 0
  let rewardKernel := RewardKernel.contextIndependentOfActionLaws
    (Context := Context) armLaw hprob
  let policy := fun t => ETC.explorationArgmaxHistoryPolicy spec model t
  let state := fun t history => ETC.explorationArgmaxHistoryState t history
  let stepKernel :=
    RewardKernel.historyStepKernelFamily rewardKernel policy context state
      hcontext (fun t => ETC.measurable_explorationArgmaxHistoryState t)
  letI : IsProbabilityMeasure (armLaw defaultAction) := hprob defaultAction
  let trajMeasure := ProbabilityTheory.Kernel.trajMeasure
    (X := fun _ : Nat => Rat) (armLaw defaultAction) stepKernel
  let reward : RewardTrace Rat -> RewardTrace Rat := fun trajectory => trajectory
  let cReward : Fin K -> Nat -> NNReal := fun _ _ =>
    Concentration.intervalVarianceProxy lo hi
  let pairwiseProxy := ETC.centeredPairwiseRewardDiffVarianceProxy
    spec model model.bestArm cReward
  have hcontract :=
    ETC.explorationArgmaxHistory_pairwiseEmpMeanTailContract_of_boundedArmLaws
      spec model armLaw hprob lo hi hmeas hbound hmean
      context hcontext hexplorationPulls_pos
  have hprobability :=
    ETC.prob_argmaxCommitOracle_ne_bestArm_le_filtered_sum_pairwise_tail_of_contract
      model.hK trajMeasure spec model model.bestArm reward
      (ETC.centeredDiffSubGaussianTail spec model pairwiseProxy) hcontract
  simpa [ETC.explorationArgmaxCommit, ETC.fixedProductArgmaxCommit,
    reward, pairwiseProxy, cReward, trajMeasure, stepKernel,
    policy, state, rewardKernel, defaultAction] using hprobability

/--
Canonical finite-union wrong-commit tail budget for common-bounded arm laws.

Every reward-level variance proxy is the common interval proxy. The pairwise
mask retains that proxy only when the exploration trace samples the candidate
arm or the selected best arm.
-/
noncomputable def canonicalBoundedArmWrongCommitTailBudget
    {K : Nat} (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (lo hi : Real) : ENNReal :=
  let cReward : Fin K -> Nat -> NNReal := fun _ _ =>
    Concentration.intervalVarianceProxy lo hi
  let pairwiseProxy := ETC.centeredPairwiseRewardDiffVarianceProxy
    spec model model.bestArm cReward
  ((Finset.univ : Finset (Fin K)).filter
    (fun a : Fin K => a = model.bestArm -> False)).sum
    (ETC.centeredDiffSubGaussianTail spec model pairwiseProxy)

/-- Real view of the canonical bounded-arm wrong-commit tail budget. -/
noncomputable def canonicalBoundedArmWrongCommitTailBudgetReal
    {K : Nat} (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (lo hi : Real) : Real :=
  (ETC.canonicalBoundedArmWrongCommitTailBudget spec model lo hi).toReal

/--
Named Real regret budget for canonical bounded-arm generated ETC.

The first term pays the round-robin exploration cost. The second charges the
remaining `r` rounds by `model.maxGap` times the canonical wrong-commit budget.
-/
noncomputable def canonicalBoundedArmMaxGapIntegralRegretBoundReal
    {K : Nat} (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (r : Nat) (lo hi : Real) : Real :=
  let base : Real :=
    (((((Finset.univ : Finset (Fin K)).sum
      (fun a : Fin K => model.gap a)) *
      (((spec.explorationPulls : Nat) : Rat)) : Rat) : Real))
  let suffix : Real :=
    (((((r : Nat) : Rat) * model.maxGap : Rat) : Real))
  base + suffix *
    ETC.canonicalBoundedArmWrongCommitTailBudgetReal spec model lo hi

/-- Real view of one canonical bounded-arm centered pairwise tail. -/
noncomputable def canonicalBoundedArmPairwiseTailReal
    {K : Nat} (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (lo hi : Real) (a : Fin K) : Real :=
  let cReward : Fin K -> Nat -> NNReal := fun _ _ =>
    Concentration.intervalVarianceProxy lo hi
  let pairwiseProxy := ETC.centeredPairwiseRewardDiffVarianceProxy
    spec model model.bestArm cReward
  (ETC.centeredDiffSubGaussianTail spec model pairwiseProxy a).toReal

/--
Named Real regret budget for the canonical bounded-arm per-arm ETC route.

The exploration term is unchanged. The suffix keeps every arm gap paired with
that arm's own canonical pairwise tail instead of collapsing the finite family
to `model.maxGap` times a union probability.
-/
noncomputable def canonicalBoundedArmPerArmIntegralRegretBoundReal
    {K : Nat} (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (r : Nat) (lo hi : Real) : Real :=
  let base : Real :=
    (((((Finset.univ : Finset (Fin K)).sum
      (fun a : Fin K => model.gap a)) *
      (((spec.explorationPulls : Nat) : Rat)) : Rat) : Real))
  base + (Finset.univ : Finset (Fin K)).sum
    (fun a : Fin K =>
      ((((((r : Nat) : Rat) * model.gap a : Rat) : Real))) *
        ETC.canonicalBoundedArmPairwiseTailReal spec model lo hi a)

/-- Real view of one canonical common-sub-Gaussian arm pairwise tail. -/
noncomputable def canonicalSubGaussianArmPairwiseTailReal
    {K : Nat} (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (sigma2 : NNReal) (a : Fin K) : Real :=
  let cReward : Fin K -> Nat -> NNReal := fun _ _ => sigma2
  let pairwiseProxy := ETC.centeredPairwiseRewardDiffVarianceProxy
    spec model model.bestArm cReward
  (ETC.centeredDiffSubGaussianTail spec model pairwiseProxy a).toReal

/--
Named Real regret budget for the canonical common-sub-Gaussian per-arm ETC
route over `Rat` rewards.

The suffix preserves one gap-weighted direct-MGF pairwise tail per arm and
takes no finite-arm union.
-/
noncomputable def canonicalSubGaussianArmPerArmIntegralRegretBoundReal
    {K : Nat} (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (r : Nat) (sigma2 : NNReal) : Real :=
  let base : Real :=
    (((((Finset.univ : Finset (Fin K)).sum
      (fun a : Fin K => model.gap a)) *
      (((spec.explorationPulls : Nat) : Rat)) : Rat) : Real))
  base + (Finset.univ : Finset (Fin K)).sum
    (fun a : Fin K =>
      ((((((r : Nat) : Rat) * model.gap a : Rat) : Real))) *
        ETC.canonicalSubGaussianArmPairwiseTailReal spec model sigma2 a)

/--
Real-valued canonical probability bound for one non-best commit fiber under
direct common-sub-Gaussian finite-arm laws.

The ENNReal pairwise tail is finite because it is an `ofReal` exponential, so
the conversion preserves the concrete event and introduces no arm union.
-/
theorem real_measure_explorationArgmaxCommit_eq_arm_le_canonicalSubGaussianArmPairwiseTailReal
    {K : Nat} {Context : Type}
    [MeasurableSpace Context]
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (sigma2 : NNReal)
    (hmean : forall arm, integral (armLaw arm)
      (fun reward : Rat => (((reward : Rat) : Real))) =
        (((model.mean arm : Rat) : Real)))
    (hsubG : forall arm, ProbabilityTheory.HasSubgaussianMGF
      (fun reward : Rat =>
        ((reward : Rat) : Real) - (((model.mean arm : Rat) : Real)))
      sigma2 (armLaw arm))
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (hcontext : forall n : Nat, Measurable (context n))
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    (a : Fin K)
    (hne : a = model.bestArm -> False) :
    let defaultAction := ETC.exploreArm spec 0
    let rewardKernel := RewardKernel.contextIndependentOfActionLaws
      (Context := Context) armLaw hprob
    let policy := fun t => ETC.explorationArgmaxHistoryPolicy spec model t
    let state := fun t history => ETC.explorationArgmaxHistoryState t history
    let stepKernel :=
      RewardKernel.historyStepKernelFamily rewardKernel policy context state
        hcontext (fun t => ETC.measurable_explorationArgmaxHistoryState t)
    let trajMeasure := ProbabilityTheory.Kernel.trajMeasure
      (X := fun _ : Nat => Rat) (armLaw defaultAction) stepKernel
    trajMeasure.real
        {trajectory : RewardTrace Rat |
          ETC.explorationArgmaxCommit spec model trajectory = a} <=
      ETC.canonicalSubGaussianArmPairwiseTailReal spec model sigma2 a := by
  let defaultAction := ETC.exploreArm spec 0
  let rewardKernel := RewardKernel.contextIndependentOfActionLaws
    (Context := Context) armLaw hprob
  let policy := fun t => ETC.explorationArgmaxHistoryPolicy spec model t
  let state := fun t history => ETC.explorationArgmaxHistoryState t history
  let stepKernel :=
    RewardKernel.historyStepKernelFamily rewardKernel policy context state
      hcontext (fun t => ETC.measurable_explorationArgmaxHistoryState t)
  letI : IsProbabilityMeasure (armLaw defaultAction) := hprob defaultAction
  let trajMeasure := ProbabilityTheory.Kernel.trajMeasure
    (X := fun _ : Nat => Rat) (armLaw defaultAction) stepKernel
  let cReward : Fin K -> Nat -> NNReal := fun _ _ => sigma2
  let pairwiseProxy := ETC.centeredPairwiseRewardDiffVarianceProxy
    spec model model.bestArm cReward
  let pArm : ENNReal :=
    ETC.centeredDiffSubGaussianTail spec model pairwiseProxy a
  have hprob_arm :
      trajMeasure
          {trajectory : RewardTrace Rat |
            ETC.explorationArgmaxCommit spec model trajectory = a} <=
        pArm := by
    simpa [pArm, pairwiseProxy, cReward] using
      (ETC.explorationArgmaxHistory_prob_commit_eq_arm_le_pairwiseTail_of_armLaws
        spec model armLaw hprob sigma2 hmean hsubG
        context hcontext hexplorationPulls_pos a hne)
  have hpArm_ne_top : pArm != (none : ENNReal) := by
    simp [pArm, ETC.centeredDiffSubGaussianTail]
  simpa [Measure.real, ETC.canonicalSubGaussianArmPairwiseTailReal,
    pairwiseProxy, cReward, pArm] using
    (ENNReal.toReal_mono (by simpa using hpArm_ne_top) hprob_arm)

/--
Real-valued canonical probability bound for committing to one non-best arm.

The corresponding ENNReal tail is finite because it is `ENNReal.ofReal` of a
real exponential, so `ENNReal.toReal_mono` transports the compiled armwise
probability theorem without changing the event or taking a union.
-/
theorem real_measure_explorationArgmaxCommit_eq_arm_le_canonicalBoundedArmPairwiseTailReal
    {K : Nat} {Context : Type}
    [MeasurableSpace Context]
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (lo hi : Real)
    (hmeas : forall arm, AEMeasurable
      (fun reward : Rat => (((reward : Rat) : Real))) (armLaw arm))
    (hbound : forall arm, Filter.Eventually
      (fun reward : Rat => Set.Icc lo hi (((reward : Rat) : Real)))
      (ae (armLaw arm)))
    (hmean : forall arm, integral (armLaw arm)
      (fun reward : Rat => (((reward : Rat) : Real))) =
        (((model.mean arm : Rat) : Real)))
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (hcontext : forall n : Nat, Measurable (context n))
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    (a : Fin K)
    (hne : a = model.bestArm -> False) :
    let defaultAction := ETC.exploreArm spec 0
    let rewardKernel := RewardKernel.contextIndependentOfActionLaws
      (Context := Context) armLaw hprob
    let policy := fun t => ETC.explorationArgmaxHistoryPolicy spec model t
    let state := fun t history => ETC.explorationArgmaxHistoryState t history
    let stepKernel :=
      RewardKernel.historyStepKernelFamily rewardKernel policy context state
        hcontext (fun t => ETC.measurable_explorationArgmaxHistoryState t)
    let trajMeasure := ProbabilityTheory.Kernel.trajMeasure
      (X := fun _ : Nat => Rat) (armLaw defaultAction) stepKernel
    trajMeasure.real
        {trajectory : RewardTrace Rat |
          ETC.explorationArgmaxCommit spec model trajectory = a} <=
      ETC.canonicalBoundedArmPairwiseTailReal spec model lo hi a := by
  let defaultAction := ETC.exploreArm spec 0
  let rewardKernel := RewardKernel.contextIndependentOfActionLaws
    (Context := Context) armLaw hprob
  let policy := fun t => ETC.explorationArgmaxHistoryPolicy spec model t
  let state := fun t history => ETC.explorationArgmaxHistoryState t history
  let stepKernel :=
    RewardKernel.historyStepKernelFamily rewardKernel policy context state
      hcontext (fun t => ETC.measurable_explorationArgmaxHistoryState t)
  letI : IsProbabilityMeasure (armLaw defaultAction) := hprob defaultAction
  let trajMeasure := ProbabilityTheory.Kernel.trajMeasure
    (X := fun _ : Nat => Rat) (armLaw defaultAction) stepKernel
  let cReward : Fin K -> Nat -> NNReal := fun _ _ =>
    Concentration.intervalVarianceProxy lo hi
  let pairwiseProxy := ETC.centeredPairwiseRewardDiffVarianceProxy
    spec model model.bestArm cReward
  let pArm : ENNReal :=
    ETC.centeredDiffSubGaussianTail spec model pairwiseProxy a
  have hprob_arm :
      trajMeasure
          {trajectory : RewardTrace Rat |
            ETC.explorationArgmaxCommit spec model trajectory = a} <=
        pArm := by
    simpa [pArm, pairwiseProxy, cReward] using
      (ETC.explorationArgmaxHistory_prob_commit_eq_arm_le_pairwiseTail_of_boundedArmLaws
        spec model armLaw hprob lo hi hmeas hbound hmean
        context hcontext hexplorationPulls_pos a hne)
  have hpArm_ne_top : pArm != (none : ENNReal) := by
    simp [pArm, ETC.centeredDiffSubGaussianTail]
  simpa [Measure.real, ETC.canonicalBoundedArmPairwiseTailReal,
    pairwiseProxy, cReward, pArm] using
    (ENNReal.toReal_mono (by simpa using hpArm_ne_top) hprob_arm)

/--
Real-valued canonical wrong-commit probability bound.

The ENNReal finite tail sum is never infinite because each summand is an
`ENNReal.ofReal` exponential. This wrapper converts the compiled canonical
pairwise probability theorem with `ENNReal.toReal_mono`.
-/
theorem real_measure_explorationArgmaxCommit_ne_bestArm_le_canonicalBoundedArmWrongCommitTailBudgetReal
    {K : Nat} {Context : Type}
    [MeasurableSpace Context]
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (lo hi : Real)
    (hmeas : forall arm, AEMeasurable
      (fun reward : Rat => (((reward : Rat) : Real))) (armLaw arm))
    (hbound : forall arm, Filter.Eventually
      (fun reward : Rat => Set.Icc lo hi (((reward : Rat) : Real)))
      (ae (armLaw arm)))
    (hmean : forall arm, integral (armLaw arm)
      (fun reward : Rat => (((reward : Rat) : Real))) =
        (((model.mean arm : Rat) : Real)))
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (hcontext : forall n : Nat, Measurable (context n))
    (hexplorationPulls_pos : 0 < spec.explorationPulls) :
    let defaultAction := ETC.exploreArm spec 0
    let rewardKernel := RewardKernel.contextIndependentOfActionLaws
      (Context := Context) armLaw hprob
    let policy := fun t => ETC.explorationArgmaxHistoryPolicy spec model t
    let state := fun t history => ETC.explorationArgmaxHistoryState t history
    let stepKernel :=
      RewardKernel.historyStepKernelFamily rewardKernel policy context state
        hcontext (fun t => ETC.measurable_explorationArgmaxHistoryState t)
    let trajMeasure := ProbabilityTheory.Kernel.trajMeasure
      (X := fun _ : Nat => Rat) (armLaw defaultAction) stepKernel
    trajMeasure.real
        {trajectory : RewardTrace Rat |
          ETC.explorationArgmaxCommit spec model trajectory = model.bestArm -> False} <=
      ETC.canonicalBoundedArmWrongCommitTailBudgetReal spec model lo hi := by
  let defaultAction := ETC.exploreArm spec 0
  let rewardKernel := RewardKernel.contextIndependentOfActionLaws
    (Context := Context) armLaw hprob
  let policy := fun t => ETC.explorationArgmaxHistoryPolicy spec model t
  let state := fun t history => ETC.explorationArgmaxHistoryState t history
  let stepKernel :=
    RewardKernel.historyStepKernelFamily rewardKernel policy context state
      hcontext (fun t => ETC.measurable_explorationArgmaxHistoryState t)
  letI : IsProbabilityMeasure (armLaw defaultAction) := hprob defaultAction
  let trajMeasure := ProbabilityTheory.Kernel.trajMeasure
    (X := fun _ : Nat => Rat) (armLaw defaultAction) stepKernel
  let pWrong : ENNReal :=
    ETC.canonicalBoundedArmWrongCommitTailBudget spec model lo hi
  have hprob_wrong :
      trajMeasure
          {trajectory : RewardTrace Rat |
            ETC.explorationArgmaxCommit spec model trajectory =
              model.bestArm -> False} <=
        pWrong := by
    simpa [pWrong, ETC.canonicalBoundedArmWrongCommitTailBudget] using
      (ETC.explorationArgmaxHistory_prob_wrongCommit_le_pairwiseTailSum_of_boundedArmLaws
        spec model armLaw hprob lo hi hmeas hbound hmean
        context hcontext hexplorationPulls_pos)
  have hpWrong_ne_top : pWrong != (none : ENNReal) := by
    simp [pWrong, ETC.canonicalBoundedArmWrongCommitTailBudget,
      ETC.centeredDiffSubGaussianTail]
  simpa [Measure.real,
    ETC.canonicalBoundedArmWrongCommitTailBudgetReal, pWrong] using
    (ENNReal.toReal_mono (by simpa using hpWrong_ne_top) hprob_wrong)

/--
Bochner expected pseudo-regret bound for the generated finite-history ETC
action under its canonical bounded-arm trajectory law.

The measurable empirical-mean argmax supplies both wrong-event measurability
and pseudo-regret integrability. The preceding Real probability wrapper feeds
the generic pointwise-to-expectation ETC assembly with `model.maxGap` as the
suffix charge. This is the canonical action-dependent kernel theorem; transport
to an externally supplied environment law remains separate.
-/
theorem integral_real_pseudoRegret_explorationArgmaxGeneratedAction_le_canonicalBoundedArmMaxGapIntegralRegretBoundReal
    {K : Nat} {Context : Type}
    [MeasurableSpace Context]
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (lo hi : Real)
    (hmeas : forall arm, AEMeasurable
      (fun reward : Rat => (((reward : Rat) : Real))) (armLaw arm))
    (hbound : forall arm, Filter.Eventually
      (fun reward : Rat => Set.Icc lo hi (((reward : Rat) : Real)))
      (ae (armLaw arm)))
    (hmean : forall arm, integral (armLaw arm)
      (fun reward : Rat => (((reward : Rat) : Real))) =
        (((model.mean arm : Rat) : Real)))
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (hcontext : forall n : Nat, Measurable (context n))
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    (r : Nat) :
    let defaultAction := ETC.exploreArm spec 0
    let rewardKernel := RewardKernel.contextIndependentOfActionLaws
      (Context := Context) armLaw hprob
    let policy := fun t => ETC.explorationArgmaxHistoryPolicy spec model t
    let state := fun t history => ETC.explorationArgmaxHistoryState t history
    let stepKernel :=
      RewardKernel.historyStepKernelFamily rewardKernel policy context state
        hcontext (fun t => ETC.measurable_explorationArgmaxHistoryState t)
    let trajMeasure := ProbabilityTheory.Kernel.trajMeasure
      (X := fun _ : Nat => Rat) (armLaw defaultAction) stepKernel
    integral trajMeasure
      (fun trajectory : RewardTrace Rat =>
        (((pseudoRegret model
            (ETC.explorationArgmaxGeneratedAction spec model trajectory)
            (spec.explorationPulls * K + r) : Rat) : Real))) <=
      ETC.canonicalBoundedArmMaxGapIntegralRegretBoundReal
        spec model r lo hi := by
  let defaultAction := ETC.exploreArm spec 0
  let rewardKernel := RewardKernel.contextIndependentOfActionLaws
    (Context := Context) armLaw hprob
  let policy := fun t => ETC.explorationArgmaxHistoryPolicy spec model t
  let state := fun t history => ETC.explorationArgmaxHistoryState t history
  let stepKernel :=
    RewardKernel.historyStepKernelFamily rewardKernel policy context state
      hcontext (fun t => ETC.measurable_explorationArgmaxHistoryState t)
  letI : IsProbabilityMeasure (armLaw defaultAction) := hprob defaultAction
  let trajMeasure := ProbabilityTheory.Kernel.trajMeasure
    (X := fun _ : Nat => Rat) (armLaw defaultAction) stepKernel
  let commit : RewardTrace Rat -> Fin K :=
    fun trajectory => ETC.explorationArgmaxCommit spec model trajectory
  have hmeas_coord : forall a : Fin K,
      Measurable (fun trajectory : RewardTrace Rat =>
        (fun b : Fin K =>
          ETC.empMeanAtExploration spec model.bestArm trajectory b) a) := by
    exact ETC.measurable_empMeanAtExploration_coordinates
      (spec := spec)
      (commitArm := model.bestArm)
      (reward := fun trajectory : RewardTrace Rat => trajectory)
      (hreward := fun t => measurable_pi_apply t)
  have hmeas_commit : Measurable commit := by
    simpa [commit, ETC.explorationArgmaxCommit,
      ETC.fixedProductArgmaxCommit] using
      (ETC.measurable_commitOracle_choose_of_forall_measurable_empMean
        (oracle := ETC.argmaxCommitOracle model.hK)
        (empMean := fun trajectory : RewardTrace Rat => fun a : Fin K =>
          ETC.empMeanAtExploration spec model.bestArm trajectory a)
        hmeas_coord)
  have hmeas_wrong : MeasurableSet
      {trajectory : RewardTrace Rat |
        commit trajectory = model.bestArm -> False} := by
    simpa [commit, ETC.explorationArgmaxCommit,
      ETC.fixedProductArgmaxCommit] using
      (ETC.measurableSet_commitOracle_ne_bestArm_of_forall_measurable_empMean
        (model := model)
        (oracle := ETC.argmaxCommitOracle model.hK)
        (empMean := fun trajectory : RewardTrace Rat => fun a : Fin K =>
          ETC.empMeanAtExploration spec model.bestArm trajectory a)
        hmeas_coord)
  have hprob_wrong_real : trajMeasure.real
      {trajectory : RewardTrace Rat |
        commit trajectory = model.bestArm -> False} <=
      ETC.canonicalBoundedArmWrongCommitTailBudgetReal spec model lo hi := by
    simpa [commit] using
      (ETC.real_measure_explorationArgmaxCommit_ne_bestArm_le_canonicalBoundedArmWrongCommitTailBudgetReal
        spec model armLaw hprob lo hi hmeas hbound hmean
        context hcontext hexplorationPulls_pos)
  have hinteg : Integrable
      (fun trajectory : RewardTrace Rat =>
        (((pseudoRegret model (ETC.actionWithCommit spec (commit trajectory))
          (spec.explorationPulls * K + r) : Rat) : Real))) trajMeasure :=
    ETC.integrable_real_pseudoRegret_actionWithCommit_choice_of_measurable_commit
      (mu := trajMeasure) (spec := spec) (model := model)
      (commit := commit) (r := r) (hmeas_commit := hmeas_commit)
  have hregret :=
    ETC.integral_real_pseudoRegret_actionWithCommit_choice_le_exploration_add_suffix_badGap_prob
      (mu := trajMeasure) (spec := spec) (model := model)
      (commit := commit) (r := r)
      (badGapBound := model.maxGap)
      (pWrong := ETC.canonicalBoundedArmWrongCommitTailBudgetReal
        spec model lo hi)
      (hbadGap := fun a _hne => model.gap_le_maxGap a)
      (hbadGap_nonneg := model.maxGap_nonneg)
      (hmeas_wrong := hmeas_wrong)
      (hprob_wrong := hprob_wrong_real)
      (hinteg := hinteg)
  rw [ETC.explorationArgmaxGeneratedAction_eq_explorationArgmaxAction
    spec model hexplorationPulls_pos]
  simpa [commit, ETC.explorationArgmaxAction,
    ETC.fixedProductArgmaxAction, ETC.explorationArgmaxCommit,
    ETC.canonicalBoundedArmMaxGapIntegralRegretBoundReal] using hregret

/--
Canonical bounded-arm generated-history ETC expected-regret theorem with a
per-arm gap-weighted suffix budget.

Each non-best commit fiber uses its own canonical centered pairwise tail. The
best-arm term vanishes by `gap_bestArm`, so no artificial tail hypothesis is
needed there. This endpoint removes the max-gap finite-union collapse from the
canonical bounded-Rat theorem while retaining the same exploration term.
-/
theorem integral_real_pseudoRegret_explorationArgmaxGeneratedAction_le_canonicalBoundedArmPerArmIntegralRegretBoundReal
    {K : Nat} {Context : Type}
    [MeasurableSpace Context]
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (lo hi : Real)
    (hmeas : forall arm, AEMeasurable
      (fun reward : Rat => (((reward : Rat) : Real))) (armLaw arm))
    (hbound : forall arm, Filter.Eventually
      (fun reward : Rat => Set.Icc lo hi (((reward : Rat) : Real)))
      (ae (armLaw arm)))
    (hmean : forall arm, integral (armLaw arm)
      (fun reward : Rat => (((reward : Rat) : Real))) =
        (((model.mean arm : Rat) : Real)))
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (hcontext : forall n : Nat, Measurable (context n))
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    (r : Nat) :
    let defaultAction := ETC.exploreArm spec 0
    let rewardKernel := RewardKernel.contextIndependentOfActionLaws
      (Context := Context) armLaw hprob
    let policy := fun t => ETC.explorationArgmaxHistoryPolicy spec model t
    let state := fun t history => ETC.explorationArgmaxHistoryState t history
    let stepKernel :=
      RewardKernel.historyStepKernelFamily rewardKernel policy context state
        hcontext (fun t => ETC.measurable_explorationArgmaxHistoryState t)
    let trajMeasure := ProbabilityTheory.Kernel.trajMeasure
      (X := fun _ : Nat => Rat) (armLaw defaultAction) stepKernel
    integral trajMeasure
      (fun trajectory : RewardTrace Rat =>
        (((pseudoRegret model
            (ETC.explorationArgmaxGeneratedAction spec model trajectory)
            (spec.explorationPulls * K + r) : Rat) : Real))) <=
      ETC.canonicalBoundedArmPerArmIntegralRegretBoundReal
        spec model r lo hi := by
  let defaultAction := ETC.exploreArm spec 0
  let rewardKernel := RewardKernel.contextIndependentOfActionLaws
    (Context := Context) armLaw hprob
  let policy := fun t => ETC.explorationArgmaxHistoryPolicy spec model t
  let state := fun t history => ETC.explorationArgmaxHistoryState t history
  let stepKernel :=
    RewardKernel.historyStepKernelFamily rewardKernel policy context state
      hcontext (fun t => ETC.measurable_explorationArgmaxHistoryState t)
  letI : IsProbabilityMeasure (armLaw defaultAction) := hprob defaultAction
  let trajMeasure := ProbabilityTheory.Kernel.trajMeasure
    (X := fun _ : Nat => Rat) (armLaw defaultAction) stepKernel
  let commit : RewardTrace Rat -> Fin K :=
    fun trajectory => ETC.explorationArgmaxCommit spec model trajectory
  have hmeas_coord : forall a : Fin K,
      Measurable (fun trajectory : RewardTrace Rat =>
        (fun b : Fin K =>
          ETC.empMeanAtExploration spec model.bestArm trajectory b) a) := by
    exact ETC.measurable_empMeanAtExploration_coordinates
      (spec := spec)
      (commitArm := model.bestArm)
      (reward := fun trajectory : RewardTrace Rat => trajectory)
      (hreward := fun t => measurable_pi_apply t)
  have hmeas_commit : Measurable commit := by
    simpa [commit, ETC.explorationArgmaxCommit,
      ETC.fixedProductArgmaxCommit] using
      (ETC.measurable_commitOracle_choose_of_forall_measurable_empMean
        (oracle := ETC.argmaxCommitOracle model.hK)
        (empMean := fun trajectory : RewardTrace Rat => fun a : Fin K =>
          ETC.empMeanAtExploration spec model.bestArm trajectory a)
        hmeas_coord)
  have hregret :=
    ETC.integral_real_pseudoRegret_actionWithCommit_choice_le_exploration_add_suffix_sum_gap_mul_commit_prob
      (mu := trajMeasure) (spec := spec) (model := model)
      (commit := commit) (r := r) hmeas_commit
  have hsum :
      (Finset.univ : Finset (Fin K)).sum
          (fun a : Fin K =>
            ((((((r : Nat) : Rat) * model.gap a : Rat) : Real))) *
              trajMeasure.real
                {trajectory : RewardTrace Rat | commit trajectory = a}) <=
        (Finset.univ : Finset (Fin K)).sum
          (fun a : Fin K =>
            ((((((r : Nat) : Rat) * model.gap a : Rat) : Real))) *
              ETC.canonicalBoundedArmPairwiseTailReal
                spec model lo hi a) := by
    apply Finset.sum_le_sum
    intro a _ha
    by_cases hbest : a = model.bestArm
    case pos =>
      subst a
      simp [FiniteBanditModel.gap_bestArm]
    case neg =>
      have hprob_arm :
          trajMeasure.real
              {trajectory : RewardTrace Rat | commit trajectory = a} <=
            ETC.canonicalBoundedArmPairwiseTailReal spec model lo hi a := by
        simpa [commit] using
          (ETC.real_measure_explorationArgmaxCommit_eq_arm_le_canonicalBoundedArmPairwiseTailReal
            spec model armLaw hprob lo hi hmeas hbound hmean
            context hcontext hexplorationPulls_pos a hbest)
      have hr_nonneg : (0 : Rat) <= (((r : Nat) : Rat)) := by
        exact_mod_cast Nat.zero_le r
      have hcoeff_rat :
          (0 : Rat) <= (((r : Nat) : Rat) * model.gap a) :=
        mul_nonneg hr_nonneg (FiniteBanditModel.gap_nonneg model a)
      have hcoeff_real :
          (0 : Real) <=
            (((((r : Nat) : Rat) * model.gap a : Rat) : Real)) := by
        exact_mod_cast hcoeff_rat
      exact mul_le_mul_of_nonneg_left hprob_arm hcoeff_real
  have htotal := le_trans hregret
    (add_le_add_right hsum
      (((((Finset.univ : Finset (Fin K)).sum
        (fun a : Fin K => model.gap a)) *
        (((spec.explorationPulls : Nat) : Rat)) : Rat) : Real)))
  rw [ETC.explorationArgmaxGeneratedAction_eq_explorationArgmaxAction
    spec model hexplorationPulls_pos]
  simpa [commit, ETC.explorationArgmaxAction,
    ETC.fixedProductArgmaxAction, ETC.explorationArgmaxCommit,
    ETC.canonicalBoundedArmPerArmIntegralRegretBoundReal] using htotal

/--
Canonical generated-history ETC expected-regret theorem with direct common-
sub-Gaussian finite-arm laws and a per-arm gap-weighted suffix budget.

Each non-best commit fiber is charged by its own direct-MGF pairwise tail. The
best-arm term vanishes by `gap_bestArm`; no bounded-support assumption, max-gap
collapse, or arm union is used. Rewards and model means remain `Rat`-valued.
-/
theorem integral_real_pseudoRegret_explorationArgmaxGeneratedAction_le_canonicalSubGaussianArmPerArmIntegralRegretBoundReal
    {K : Nat} {Context : Type}
    [MeasurableSpace Context]
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (sigma2 : NNReal)
    (hmean : forall arm, integral (armLaw arm)
      (fun reward : Rat => (((reward : Rat) : Real))) =
        (((model.mean arm : Rat) : Real)))
    (hsubG : forall arm, ProbabilityTheory.HasSubgaussianMGF
      (fun reward : Rat =>
        ((reward : Rat) : Real) - (((model.mean arm : Rat) : Real)))
      sigma2 (armLaw arm))
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (hcontext : forall n : Nat, Measurable (context n))
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    (r : Nat) :
    let defaultAction := ETC.exploreArm spec 0
    let rewardKernel := RewardKernel.contextIndependentOfActionLaws
      (Context := Context) armLaw hprob
    let policy := fun t => ETC.explorationArgmaxHistoryPolicy spec model t
    let state := fun t history => ETC.explorationArgmaxHistoryState t history
    let stepKernel :=
      RewardKernel.historyStepKernelFamily rewardKernel policy context state
        hcontext (fun t => ETC.measurable_explorationArgmaxHistoryState t)
    let trajMeasure := ProbabilityTheory.Kernel.trajMeasure
      (X := fun _ : Nat => Rat) (armLaw defaultAction) stepKernel
    integral trajMeasure
      (fun trajectory : RewardTrace Rat =>
        (((pseudoRegret model
            (ETC.explorationArgmaxGeneratedAction spec model trajectory)
            (spec.explorationPulls * K + r) : Rat) : Real))) <=
      ETC.canonicalSubGaussianArmPerArmIntegralRegretBoundReal
        spec model r sigma2 := by
  let defaultAction := ETC.exploreArm spec 0
  let rewardKernel := RewardKernel.contextIndependentOfActionLaws
    (Context := Context) armLaw hprob
  let policy := fun t => ETC.explorationArgmaxHistoryPolicy spec model t
  let state := fun t history => ETC.explorationArgmaxHistoryState t history
  let stepKernel :=
    RewardKernel.historyStepKernelFamily rewardKernel policy context state
      hcontext (fun t => ETC.measurable_explorationArgmaxHistoryState t)
  letI : IsProbabilityMeasure (armLaw defaultAction) := hprob defaultAction
  let trajMeasure := ProbabilityTheory.Kernel.trajMeasure
    (X := fun _ : Nat => Rat) (armLaw defaultAction) stepKernel
  let commit : RewardTrace Rat -> Fin K :=
    fun trajectory => ETC.explorationArgmaxCommit spec model trajectory
  have hmeas_coord : forall a : Fin K,
      Measurable (fun trajectory : RewardTrace Rat =>
        (fun b : Fin K =>
          ETC.empMeanAtExploration spec model.bestArm trajectory b) a) := by
    exact ETC.measurable_empMeanAtExploration_coordinates
      (spec := spec)
      (commitArm := model.bestArm)
      (reward := fun trajectory : RewardTrace Rat => trajectory)
      (hreward := fun t => measurable_pi_apply t)
  have hmeas_commit : Measurable commit := by
    simpa [commit, ETC.explorationArgmaxCommit,
      ETC.fixedProductArgmaxCommit] using
      (ETC.measurable_commitOracle_choose_of_forall_measurable_empMean
        (oracle := ETC.argmaxCommitOracle model.hK)
        (empMean := fun trajectory : RewardTrace Rat => fun a : Fin K =>
          ETC.empMeanAtExploration spec model.bestArm trajectory a)
        hmeas_coord)
  have hregret :=
    ETC.integral_real_pseudoRegret_actionWithCommit_choice_le_exploration_add_suffix_sum_gap_mul_commit_prob
      (mu := trajMeasure) (spec := spec) (model := model)
      (commit := commit) (r := r) hmeas_commit
  have hsum :
      (Finset.univ : Finset (Fin K)).sum
          (fun a : Fin K =>
            ((((((r : Nat) : Rat) * model.gap a : Rat) : Real))) *
              trajMeasure.real
                {trajectory : RewardTrace Rat | commit trajectory = a}) <=
        (Finset.univ : Finset (Fin K)).sum
          (fun a : Fin K =>
            ((((((r : Nat) : Rat) * model.gap a : Rat) : Real))) *
              ETC.canonicalSubGaussianArmPairwiseTailReal
                spec model sigma2 a) := by
    apply Finset.sum_le_sum
    intro a _ha
    by_cases hbest : a = model.bestArm
    case pos =>
      subst a
      simp [FiniteBanditModel.gap_bestArm]
    case neg =>
      have hprob_arm :
          trajMeasure.real
              {trajectory : RewardTrace Rat | commit trajectory = a} <=
            ETC.canonicalSubGaussianArmPairwiseTailReal
              spec model sigma2 a := by
        simpa [commit] using
          (ETC.real_measure_explorationArgmaxCommit_eq_arm_le_canonicalSubGaussianArmPairwiseTailReal
            spec model armLaw hprob sigma2 hmean hsubG
            context hcontext hexplorationPulls_pos a hbest)
      have hr_nonneg : (0 : Rat) <= (((r : Nat) : Rat)) := by
        exact_mod_cast Nat.zero_le r
      have hcoeff_rat :
          (0 : Rat) <= (((r : Nat) : Rat) * model.gap a) :=
        mul_nonneg hr_nonneg (FiniteBanditModel.gap_nonneg model a)
      have hcoeff_real :
          (0 : Real) <=
            (((((r : Nat) : Rat) * model.gap a : Rat) : Real)) := by
        exact_mod_cast hcoeff_rat
      exact mul_le_mul_of_nonneg_left hprob_arm hcoeff_real
  have htotal := le_trans hregret
    (add_le_add_right hsum
      (((((Finset.univ : Finset (Fin K)).sum
        (fun a : Fin K => model.gap a)) *
        (((spec.explorationPulls : Nat) : Rat)) : Rat) : Real)))
  rw [ETC.explorationArgmaxGeneratedAction_eq_explorationArgmaxAction
    spec model hexplorationPulls_pos]
  simpa [commit, ETC.explorationArgmaxAction,
    ETC.fixedProductArgmaxAction, ETC.explorationArgmaxCommit,
    ETC.canonicalSubGaussianArmPerArmIntegralRegretBoundReal] using htotal

/--
Finite-prefix realization of the generated ETC pseudo-regret integrand.

The completed trace is only an implementation device. Once the supplied
history contains the complete exploration prefix, the value agrees with the
original generated-history action by the factorization theorem below.
-/
noncomputable def explorationArgmaxPrefixRegretReal
    {K : Nat} (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (t r : Nat) (history : History.FiniteRewardHistory Rat t) : Real :=
  (((pseudoRegret model
      (ETC.explorationArgmaxAction spec model
        (History.completeRewardTrace t history (0 : Rat)))
      (spec.explorationPulls * K + r) : Rat) : Real))

/-- The finite-prefix ETC pseudo-regret realization is measurable. -/
theorem measurable_explorationArgmaxPrefixRegretReal
    {K : Nat} (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (t r : Nat) :
    Measurable (ETC.explorationArgmaxPrefixRegretReal spec model t r) := by
  let reward : History.FiniteRewardHistory Rat t -> RewardTrace Rat :=
    fun history => History.completeRewardTrace t history (0 : Rat)
  let commit : History.FiniteRewardHistory Rat t -> Fin K :=
    fun history => ETC.explorationArgmaxCommit spec model (reward history)
  have hreward : forall s : Nat,
      Measurable (fun history : History.FiniteRewardHistory Rat t =>
        reward history s) := by
    intro s
    exact (measurable_pi_apply s).comp
      (ETC.measurable_explorationArgmaxHistoryState t)
  have hmeas_coord : forall a : Fin K,
      Measurable (fun history : History.FiniteRewardHistory Rat t =>
        ETC.empMeanAtExploration spec model.bestArm (reward history) a) := by
    exact ETC.measurable_empMeanAtExploration_coordinates
      (spec := spec) (commitArm := model.bestArm)
      (reward := reward) (hreward := hreward)
  have hcommit : Measurable commit := by
    simpa [commit, reward, ETC.explorationArgmaxCommit,
      ETC.fixedProductArgmaxCommit] using
      (ETC.measurable_commitOracle_choose_of_forall_measurable_empMean
        (oracle := ETC.argmaxCommitOracle model.hK)
        (empMean := fun history : History.FiniteRewardHistory Rat t =>
          fun a : Fin K =>
            ETC.empMeanAtExploration spec model.bestArm (reward history) a)
        hmeas_coord)
  have haction : forall s : Nat,
      Measurable (fun history : History.FiniteRewardHistory Rat t =>
        ETC.explorationArgmaxAction spec model (reward history) s) := by
    intro s
    have hfromCommit : Measurable
        (fun arm : Fin K => ETC.actionWithCommit spec arm s) :=
      measurable_of_finite _
    simpa [ETC.explorationArgmaxAction, ETC.fixedProductArgmaxAction,
      ETC.explorationArgmaxCommit, commit, reward] using
      hfromCommit.comp hcommit
  have hpseudo : Measurable
      (fun history : History.FiniteRewardHistory Rat t =>
        pseudoRegret model
          (ETC.explorationArgmaxAction spec model (reward history))
          (spec.explorationPulls * K + r)) :=
    measurable_pseudoRegret model
      (fun history => ETC.explorationArgmaxAction spec model (reward history))
      haction (spec.explorationPulls * K + r)
  have hcast : Measurable (fun q : Rat => (q : Real)) :=
    measurable_of_countable _
  simpa [ETC.explorationArgmaxPrefixRegretReal, reward] using
    hcast.comp hpseudo

/--
The finite-prefix realization agrees with canonical ETC whenever the retained
history covers every exploration reward coordinate.
-/
theorem explorationArgmaxPrefixRegretReal_finiteRewardHistoryOfTrace
    {K : Nat} (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (reward : RewardTrace Rat) (t r : Nat)
    (horizon_le : spec.explorationPulls * K <= t + 1) :
    ETC.explorationArgmaxPrefixRegretReal spec model t r
        (History.finiteRewardHistoryOfTrace reward t) =
      (((pseudoRegret model
          (ETC.explorationArgmaxAction spec model reward)
          (spec.explorationPulls * K + r) : Rat) : Real)) := by
  have hscores :
      (fun a : Fin K =>
        ETC.empMeanAtExploration spec model.bestArm
          (History.completeRewardTrace t
            (History.finiteRewardHistoryOfTrace reward t) (0 : Rat)) a) =
      (fun a : Fin K =>
        ETC.empMeanAtExploration spec model.bestArm reward a) := by
    funext a
    exact
      ETC.empMeanAtExploration_completeRewardTrace_eq_of_explorationHorizon_le
        spec model.bestArm reward t horizon_le a
  simp [ETC.explorationArgmaxPrefixRegretReal,
    ETC.explorationArgmaxAction, ETC.fixedProductArgmaxAction,
    ETC.fixedProductArgmaxCommit, hscores]

/--
Generated-history form of the finite exploration-prefix regret factorization.
-/
theorem explorationArgmaxPrefixRegretReal_finiteRewardHistoryOfTrace_generated
    {K : Nat} (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (reward : RewardTrace Rat) (t r : Nat)
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    (horizon_le : spec.explorationPulls * K <= t + 1) :
    ETC.explorationArgmaxPrefixRegretReal spec model t r
        (History.finiteRewardHistoryOfTrace reward t) =
      (((pseudoRegret model
          (ETC.explorationArgmaxGeneratedAction spec model reward)
          (spec.explorationPulls * K + r) : Rat) : Real)) := by
  rw [ETC.explorationArgmaxGeneratedAction_eq_explorationArgmaxAction
    spec model hexplorationPulls_pos]
  exact ETC.explorationArgmaxPrefixRegretReal_finiteRewardHistoryOfTrace
    spec model reward t r horizon_le

/--
The generated-history ETC pseudo-regret integral depends only on the finite
exploration-prefix pushforward.

This law-transport equality is independent of the reward-law or concentration
route used later to bound either integral. It packages the measurable prefix
factorization once for both max-gap and per-arm canonical endpoints.
-/
theorem integral_real_pseudoRegret_explorationArgmaxGeneratedAction_eq_of_explorationPrefix_map_eq
    {K : Nat}
    (mu nu : Measure (RewardTrace Rat))
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    (r : Nat)
    (hprefix :
      let explorationLast := spec.explorationPulls * K - 1
      Measure.map
          (fun trajectory : RewardTrace Rat =>
            History.finiteRewardHistoryOfTrace trajectory explorationLast) mu =
        Measure.map
          (fun trajectory : RewardTrace Rat =>
            History.finiteRewardHistoryOfTrace trajectory explorationLast) nu) :
    integral mu
        (fun trajectory : RewardTrace Rat =>
          (((pseudoRegret model
              (ETC.explorationArgmaxGeneratedAction spec model trajectory)
              (spec.explorationPulls * K + r) : Rat) : Real))) =
      integral nu
        (fun trajectory : RewardTrace Rat =>
          (((pseudoRegret model
              (ETC.explorationArgmaxGeneratedAction spec model trajectory)
              (spec.explorationPulls * K + r) : Rat) : Real))) := by
  let explorationLast := spec.explorationPulls * K - 1
  let prefixMap :
      RewardTrace Rat -> History.FiniteRewardHistory Rat explorationLast :=
    fun trajectory =>
      History.finiteRewardHistoryOfTrace trajectory explorationLast
  let prefixRegret : History.FiniteRewardHistory Rat explorationLast -> Real :=
    ETC.explorationArgmaxPrefixRegretReal spec model explorationLast r
  let regret : RewardTrace Rat -> Real :=
    fun trajectory =>
      (((pseudoRegret model
          (ETC.explorationArgmaxGeneratedAction spec model trajectory)
          (spec.explorationPulls * K + r) : Rat) : Real))
  have hexplorationHorizon_pos : 0 < spec.explorationPulls * K :=
    Nat.mul_pos hexplorationPulls_pos model.hK
  have hexplorationHorizon_le :
      spec.explorationPulls * K <= explorationLast + 1 := by
    simpa [explorationLast] using
      (Nat.succ_pred_eq_of_pos hexplorationHorizon_pos).symm.le
  have hprefix_meas : Measurable prefixMap := by
    exact History.measurable_finiteRewardHistoryOfTrace
      (fun trajectory : RewardTrace Rat => trajectory)
      (fun t => measurable_pi_apply t) explorationLast
  have hprefixRegret_meas : Measurable prefixRegret := by
    exact ETC.measurable_explorationArgmaxPrefixRegretReal
      spec model explorationLast r
  have hfactor : forall trajectory : RewardTrace Rat,
      prefixRegret (prefixMap trajectory) = regret trajectory := by
    intro trajectory
    exact
      ETC.explorationArgmaxPrefixRegretReal_finiteRewardHistoryOfTrace_generated
        spec model trajectory explorationLast r hexplorationPulls_pos
        hexplorationHorizon_le
  calc
    integral mu regret = integral mu (fun trajectory =>
        prefixRegret (prefixMap trajectory)) := by
      exact integral_congr_ae <| Filter.Eventually.of_forall <| fun trajectory =>
        (hfactor trajectory).symm
    _ = integral (Measure.map prefixMap mu) prefixRegret := by
      exact (integral_map hprefix_meas.aemeasurable
        hprefixRegret_meas.aestronglyMeasurable).symm
    _ = integral (Measure.map prefixMap nu) prefixRegret := by
      rw [hprefix]
    _ = integral nu (fun trajectory =>
        prefixRegret (prefixMap trajectory)) := by
      exact integral_map hprefix_meas.aemeasurable
        hprefixRegret_meas.aestronglyMeasurable
    _ = integral nu regret := by
      exact integral_congr_ae <| Filter.Eventually.of_forall hfactor

/--
External-law ETC expected-regret theorem from exploration-prefix law equality.

The external reward law need not equal the canonical Ionescu-Tulcea law on
the full infinite trajectory. It is enough that their pushforwards to the
`m * K` exploration rewards agree: the generated ETC action and its finite
horizon pseudo-regret factor through exactly that prefix. This is the law
transport surface needed by external stationary-bandit environment models.
-/
theorem integral_real_pseudoRegret_explorationArgmaxGeneratedAction_le_canonicalBoundedArmMaxGapIntegralRegretBoundReal_of_explorationPrefix_map_eq
    {K : Nat} {Context : Type}
    [MeasurableSpace Context]
    (mu : Measure (RewardTrace Rat)) [IsProbabilityMeasure mu]
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (lo hi : Real)
    (hmeas : forall arm, AEMeasurable
      (fun reward : Rat => (((reward : Rat) : Real))) (armLaw arm))
    (hbound : forall arm, Filter.Eventually
      (fun reward : Rat => Set.Icc lo hi (((reward : Rat) : Real)))
      (ae (armLaw arm)))
    (hmean : forall arm, integral (armLaw arm)
      (fun reward : Rat => (((reward : Rat) : Real))) =
        (((model.mean arm : Rat) : Real)))
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (hcontext : forall n : Nat, Measurable (context n))
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    (r : Nat)
    (hprefix :
      let defaultAction := ETC.exploreArm spec 0
      let rewardKernel := RewardKernel.contextIndependentOfActionLaws
        (Context := Context) armLaw hprob
      let policy := fun t => ETC.explorationArgmaxHistoryPolicy spec model t
      let state := fun t history => ETC.explorationArgmaxHistoryState t history
      let stepKernel :=
        RewardKernel.historyStepKernelFamily rewardKernel policy context state
          hcontext (fun t => ETC.measurable_explorationArgmaxHistoryState t)
      let trajMeasure := ProbabilityTheory.Kernel.trajMeasure
        (X := fun _ : Nat => Rat) (armLaw defaultAction) stepKernel
      let explorationLast := spec.explorationPulls * K - 1
      Measure.map
          (fun trajectory : RewardTrace Rat =>
            History.finiteRewardHistoryOfTrace trajectory explorationLast) mu =
        Measure.map
          (fun trajectory : RewardTrace Rat =>
            History.finiteRewardHistoryOfTrace trajectory explorationLast)
          trajMeasure) :
    integral mu
      (fun trajectory : RewardTrace Rat =>
        (((pseudoRegret model
            (ETC.explorationArgmaxGeneratedAction spec model trajectory)
            (spec.explorationPulls * K + r) : Rat) : Real))) <=
      ETC.canonicalBoundedArmMaxGapIntegralRegretBoundReal
        spec model r lo hi := by
  let defaultAction := ETC.exploreArm spec 0
  let rewardKernel := RewardKernel.contextIndependentOfActionLaws
    (Context := Context) armLaw hprob
  let policy := fun t => ETC.explorationArgmaxHistoryPolicy spec model t
  let state := fun t history => ETC.explorationArgmaxHistoryState t history
  let stepKernel :=
    RewardKernel.historyStepKernelFamily rewardKernel policy context state
      hcontext (fun t => ETC.measurable_explorationArgmaxHistoryState t)
  letI : IsProbabilityMeasure (armLaw defaultAction) := hprob defaultAction
  let trajMeasure := ProbabilityTheory.Kernel.trajMeasure
    (X := fun _ : Nat => Rat) (armLaw defaultAction) stepKernel
  let explorationLast := spec.explorationPulls * K - 1
  let prefixMap :
      RewardTrace Rat -> History.FiniteRewardHistory Rat explorationLast :=
    fun trajectory =>
      History.finiteRewardHistoryOfTrace trajectory explorationLast
  let prefixRegret : History.FiniteRewardHistory Rat explorationLast -> Real :=
    ETC.explorationArgmaxPrefixRegretReal spec model explorationLast r
  let regret : RewardTrace Rat -> Real :=
    fun trajectory =>
      (((pseudoRegret model
          (ETC.explorationArgmaxGeneratedAction spec model trajectory)
          (spec.explorationPulls * K + r) : Rat) : Real))
  have hexplorationHorizon_pos : 0 < spec.explorationPulls * K :=
    Nat.mul_pos hexplorationPulls_pos model.hK
  have hexplorationHorizon_le :
      spec.explorationPulls * K <= explorationLast + 1 := by
    simpa [explorationLast] using
      (Nat.succ_pred_eq_of_pos hexplorationHorizon_pos).symm.le
  have hprefix_meas : Measurable prefixMap := by
    exact History.measurable_finiteRewardHistoryOfTrace
      (fun trajectory : RewardTrace Rat => trajectory)
      (fun t => measurable_pi_apply t) explorationLast
  have hprefixRegret_meas : Measurable prefixRegret := by
    exact ETC.measurable_explorationArgmaxPrefixRegretReal
      spec model explorationLast r
  have hfactor : forall trajectory : RewardTrace Rat,
      prefixRegret (prefixMap trajectory) = regret trajectory := by
    intro trajectory
    exact
      ETC.explorationArgmaxPrefixRegretReal_finiteRewardHistoryOfTrace_generated
        spec model trajectory explorationLast r hexplorationPulls_pos
        hexplorationHorizon_le
  have htransport : integral mu regret = integral trajMeasure regret := by
    calc
      integral mu regret = integral mu (fun trajectory =>
          prefixRegret (prefixMap trajectory)) := by
        exact integral_congr_ae <| Filter.Eventually.of_forall <| fun trajectory =>
          (hfactor trajectory).symm
      _ = integral (Measure.map prefixMap mu) prefixRegret := by
        exact (integral_map hprefix_meas.aemeasurable
          hprefixRegret_meas.aestronglyMeasurable).symm
      _ = integral (Measure.map prefixMap trajMeasure) prefixRegret := by
        rw [hprefix]
      _ = integral trajMeasure (fun trajectory =>
          prefixRegret (prefixMap trajectory)) := by
        exact integral_map hprefix_meas.aemeasurable
          hprefixRegret_meas.aestronglyMeasurable
      _ = integral trajMeasure regret := by
        exact integral_congr_ae <| Filter.Eventually.of_forall hfactor
  rw [htransport]
  exact
    ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_le_canonicalBoundedArmMaxGapIntegralRegretBoundReal
      spec model armLaw hprob lo hi hmeas hbound hmean context hcontext
      hexplorationPulls_pos r

/--
External-law canonical per-arm ETC expected-regret theorem from exploration-
prefix law equality.

The external reward law only needs the same `m * K` exploration-prefix
pushforward as the canonical generated-history trajectory. The resulting bound
preserves each arm's own gap-weighted pairwise tail and takes no union over
commit arms.
-/
theorem integral_real_pseudoRegret_explorationArgmaxGeneratedAction_le_canonicalBoundedArmPerArmIntegralRegretBoundReal_of_explorationPrefix_map_eq
    {K : Nat} {Context : Type}
    [MeasurableSpace Context]
    (mu : Measure (RewardTrace Rat)) [IsProbabilityMeasure mu]
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (lo hi : Real)
    (hmeas : forall arm, AEMeasurable
      (fun reward : Rat => (((reward : Rat) : Real))) (armLaw arm))
    (hbound : forall arm, Filter.Eventually
      (fun reward : Rat => Set.Icc lo hi (((reward : Rat) : Real)))
      (ae (armLaw arm)))
    (hmean : forall arm, integral (armLaw arm)
      (fun reward : Rat => (((reward : Rat) : Real))) =
        (((model.mean arm : Rat) : Real)))
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (hcontext : forall n : Nat, Measurable (context n))
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    (r : Nat)
    (hprefix :
      let defaultAction := ETC.exploreArm spec 0
      let rewardKernel := RewardKernel.contextIndependentOfActionLaws
        (Context := Context) armLaw hprob
      let policy := fun t => ETC.explorationArgmaxHistoryPolicy spec model t
      let state := fun t history => ETC.explorationArgmaxHistoryState t history
      let stepKernel :=
        RewardKernel.historyStepKernelFamily rewardKernel policy context state
          hcontext (fun t => ETC.measurable_explorationArgmaxHistoryState t)
      let trajMeasure := ProbabilityTheory.Kernel.trajMeasure
        (X := fun _ : Nat => Rat) (armLaw defaultAction) stepKernel
      let explorationLast := spec.explorationPulls * K - 1
      Measure.map
          (fun trajectory : RewardTrace Rat =>
            History.finiteRewardHistoryOfTrace trajectory explorationLast) mu =
        Measure.map
          (fun trajectory : RewardTrace Rat =>
            History.finiteRewardHistoryOfTrace trajectory explorationLast)
          trajMeasure) :
    integral mu
      (fun trajectory : RewardTrace Rat =>
        (((pseudoRegret model
            (ETC.explorationArgmaxGeneratedAction spec model trajectory)
            (spec.explorationPulls * K + r) : Rat) : Real))) <=
      ETC.canonicalBoundedArmPerArmIntegralRegretBoundReal
        spec model r lo hi := by
  let defaultAction := ETC.exploreArm spec 0
  let rewardKernel := RewardKernel.contextIndependentOfActionLaws
    (Context := Context) armLaw hprob
  let policy := fun t => ETC.explorationArgmaxHistoryPolicy spec model t
  let state := fun t history => ETC.explorationArgmaxHistoryState t history
  let stepKernel :=
    RewardKernel.historyStepKernelFamily rewardKernel policy context state
      hcontext (fun t => ETC.measurable_explorationArgmaxHistoryState t)
  letI : IsProbabilityMeasure (armLaw defaultAction) := hprob defaultAction
  let trajMeasure := ProbabilityTheory.Kernel.trajMeasure
    (X := fun _ : Nat => Rat) (armLaw defaultAction) stepKernel
  have htransport :
      integral mu
          (fun trajectory : RewardTrace Rat =>
            (((pseudoRegret model
                (ETC.explorationArgmaxGeneratedAction spec model trajectory)
                (spec.explorationPulls * K + r) : Rat) : Real))) =
        integral trajMeasure
          (fun trajectory : RewardTrace Rat =>
            (((pseudoRegret model
                (ETC.explorationArgmaxGeneratedAction spec model trajectory)
                (spec.explorationPulls * K + r) : Rat) : Real))) := by
    apply
      ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_eq_of_explorationPrefix_map_eq
        mu trajMeasure spec model hexplorationPulls_pos r
    simpa [defaultAction, rewardKernel, policy, state, stepKernel,
      trajMeasure] using hprefix
  rw [htransport]
  exact
    ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_le_canonicalBoundedArmPerArmIntegralRegretBoundReal
      spec model armLaw hprob lo hi hmeas hbound hmean context hcontext
      hexplorationPulls_pos r

/--
External-law common-sub-Gaussian per-arm ETC expected regret from exploration-
prefix law equality.

Only the `m * K` exploration reward-prefix pushforward must match the canonical
generated-history trajectory. The direct-MGF gap-weighted armwise budget is
transported without a full trajectory law, suffix law, or arm union.
-/
theorem integral_real_pseudoRegret_explorationArgmaxGeneratedAction_le_canonicalSubGaussianArmPerArmIntegralRegretBoundReal_of_explorationPrefix_map_eq
    {K : Nat} {Context : Type}
    [MeasurableSpace Context]
    (mu : Measure (RewardTrace Rat)) [IsProbabilityMeasure mu]
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (sigma2 : NNReal)
    (hmean : forall arm, integral (armLaw arm)
      (fun reward : Rat => (((reward : Rat) : Real))) =
        (((model.mean arm : Rat) : Real)))
    (hsubG : forall arm, ProbabilityTheory.HasSubgaussianMGF
      (fun reward : Rat =>
        ((reward : Rat) : Real) - (((model.mean arm : Rat) : Real)))
      sigma2 (armLaw arm))
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (hcontext : forall n : Nat, Measurable (context n))
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    (r : Nat)
    (hprefix :
      let defaultAction := ETC.exploreArm spec 0
      let rewardKernel := RewardKernel.contextIndependentOfActionLaws
        (Context := Context) armLaw hprob
      let policy := fun t => ETC.explorationArgmaxHistoryPolicy spec model t
      let state := fun t history => ETC.explorationArgmaxHistoryState t history
      let stepKernel :=
        RewardKernel.historyStepKernelFamily rewardKernel policy context state
          hcontext (fun t => ETC.measurable_explorationArgmaxHistoryState t)
      let trajMeasure := ProbabilityTheory.Kernel.trajMeasure
        (X := fun _ : Nat => Rat) (armLaw defaultAction) stepKernel
      let explorationLast := spec.explorationPulls * K - 1
      Measure.map
          (fun trajectory : RewardTrace Rat =>
            History.finiteRewardHistoryOfTrace trajectory explorationLast) mu =
        Measure.map
          (fun trajectory : RewardTrace Rat =>
            History.finiteRewardHistoryOfTrace trajectory explorationLast)
          trajMeasure) :
    integral mu
      (fun trajectory : RewardTrace Rat =>
        (((pseudoRegret model
            (ETC.explorationArgmaxGeneratedAction spec model trajectory)
            (spec.explorationPulls * K + r) : Rat) : Real))) <=
      ETC.canonicalSubGaussianArmPerArmIntegralRegretBoundReal
        spec model r sigma2 := by
  let defaultAction := ETC.exploreArm spec 0
  let rewardKernel := RewardKernel.contextIndependentOfActionLaws
    (Context := Context) armLaw hprob
  let policy := fun t => ETC.explorationArgmaxHistoryPolicy spec model t
  let state := fun t history => ETC.explorationArgmaxHistoryState t history
  let stepKernel :=
    RewardKernel.historyStepKernelFamily rewardKernel policy context state
      hcontext (fun t => ETC.measurable_explorationArgmaxHistoryState t)
  letI : IsProbabilityMeasure (armLaw defaultAction) := hprob defaultAction
  let trajMeasure := ProbabilityTheory.Kernel.trajMeasure
    (X := fun _ : Nat => Rat) (armLaw defaultAction) stepKernel
  have htransport :
      integral mu
          (fun trajectory : RewardTrace Rat =>
            (((pseudoRegret model
                (ETC.explorationArgmaxGeneratedAction spec model trajectory)
                (spec.explorationPulls * K + r) : Rat) : Real))) =
        integral trajMeasure
          (fun trajectory : RewardTrace Rat =>
            (((pseudoRegret model
                (ETC.explorationArgmaxGeneratedAction spec model trajectory)
                (spec.explorationPulls * K + r) : Rat) : Real))) := by
    apply
      ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_eq_of_explorationPrefix_map_eq
        mu trajMeasure spec model hexplorationPulls_pos r
    simpa [defaultAction, rewardKernel, policy, state, stepKernel,
      trajMeasure] using hprefix
  rw [htransport]
  exact
    ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_le_canonicalSubGaussianArmPerArmIntegralRegretBoundReal
      spec model armLaw hprob sigma2 hmean hsubG context hcontext
      hexplorationPulls_pos r

/--
External-process ETC expected regret from initial and successor conditional
reward laws.

The contract is local to the exploration prefix: coordinate measurability, the
zeroth reward marginal, and the conditional distribution of reward `i + 1`
given rewards through `i` for `i < m * K - 1`. The generic finite-prefix law
result identifies the required pushforward with the Ionescu-Tulcea process;
the preceding prefix-transport theorem then supplies the regret bound.
-/
theorem integral_real_pseudoRegret_explorationArgmaxGeneratedAction_reward_le_canonicalBoundedArmMaxGapIntegralRegretBoundReal_of_initial_map_eq_condDistrib
    {Omega : Type*} {K : Nat} {Context : Type}
    [MeasurableSpace Omega] [MeasurableSpace Context]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (lo hi : Real)
    (hmeas : forall arm, AEMeasurable
      (fun reward : Rat => (((reward : Rat) : Real))) (armLaw arm))
    (hbound : forall arm, Filter.Eventually
      (fun reward : Rat => Set.Icc lo hi (((reward : Rat) : Real)))
      (ae (armLaw arm)))
    (hmean : forall arm, integral (armLaw arm)
      (fun reward : Rat => (((reward : Rat) : Real))) =
        (((model.mean arm : Rat) : Real)))
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (hcontext : forall n : Nat, Measurable (context n))
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    (r : Nat)
    (hzero : Measure.map (fun omega : Omega => reward omega 0) mu =
      armLaw (ETC.exploreArm spec 0))
    (hcond :
      let rewardKernel := RewardKernel.contextIndependentOfActionLaws
        (Context := Context) armLaw hprob
      let policy := fun t => ETC.explorationArgmaxHistoryPolicy spec model t
      let state := fun t history => ETC.explorationArgmaxHistoryState t history
      let stepKernel :=
        RewardKernel.historyStepKernelFamily rewardKernel policy context state
          hcontext (fun t => ETC.measurable_explorationArgmaxHistoryState t)
      let explorationLast := spec.explorationPulls * K - 1
      forall i : Nat, i < explorationLast ->
        ProbabilityTheory.condDistrib
            (fun omega : Omega => reward omega (i + 1))
            (fun omega : Omega =>
              History.finiteRewardHistoryOfTrace (reward omega) i)
            mu =ᵐ[
              mu.map (fun omega : Omega =>
                History.finiteRewardHistoryOfTrace (reward omega) i)]
          stepKernel i) :
    integral mu
      (fun omega : Omega =>
        (((pseudoRegret model
            (ETC.explorationArgmaxGeneratedAction spec model (reward omega))
            (spec.explorationPulls * K + r) : Rat) : Real))) <=
      ETC.canonicalBoundedArmMaxGapIntegralRegretBoundReal
        spec model r lo hi := by
  let defaultAction := ETC.exploreArm spec 0
  let rewardKernel := RewardKernel.contextIndependentOfActionLaws
    (Context := Context) armLaw hprob
  let policy := fun t => ETC.explorationArgmaxHistoryPolicy spec model t
  let state := fun t history => ETC.explorationArgmaxHistoryState t history
  let stepKernel :=
    RewardKernel.historyStepKernelFamily rewardKernel policy context state
      hcontext (fun t => ETC.measurable_explorationArgmaxHistoryState t)
  letI : IsProbabilityMeasure (armLaw defaultAction) := hprob defaultAction
  let trajMeasure := ProbabilityTheory.Kernel.trajMeasure
    (X := fun _ : Nat => Rat) (armLaw defaultAction) stepKernel
  let explorationLast := spec.explorationPulls * K - 1
  let externalLaw := Measure.map reward mu
  have hreward_meas : Measurable reward := measurable_pi_lambda _ hreward
  letI : IsProbabilityMeasure externalLaw :=
    Measure.isProbabilityMeasure_map hreward_meas.aemeasurable
  let prefixMap :
      RewardTrace Rat -> History.FiniteRewardHistory Rat explorationLast :=
    fun trajectory =>
      History.finiteRewardHistoryOfTrace trajectory explorationLast
  have hprefix_meas : Measurable prefixMap :=
    History.measurable_finiteRewardHistoryOfTrace
      (fun trajectory : RewardTrace Rat => trajectory)
      (fun t => measurable_pi_apply t) explorationLast
  have hprefix_external :
      Measure.map prefixMap externalLaw = Measure.map prefixMap trajMeasure := by
    change Measure.map prefixMap (Measure.map reward mu) = _
    rw [Measure.map_map hprefix_meas hreward_meas]
    exact RewardKernel.rewardTrace_prefix_map_eq_trajMeasure_of_condDistrib
      mu (armLaw defaultAction) reward hreward stepKernel hzero explorationLast hcond
  have hbound_external :=
    ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_le_canonicalBoundedArmMaxGapIntegralRegretBoundReal_of_explorationPrefix_map_eq
      externalLaw spec model armLaw hprob lo hi hmeas hbound hmean
      context hcontext hexplorationPulls_pos r hprefix_external
  let regret : RewardTrace Rat -> Real :=
    fun trajectory =>
      (((pseudoRegret model
          (ETC.explorationArgmaxGeneratedAction spec model trajectory)
          (spec.explorationPulls * K + r) : Rat) : Real))
  let prefixRegret : History.FiniteRewardHistory Rat explorationLast -> Real :=
    ETC.explorationArgmaxPrefixRegretReal spec model explorationLast r
  have hexplorationHorizon_pos : 0 < spec.explorationPulls * K :=
    Nat.mul_pos hexplorationPulls_pos model.hK
  have hexplorationHorizon_le :
      spec.explorationPulls * K <= explorationLast + 1 := by
    simpa [explorationLast] using
      (Nat.succ_pred_eq_of_pos hexplorationHorizon_pos).symm.le
  have hprefixRegret_meas : Measurable prefixRegret :=
    ETC.measurable_explorationArgmaxPrefixRegretReal
      spec model explorationLast r
  have hregret_meas : Measurable regret := by
    have hfactor : regret = prefixRegret ∘ prefixMap := by
      funext trajectory
      exact
        (ETC.explorationArgmaxPrefixRegretReal_finiteRewardHistoryOfTrace_generated
          spec model trajectory explorationLast r hexplorationPulls_pos
          hexplorationHorizon_le).symm
    rw [hfactor]
    exact hprefixRegret_meas.comp hprefix_meas
  have hmapIntegral : integral externalLaw regret =
      integral mu (fun omega => regret (reward omega)) := by
    exact integral_map hreward_meas.aemeasurable
      hregret_meas.aestronglyMeasurable
  rw [hmapIntegral] at hbound_external
  exact hbound_external

/--
External-process canonical per-arm ETC expected regret from initial and
successor conditional reward laws.

The conditional laws are needed only through the exploration prefix. They
identify the reward-trace prefix pushforward with the canonical trajectory;
the per-arm prefix transport then preserves each gap-weighted pairwise tail
without a wrong-event union.
-/
theorem integral_real_pseudoRegret_explorationArgmaxGeneratedAction_reward_le_canonicalBoundedArmPerArmIntegralRegretBoundReal_of_initial_map_eq_condDistrib
    {Omega : Type*} {K : Nat} {Context : Type}
    [MeasurableSpace Omega] [MeasurableSpace Context]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (lo hi : Real)
    (hmeas : forall arm, AEMeasurable
      (fun reward : Rat => (((reward : Rat) : Real))) (armLaw arm))
    (hbound : forall arm, Filter.Eventually
      (fun reward : Rat => Set.Icc lo hi (((reward : Rat) : Real)))
      (ae (armLaw arm)))
    (hmean : forall arm, integral (armLaw arm)
      (fun reward : Rat => (((reward : Rat) : Real))) =
        (((model.mean arm : Rat) : Real)))
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (hcontext : forall n : Nat, Measurable (context n))
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    (r : Nat)
    (hzero : Measure.map (fun omega : Omega => reward omega 0) mu =
      armLaw (ETC.exploreArm spec 0))
    (hcond :
      let rewardKernel := RewardKernel.contextIndependentOfActionLaws
        (Context := Context) armLaw hprob
      let policy := fun t => ETC.explorationArgmaxHistoryPolicy spec model t
      let state := fun t history => ETC.explorationArgmaxHistoryState t history
      let stepKernel :=
        RewardKernel.historyStepKernelFamily rewardKernel policy context state
          hcontext (fun t => ETC.measurable_explorationArgmaxHistoryState t)
      let explorationLast := spec.explorationPulls * K - 1
      forall i : Nat, i < explorationLast ->
        ProbabilityTheory.condDistrib
            (fun omega : Omega => reward omega (i + 1))
            (fun omega : Omega =>
              History.finiteRewardHistoryOfTrace (reward omega) i)
            mu =ᵐ[
              mu.map (fun omega : Omega =>
                History.finiteRewardHistoryOfTrace (reward omega) i)]
          stepKernel i) :
    integral mu
      (fun omega : Omega =>
        (((pseudoRegret model
            (ETC.explorationArgmaxGeneratedAction spec model (reward omega))
            (spec.explorationPulls * K + r) : Rat) : Real))) <=
      ETC.canonicalBoundedArmPerArmIntegralRegretBoundReal
        spec model r lo hi := by
  let defaultAction := ETC.exploreArm spec 0
  let rewardKernel := RewardKernel.contextIndependentOfActionLaws
    (Context := Context) armLaw hprob
  let policy := fun t => ETC.explorationArgmaxHistoryPolicy spec model t
  let state := fun t history => ETC.explorationArgmaxHistoryState t history
  let stepKernel :=
    RewardKernel.historyStepKernelFamily rewardKernel policy context state
      hcontext (fun t => ETC.measurable_explorationArgmaxHistoryState t)
  letI : IsProbabilityMeasure (armLaw defaultAction) := hprob defaultAction
  let trajMeasure := ProbabilityTheory.Kernel.trajMeasure
    (X := fun _ : Nat => Rat) (armLaw defaultAction) stepKernel
  let explorationLast := spec.explorationPulls * K - 1
  let externalLaw := Measure.map reward mu
  have hreward_meas : Measurable reward := measurable_pi_lambda _ hreward
  letI : IsProbabilityMeasure externalLaw :=
    Measure.isProbabilityMeasure_map hreward_meas.aemeasurable
  let prefixMap :
      RewardTrace Rat -> History.FiniteRewardHistory Rat explorationLast :=
    fun trajectory =>
      History.finiteRewardHistoryOfTrace trajectory explorationLast
  have hprefix_meas : Measurable prefixMap :=
    History.measurable_finiteRewardHistoryOfTrace
      (fun trajectory : RewardTrace Rat => trajectory)
      (fun t => measurable_pi_apply t) explorationLast
  have hprefix_external :
      Measure.map prefixMap externalLaw = Measure.map prefixMap trajMeasure := by
    change Measure.map prefixMap (Measure.map reward mu) = _
    rw [Measure.map_map hprefix_meas hreward_meas]
    exact RewardKernel.rewardTrace_prefix_map_eq_trajMeasure_of_condDistrib
      mu (armLaw defaultAction) reward hreward stepKernel hzero explorationLast hcond
  have hbound_external :=
    ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_le_canonicalBoundedArmPerArmIntegralRegretBoundReal_of_explorationPrefix_map_eq
      externalLaw spec model armLaw hprob lo hi hmeas hbound hmean
      context hcontext hexplorationPulls_pos r hprefix_external
  let regret : RewardTrace Rat -> Real :=
    fun trajectory =>
      (((pseudoRegret model
          (ETC.explorationArgmaxGeneratedAction spec model trajectory)
          (spec.explorationPulls * K + r) : Rat) : Real))
  let prefixRegret : History.FiniteRewardHistory Rat explorationLast -> Real :=
    ETC.explorationArgmaxPrefixRegretReal spec model explorationLast r
  have hexplorationHorizon_pos : 0 < spec.explorationPulls * K :=
    Nat.mul_pos hexplorationPulls_pos model.hK
  have hexplorationHorizon_le :
      spec.explorationPulls * K <= explorationLast + 1 := by
    simpa [explorationLast] using
      (Nat.succ_pred_eq_of_pos hexplorationHorizon_pos).symm.le
  have hprefixRegret_meas : Measurable prefixRegret :=
    ETC.measurable_explorationArgmaxPrefixRegretReal
      spec model explorationLast r
  have hregret_meas : Measurable regret := by
    have hfactor : regret = prefixRegret ∘ prefixMap := by
      funext trajectory
      exact
        (ETC.explorationArgmaxPrefixRegretReal_finiteRewardHistoryOfTrace_generated
          spec model trajectory explorationLast r hexplorationPulls_pos
          hexplorationHorizon_le).symm
    rw [hfactor]
    exact hprefixRegret_meas.comp hprefix_meas
  have hmapIntegral : integral externalLaw regret =
      integral mu (fun omega => regret (reward omega)) := by
    exact integral_map hreward_meas.aemeasurable
      hregret_meas.aestronglyMeasurable
  rw [hmapIntegral] at hbound_external
  exact hbound_external

/--
External-process common-sub-Gaussian per-arm ETC expected regret from an
initial reward marginal and successor conditional reward laws.

The conditional laws are required only through exploration. They identify the
external reward-prefix law with the canonical trajectory and then invoke the
direct-MGF prefix transport theorem.
-/
theorem integral_real_pseudoRegret_explorationArgmaxGeneratedAction_reward_le_canonicalSubGaussianArmPerArmIntegralRegretBoundReal_of_initial_map_eq_condDistrib
    {Omega : Type*} {K : Nat} {Context : Type}
    [MeasurableSpace Omega] [MeasurableSpace Context]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (sigma2 : NNReal)
    (hmean : forall arm, integral (armLaw arm)
      (fun reward : Rat => (((reward : Rat) : Real))) =
        (((model.mean arm : Rat) : Real)))
    (hsubG : forall arm, ProbabilityTheory.HasSubgaussianMGF
      (fun reward : Rat =>
        ((reward : Rat) : Real) - (((model.mean arm : Rat) : Real)))
      sigma2 (armLaw arm))
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (hcontext : forall n : Nat, Measurable (context n))
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    (r : Nat)
    (hzero : Measure.map (fun omega : Omega => reward omega 0) mu =
      armLaw (ETC.exploreArm spec 0))
    (hcond :
      let rewardKernel := RewardKernel.contextIndependentOfActionLaws
        (Context := Context) armLaw hprob
      let policy := fun t => ETC.explorationArgmaxHistoryPolicy spec model t
      let state := fun t history => ETC.explorationArgmaxHistoryState t history
      let stepKernel :=
        RewardKernel.historyStepKernelFamily rewardKernel policy context state
          hcontext (fun t => ETC.measurable_explorationArgmaxHistoryState t)
      let explorationLast := spec.explorationPulls * K - 1
      forall i : Nat, i < explorationLast ->
        ProbabilityTheory.condDistrib
            (fun omega : Omega => reward omega (i + 1))
            (fun omega : Omega =>
              History.finiteRewardHistoryOfTrace (reward omega) i)
            mu =ᵐ[
              mu.map (fun omega : Omega =>
                History.finiteRewardHistoryOfTrace (reward omega) i)]
          stepKernel i) :
    integral mu
      (fun omega : Omega =>
        (((pseudoRegret model
            (ETC.explorationArgmaxGeneratedAction spec model (reward omega))
            (spec.explorationPulls * K + r) : Rat) : Real))) <=
      ETC.canonicalSubGaussianArmPerArmIntegralRegretBoundReal
        spec model r sigma2 := by
  let defaultAction := ETC.exploreArm spec 0
  let rewardKernel := RewardKernel.contextIndependentOfActionLaws
    (Context := Context) armLaw hprob
  let policy := fun t => ETC.explorationArgmaxHistoryPolicy spec model t
  let state := fun t history => ETC.explorationArgmaxHistoryState t history
  let stepKernel :=
    RewardKernel.historyStepKernelFamily rewardKernel policy context state
      hcontext (fun t => ETC.measurable_explorationArgmaxHistoryState t)
  letI : IsProbabilityMeasure (armLaw defaultAction) := hprob defaultAction
  let trajMeasure := ProbabilityTheory.Kernel.trajMeasure
    (X := fun _ : Nat => Rat) (armLaw defaultAction) stepKernel
  let explorationLast := spec.explorationPulls * K - 1
  let externalLaw := Measure.map reward mu
  have hreward_meas : Measurable reward := measurable_pi_lambda _ hreward
  letI : IsProbabilityMeasure externalLaw :=
    Measure.isProbabilityMeasure_map hreward_meas.aemeasurable
  let prefixMap :
      RewardTrace Rat -> History.FiniteRewardHistory Rat explorationLast :=
    fun trajectory =>
      History.finiteRewardHistoryOfTrace trajectory explorationLast
  have hprefix_meas : Measurable prefixMap :=
    History.measurable_finiteRewardHistoryOfTrace
      (fun trajectory : RewardTrace Rat => trajectory)
      (fun t => measurable_pi_apply t) explorationLast
  have hprefix_external :
      Measure.map prefixMap externalLaw = Measure.map prefixMap trajMeasure := by
    change Measure.map prefixMap (Measure.map reward mu) = _
    rw [Measure.map_map hprefix_meas hreward_meas]
    exact RewardKernel.rewardTrace_prefix_map_eq_trajMeasure_of_condDistrib
      mu (armLaw defaultAction) reward hreward stepKernel hzero explorationLast hcond
  have hbound_external :=
    ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_le_canonicalSubGaussianArmPerArmIntegralRegretBoundReal_of_explorationPrefix_map_eq
      externalLaw spec model armLaw hprob sigma2 hmean hsubG
      context hcontext hexplorationPulls_pos r hprefix_external
  let regret : RewardTrace Rat -> Real :=
    fun trajectory =>
      (((pseudoRegret model
          (ETC.explorationArgmaxGeneratedAction spec model trajectory)
          (spec.explorationPulls * K + r) : Rat) : Real))
  let prefixRegret : History.FiniteRewardHistory Rat explorationLast -> Real :=
    ETC.explorationArgmaxPrefixRegretReal spec model explorationLast r
  have hexplorationHorizon_pos : 0 < spec.explorationPulls * K :=
    Nat.mul_pos hexplorationPulls_pos model.hK
  have hexplorationHorizon_le :
      spec.explorationPulls * K <= explorationLast + 1 := by
    simpa [explorationLast] using
      (Nat.succ_pred_eq_of_pos hexplorationHorizon_pos).symm.le
  have hprefixRegret_meas : Measurable prefixRegret :=
    ETC.measurable_explorationArgmaxPrefixRegretReal
      spec model explorationLast r
  have hregret_meas : Measurable regret := by
    have hfactor : regret = prefixRegret ∘ prefixMap := by
      funext trajectory
      exact
        (ETC.explorationArgmaxPrefixRegretReal_finiteRewardHistoryOfTrace_generated
          spec model trajectory explorationLast r hexplorationPulls_pos
          hexplorationHorizon_le).symm
    rw [hfactor]
    exact hprefixRegret_meas.comp hprefix_meas
  have hmapIntegral : integral externalLaw regret =
      integral mu (fun omega => regret (reward omega)) := by
    exact integral_map hreward_meas.aemeasurable
      hregret_meas.aestronglyMeasurable
  rw [hmapIntegral] at hbound_external
  exact hbound_external

/--
During exploration, the generated-history ETC step kernel is exactly the law
of the arm scheduled at time `i + 1`.

The context disappears because `contextIndependentOfActionLaws` selects only
the policy action, and the history state disappears because the exploration
branch of the policy is deterministic.
-/
theorem explorationArgmaxHistory_stepKernel_apply_eq_exploreArmLaw_of_lt
    {K : Nat} {Context : Type}
    [MeasurableSpace Context]
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (hcontext : forall n : Nat, Measurable (context n))
    (i : Nat) (hi : i + 1 < spec.explorationPulls * K)
    (history : (j : Finset.Iic i) -> Rat) :
    RewardKernel.historyStepKernelFamily
        (RewardKernel.contextIndependentOfActionLaws
          (Context := Context) armLaw hprob)
        (fun t => ETC.explorationArgmaxHistoryPolicy spec model t)
        context
        (fun t history => ETC.explorationArgmaxHistoryState t history)
        hcontext (fun t => ETC.measurable_explorationArgmaxHistoryState t)
        i history =
      armLaw (ETC.exploreArm spec (i + 1)) := by
  simp [RewardKernel.historyStepKernelFamily_apply,
    ETC.explorationArgmaxHistoryPolicy, hi]

/--
Practical external-process ETC expected regret from the conditional laws of
the scheduled exploration arms.

Unlike the preceding theorem, callers do not mention the local
`historyStepKernelFamily`. They provide the initial arm law and, before the end
of exploration, the conditional law of reward `i + 1` as the stationary law
of `exploreArm spec (i + 1)`. The exploration step-kernel equality above turns
that environment-facing contract into the canonical conditional-law contract.
-/
theorem integral_real_pseudoRegret_explorationArgmaxGeneratedAction_reward_le_canonicalBoundedArmMaxGapIntegralRegretBoundReal_of_initial_map_eq_explorationArm_condDistrib
    {Omega : Type*} {K : Nat}
    [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (lo hi : Real)
    (hmeas : forall arm, AEMeasurable
      (fun reward : Rat => (((reward : Rat) : Real))) (armLaw arm))
    (hbound : forall arm, Filter.Eventually
      (fun reward : Rat => Set.Icc lo hi (((reward : Rat) : Real)))
      (ae (armLaw arm)))
    (hmean : forall arm, integral (armLaw arm)
      (fun reward : Rat => (((reward : Rat) : Real))) =
        (((model.mean arm : Rat) : Real)))
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    (r : Nat)
    (hzero : Measure.map (fun omega : Omega => reward omega 0) mu =
      armLaw (ETC.exploreArm spec 0))
    (hcond : forall i : Nat, i < spec.explorationPulls * K - 1 ->
      ProbabilityTheory.condDistrib
          (fun omega : Omega => reward omega (i + 1))
          (fun omega : Omega =>
            History.finiteRewardHistoryOfTrace (reward omega) i)
          mu =ᵐ[
            mu.map (fun omega : Omega =>
              History.finiteRewardHistoryOfTrace (reward omega) i)]
        fun _history => armLaw (ETC.exploreArm spec (i + 1))) :
    integral mu
      (fun omega : Omega =>
        (((pseudoRegret model
            (ETC.explorationArgmaxGeneratedAction spec model (reward omega))
            (spec.explorationPulls * K + r) : Rat) : Real))) <=
      ETC.canonicalBoundedArmMaxGapIntegralRegretBoundReal
        spec model r lo hi := by
  apply
    ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_reward_le_canonicalBoundedArmMaxGapIntegralRegretBoundReal_of_initial_map_eq_condDistrib
      (Context := Unit)
      mu reward hreward spec model armLaw hprob lo hi hmeas hbound hmean
      (fun _n _history => ()) (fun _n => measurable_const)
      hexplorationPulls_pos r hzero
  dsimp
  intro i hi
  have hphase : i + 1 < spec.explorationPulls * K := by omega
  filter_upwards [hcond i hi] with history hlaw
  exact hlaw.trans
    (ETC.explorationArgmaxHistory_stepKernel_apply_eq_exploreArmLaw_of_lt
      (Context := Unit) spec model armLaw hprob
      (fun _n _history => ()) (fun _n => measurable_const)
      i hphase history).symm

/--
Practical external-process per-arm ETC expected regret from the conditional
laws of the scheduled exploration arms.

The step-kernel equality above converts the environment-facing scheduled-arm
laws into the canonical conditional-law contract. The per-arm consumer then
keeps the gap-weighted pairwise tails separate, without a wrong-event union.
-/
theorem integral_real_pseudoRegret_explorationArgmaxGeneratedAction_reward_le_canonicalBoundedArmPerArmIntegralRegretBoundReal_of_initial_map_eq_explorationArm_condDistrib
    {Omega : Type*} {K : Nat}
    [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (lo hi : Real)
    (hmeas : forall arm, AEMeasurable
      (fun reward : Rat => (((reward : Rat) : Real))) (armLaw arm))
    (hbound : forall arm, Filter.Eventually
      (fun reward : Rat => Set.Icc lo hi (((reward : Rat) : Real)))
      (ae (armLaw arm)))
    (hmean : forall arm, integral (armLaw arm)
      (fun reward : Rat => (((reward : Rat) : Real))) =
        (((model.mean arm : Rat) : Real)))
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    (r : Nat)
    (hzero : Measure.map (fun omega : Omega => reward omega 0) mu =
      armLaw (ETC.exploreArm spec 0))
    (hcond : forall i : Nat, i < spec.explorationPulls * K - 1 ->
      ProbabilityTheory.condDistrib
          (fun omega : Omega => reward omega (i + 1))
          (fun omega : Omega =>
            History.finiteRewardHistoryOfTrace (reward omega) i)
          mu =ᵐ[
            mu.map (fun omega : Omega =>
              History.finiteRewardHistoryOfTrace (reward omega) i)]
        fun _history => armLaw (ETC.exploreArm spec (i + 1))) :
    integral mu
      (fun omega : Omega =>
        (((pseudoRegret model
            (ETC.explorationArgmaxGeneratedAction spec model (reward omega))
            (spec.explorationPulls * K + r) : Rat) : Real))) <=
      ETC.canonicalBoundedArmPerArmIntegralRegretBoundReal
        spec model r lo hi := by
  apply
    ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_reward_le_canonicalBoundedArmPerArmIntegralRegretBoundReal_of_initial_map_eq_condDistrib
      (Context := Unit)
      mu reward hreward spec model armLaw hprob lo hi hmeas hbound hmean
      (fun _n _history => ()) (fun _n => measurable_const)
      hexplorationPulls_pos r hzero
  dsimp
  intro i hi
  have hphase : i + 1 < spec.explorationPulls * K := by omega
  filter_upwards [hcond i hi] with history hlaw
  exact hlaw.trans
    (ETC.explorationArgmaxHistory_stepKernel_apply_eq_exploreArmLaw_of_lt
      (Context := Unit) spec model armLaw hprob
      (fun _n _history => ()) (fun _n => measurable_const)
      i hphase history).symm

/--
Practical external-process common-sub-Gaussian per-arm ETC expected regret
from the conditional laws of the scheduled exploration arms.

The public contract exposes no local context, policy state, reward kernel, or
trajectory measure. It preserves the canonical direct-MGF gap-weighted armwise
budget and requires no bounded support or arm union.
-/
theorem integral_real_pseudoRegret_explorationArgmaxGeneratedAction_reward_le_canonicalSubGaussianArmPerArmIntegralRegretBoundReal_of_initial_map_eq_explorationArm_condDistrib
    {Omega : Type*} {K : Nat}
    [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (sigma2 : NNReal)
    (hmean : forall arm, integral (armLaw arm)
      (fun reward : Rat => (((reward : Rat) : Real))) =
        (((model.mean arm : Rat) : Real)))
    (hsubG : forall arm, ProbabilityTheory.HasSubgaussianMGF
      (fun reward : Rat =>
        ((reward : Rat) : Real) - (((model.mean arm : Rat) : Real)))
      sigma2 (armLaw arm))
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    (r : Nat)
    (hzero : Measure.map (fun omega : Omega => reward omega 0) mu =
      armLaw (ETC.exploreArm spec 0))
    (hcond : forall i : Nat, i < spec.explorationPulls * K - 1 ->
      ProbabilityTheory.condDistrib
          (fun omega : Omega => reward omega (i + 1))
          (fun omega : Omega =>
            History.finiteRewardHistoryOfTrace (reward omega) i)
          mu =ᵐ[
            mu.map (fun omega : Omega =>
              History.finiteRewardHistoryOfTrace (reward omega) i)]
        fun _history => armLaw (ETC.exploreArm spec (i + 1))) :
    integral mu
      (fun omega : Omega =>
        (((pseudoRegret model
            (ETC.explorationArgmaxGeneratedAction spec model (reward omega))
            (spec.explorationPulls * K + r) : Rat) : Real))) <=
      ETC.canonicalSubGaussianArmPerArmIntegralRegretBoundReal
        spec model r sigma2 := by
  apply
    ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_reward_le_canonicalSubGaussianArmPerArmIntegralRegretBoundReal_of_initial_map_eq_condDistrib
      (Context := Unit)
      mu reward hreward spec model armLaw hprob sigma2 hmean hsubG
      (fun _n _history => ()) (fun _n => measurable_const)
      hexplorationPulls_pos r hzero
  dsimp
  intro i hi
  have hphase : i + 1 < spec.explorationPulls * K := by omega
  filter_upwards [hcond i hi] with history hlaw
  exact hlaw.trans
    (ETC.explorationArgmaxHistory_stepKernel_apply_eq_exploreArmLaw_of_lt
      (Context := Unit) spec model armLaw hprob
      (fun _n _history => ()) (fun _n => measurable_const)
      i hphase history).symm

/--
External ETC expected regret from LML-shaped action/reward-history conditional
laws during exploration.

The initial reward law is supplied conditionally on the first action. Each
successor reward has the scheduled exploration-arm law conditionally on the
complete action/reward prefix together with the next action. Since those laws
are constant, `RewardKernel.condDistrib_ae_eq_const_of_comp` projects them to
the reward-only prefixes consumed by the preceding environment-facing theorem.
-/
theorem integral_real_pseudoRegret_explorationArgmaxGeneratedAction_reward_le_canonicalBoundedArmMaxGapIntegralRegretBoundReal_of_actionRewardHistory_explorationArm_condDistrib
    {Omega : Type*} {K : Nat}
    [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (action : Omega -> ActionTrace (Fin K))
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (lo hi : Real)
    (hmeas : forall arm, AEMeasurable
      (fun reward : Rat => (((reward : Rat) : Real))) (armLaw arm))
    (hbound : forall arm, Filter.Eventually
      (fun reward : Rat => Set.Icc lo hi (((reward : Rat) : Real)))
      (ae (armLaw arm)))
    (hmean : forall arm, integral (armLaw arm)
      (fun reward : Rat => (((reward : Rat) : Real))) =
        (((model.mean arm : Rat) : Real)))
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    (r : Nat)
    (hzero : ProbabilityTheory.condDistrib
        (fun omega : Omega => reward omega 0)
        (fun omega : Omega => action omega 0) mu =ᵐ[
          mu.map (fun omega : Omega => action omega 0)]
      ProbabilityTheory.Kernel.const (Fin K)
        (armLaw (ETC.exploreArm spec 0)))
    (hcond : forall i : Nat, i < spec.explorationPulls * K - 1 ->
      let fullCondition := fun omega : Omega =>
        (History.finitePairHistoryOfTrace
            (action omega) (reward omega) i,
          action omega (i + 1))
      ProbabilityTheory.condDistrib
          (fun omega : Omega => reward omega (i + 1))
          fullCondition mu =ᵐ[mu.map fullCondition]
        ProbabilityTheory.Kernel.const
          (History.FinitePairHistory (Fin K) Rat i × Fin K)
          (armLaw (ETC.exploreArm spec (i + 1)))) :
    integral mu
      (fun omega : Omega =>
        (((pseudoRegret model
            (ETC.explorationArgmaxGeneratedAction spec model (reward omega))
            (spec.explorationPulls * K + r) : Rat) : Real))) <=
      ETC.canonicalBoundedArmMaxGapIntegralRegretBoundReal
        spec model r lo hi := by
  apply
    ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_reward_le_canonicalBoundedArmMaxGapIntegralRegretBoundReal_of_initial_map_eq_explorationArm_condDistrib
      mu reward hreward spec model armLaw hprob lo hi hmeas hbound hmean
      hexplorationPulls_pos r
  · exact RewardKernel.map_eq_of_condDistrib_ae_eq_const
      mu (fun omega : Omega => action omega 0) (haction 0)
      (fun omega : Omega => reward omega 0) (hreward 0)
      (armLaw (ETC.exploreArm spec 0)) hzero
  · intro i hi
    let fine : Omega ->
        History.FinitePairHistory (Fin K) Rat i × Fin K :=
      fun omega =>
        (History.finitePairHistoryOfTrace
            (action omega) (reward omega) i,
          action omega (i + 1))
    let coarse : Omega -> History.FiniteRewardHistory Rat i :=
      fun omega => History.finiteRewardHistoryOfTrace (reward omega) i
    let project :
        History.FinitePairHistory (Fin K) Rat i × Fin K ->
          History.FiniteRewardHistory Rat i :=
      fun value => History.pairHistoryRewardProjection value.1
    have hfine : Measurable fine :=
      (History.measurable_finitePairHistoryOfTrace
        action reward haction hreward i).prod (haction (i + 1))
    have hproject : Measurable project :=
      (History.measurable_pairHistoryRewardProjection
        (Action := Fin K) (Reward := Rat) i).comp measurable_fst
    have hcomp : coarse = project ∘ fine := by
      rfl
    have hcoarsened := RewardKernel.condDistrib_ae_eq_const_of_comp
      mu fine hfine coarse
      (fun omega : Omega => reward omega (i + 1)) (hreward (i + 1))
      project hproject hcomp
      (armLaw (ETC.exploreArm spec (i + 1))) (hcond i hi)
    simpa [coarse, ProbabilityTheory.Kernel.const_apply] using hcoarsened

/--
External per-arm ETC expected regret from LML-shaped action/reward-history
conditional laws during exploration.

Constant scheduled-arm laws conditioned on the complete action/reward prefix
and next action coarsen to reward-only prefixes. The scheduled-arm per-arm
consumer then preserves the gap-weighted armwise tails without a wrong-event
union.
-/
theorem integral_real_pseudoRegret_explorationArgmaxGeneratedAction_reward_le_canonicalBoundedArmPerArmIntegralRegretBoundReal_of_actionRewardHistory_explorationArm_condDistrib
    {Omega : Type*} {K : Nat}
    [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (action : Omega -> ActionTrace (Fin K))
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (lo hi : Real)
    (hmeas : forall arm, AEMeasurable
      (fun reward : Rat => (((reward : Rat) : Real))) (armLaw arm))
    (hbound : forall arm, Filter.Eventually
      (fun reward : Rat => Set.Icc lo hi (((reward : Rat) : Real)))
      (ae (armLaw arm)))
    (hmean : forall arm, integral (armLaw arm)
      (fun reward : Rat => (((reward : Rat) : Real))) =
        (((model.mean arm : Rat) : Real)))
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    (r : Nat)
    (hzero : ProbabilityTheory.condDistrib
        (fun omega : Omega => reward omega 0)
        (fun omega : Omega => action omega 0) mu =ᵐ[
          mu.map (fun omega : Omega => action omega 0)]
      ProbabilityTheory.Kernel.const (Fin K)
        (armLaw (ETC.exploreArm spec 0)))
    (hcond : forall i : Nat, i < spec.explorationPulls * K - 1 ->
      let fullCondition := fun omega : Omega =>
        (History.finitePairHistoryOfTrace
            (action omega) (reward omega) i,
          action omega (i + 1))
      ProbabilityTheory.condDistrib
          (fun omega : Omega => reward omega (i + 1))
          fullCondition mu =ᵐ[mu.map fullCondition]
        ProbabilityTheory.Kernel.const
          (History.FinitePairHistory (Fin K) Rat i × Fin K)
          (armLaw (ETC.exploreArm spec (i + 1)))) :
    integral mu
      (fun omega : Omega =>
        (((pseudoRegret model
            (ETC.explorationArgmaxGeneratedAction spec model (reward omega))
            (spec.explorationPulls * K + r) : Rat) : Real))) <=
      ETC.canonicalBoundedArmPerArmIntegralRegretBoundReal
        spec model r lo hi := by
  apply
    ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_reward_le_canonicalBoundedArmPerArmIntegralRegretBoundReal_of_initial_map_eq_explorationArm_condDistrib
      mu reward hreward spec model armLaw hprob lo hi hmeas hbound hmean
      hexplorationPulls_pos r
  · exact RewardKernel.map_eq_of_condDistrib_ae_eq_const
      mu (fun omega : Omega => action omega 0) (haction 0)
      (fun omega : Omega => reward omega 0) (hreward 0)
      (armLaw (ETC.exploreArm spec 0)) hzero
  · intro i hi
    let fine : Omega ->
        History.FinitePairHistory (Fin K) Rat i × Fin K :=
      fun omega =>
        (History.finitePairHistoryOfTrace
            (action omega) (reward omega) i,
          action omega (i + 1))
    let coarse : Omega -> History.FiniteRewardHistory Rat i :=
      fun omega => History.finiteRewardHistoryOfTrace (reward omega) i
    let project :
        History.FinitePairHistory (Fin K) Rat i × Fin K ->
          History.FiniteRewardHistory Rat i :=
      fun value => History.pairHistoryRewardProjection value.1
    have hfine : Measurable fine :=
      (History.measurable_finitePairHistoryOfTrace
        action reward haction hreward i).prod (haction (i + 1))
    have hproject : Measurable project :=
      (History.measurable_pairHistoryRewardProjection
        (Action := Fin K) (Reward := Rat) i).comp measurable_fst
    have hcomp : coarse = project ∘ fine := by
      rfl
    have hcoarsened := RewardKernel.condDistrib_ae_eq_const_of_comp
      mu fine hfine coarse
      (fun omega : Omega => reward omega (i + 1)) (hreward (i + 1))
      project hproject hcomp
      (armLaw (ETC.exploreArm spec (i + 1))) (hcond i hi)
    simpa [coarse, ProbabilityTheory.Kernel.const_apply] using hcoarsened

/--
External direct-MGF per-arm ETC expected regret from LML-shaped
action/reward-history conditional laws during exploration.

The initial constant conditional reward law yields the time-zero marginal.
Each successor constant scheduled-arm law is coarsened from the complete
action/reward prefix and next action to the reward-only prefix, then the
external scheduled-arm direct-MGF theorem preserves the gap-weighted armwise
budget without bounded support or an arm union.
-/
theorem integral_real_pseudoRegret_explorationArgmaxGeneratedAction_reward_le_canonicalSubGaussianArmPerArmIntegralRegretBoundReal_of_actionRewardHistory_explorationArm_condDistrib
    {Omega : Type*} {K : Nat}
    [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (action : Omega -> ActionTrace (Fin K))
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (sigma2 : NNReal)
    (hmean : forall arm, integral (armLaw arm)
      (fun reward : Rat => (((reward : Rat) : Real))) =
        (((model.mean arm : Rat) : Real)))
    (hsubG : forall arm, ProbabilityTheory.HasSubgaussianMGF
      (fun reward : Rat =>
        ((reward : Rat) : Real) - (((model.mean arm : Rat) : Real)))
      sigma2 (armLaw arm))
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    (r : Nat)
    (hzero : ProbabilityTheory.condDistrib
        (fun omega : Omega => reward omega 0)
        (fun omega : Omega => action omega 0) mu =ᵐ[
          mu.map (fun omega : Omega => action omega 0)]
      ProbabilityTheory.Kernel.const (Fin K)
        (armLaw (ETC.exploreArm spec 0)))
    (hcond : forall i : Nat, i < spec.explorationPulls * K - 1 ->
      let fullCondition := fun omega : Omega =>
        (History.finitePairHistoryOfTrace
            (action omega) (reward omega) i,
          action omega (i + 1))
      ProbabilityTheory.condDistrib
          (fun omega : Omega => reward omega (i + 1))
          fullCondition mu =ᵐ[mu.map fullCondition]
        ProbabilityTheory.Kernel.const
          (History.FinitePairHistory (Fin K) Rat i × Fin K)
          (armLaw (ETC.exploreArm spec (i + 1)))) :
    integral mu
      (fun omega : Omega =>
        (((pseudoRegret model
            (ETC.explorationArgmaxGeneratedAction spec model (reward omega))
            (spec.explorationPulls * K + r) : Rat) : Real))) <=
      ETC.canonicalSubGaussianArmPerArmIntegralRegretBoundReal
        spec model r sigma2 := by
  apply
    ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_reward_le_canonicalSubGaussianArmPerArmIntegralRegretBoundReal_of_initial_map_eq_explorationArm_condDistrib
      mu reward hreward spec model armLaw hprob sigma2 hmean hsubG
      hexplorationPulls_pos r
  · exact RewardKernel.map_eq_of_condDistrib_ae_eq_const
      mu (fun omega : Omega => action omega 0) (haction 0)
      (fun omega : Omega => reward omega 0) (hreward 0)
      (armLaw (ETC.exploreArm spec 0)) hzero
  · intro i hi
    let fine : Omega ->
        History.FinitePairHistory (Fin K) Rat i × Fin K :=
      fun omega =>
        (History.finitePairHistoryOfTrace
            (action omega) (reward omega) i,
          action omega (i + 1))
    let coarse : Omega -> History.FiniteRewardHistory Rat i :=
      fun omega => History.finiteRewardHistoryOfTrace (reward omega) i
    let project :
        History.FinitePairHistory (Fin K) Rat i × Fin K ->
          History.FiniteRewardHistory Rat i :=
      fun value => History.pairHistoryRewardProjection value.1
    have hfine : Measurable fine :=
      (History.measurable_finitePairHistoryOfTrace
        action reward haction hreward i).prod (haction (i + 1))
    have hproject : Measurable project :=
      (History.measurable_pairHistoryRewardProjection
        (Action := Fin K) (Reward := Rat) i).comp measurable_fst
    have hcomp : coarse = project ∘ fine := by
      rfl
    have hcoarsened := RewardKernel.condDistrib_ae_eq_const_of_comp
      mu fine hfine coarse
      (fun omega : Omega => reward omega (i + 1)) (hreward (i + 1))
      project hproject hcomp
      (armLaw (ETC.exploreArm spec (i + 1))) (hcond i hi)
    simpa [coarse, ProbabilityTheory.Kernel.const_apply] using hcoarsened

/--
External bounded ETC regret from action-dependent stationary feedback kernels
and almost-sure exploration action identities.

This is the dependency-light local analogue of the law transport exposed by
the exact-seed LML `IsAlgEnvSeq` fields: the initial feedback kernel is indexed
by action zero, each later kernel is indexed by the next action in the complete
history condition, and the exploration action identities make those selectors
almost surely equal to the scheduled round-robin arms.
-/
theorem integral_real_pseudoRegret_explorationArgmaxGeneratedAction_reward_le_canonicalBoundedArmMaxGapIntegralRegretBoundReal_of_actionDependent_actionRewardHistory_condDistrib
    {Omega : Type*} {K : Nat}
    [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (action : Omega -> ActionTrace (Fin K))
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (lo hi : Real)
    (hmeas : forall arm, AEMeasurable
      (fun reward : Rat => (((reward : Rat) : Real))) (armLaw arm))
    (hbound : forall arm, Filter.Eventually
      (fun reward : Rat => Set.Icc lo hi (((reward : Rat) : Real)))
      (ae (armLaw arm)))
    (hmean : forall arm, integral (armLaw arm)
      (fun reward : Rat => (((reward : Rat) : Real))) =
        (((model.mean arm : Rat) : Real)))
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    (r : Nat)
    (hactionZero :
      (fun omega : Omega => action omega 0) =ᵐ[mu]
        fun _omega => ETC.exploreArm spec 0)
    (hactionExplore : forall i : Nat,
      i < spec.explorationPulls * K - 1 ->
        (fun omega : Omega => action omega (i + 1)) =ᵐ[mu]
          fun _omega => ETC.exploreArm spec (i + 1))
    (hzero : ProbabilityTheory.condDistrib
        (fun omega : Omega => reward omega 0)
        (fun omega : Omega => action omega 0) mu =ᵐ[
          mu.map (fun omega : Omega => action omega 0)]
      ProbabilityTheory.Kernel.ofFunOfCountable armLaw)
    (hcond : forall i : Nat, i < spec.explorationPulls * K - 1 ->
      let fullCondition := fun omega : Omega =>
        (History.finitePairHistoryOfTrace
            (action omega) (reward omega) i,
          action omega (i + 1))
      ProbabilityTheory.condDistrib
          (fun omega : Omega => reward omega (i + 1))
          fullCondition mu =ᵐ[mu.map fullCondition]
        (RewardKernel.contextIndependentOfActionLaws
          (Context := History.FinitePairHistory (Fin K) Rat i)
          armLaw hprob).kernel) :
    integral mu
      (fun omega : Omega =>
        (((pseudoRegret model
            (ETC.explorationArgmaxGeneratedAction spec model (reward omega))
            (spec.explorationPulls * K + r) : Rat) : Real))) <=
      ETC.canonicalBoundedArmMaxGapIntegralRegretBoundReal
        spec model r lo hi := by
  apply
    ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_reward_le_canonicalBoundedArmMaxGapIntegralRegretBoundReal_of_actionRewardHistory_explorationArm_condDistrib
      mu action haction reward hreward spec model armLaw hprob lo hi hmeas
      hbound hmean hexplorationPulls_pos r
  · exact RewardKernel.condDistrib_ae_eq_const_of_ae_eq_selected
      mu (fun omega : Omega => action omega 0) (haction 0)
      (fun omega : Omega => reward omega 0)
      id measurable_id
      (ProbabilityTheory.Kernel.ofFunOfCountable armLaw)
      armLaw (ETC.exploreArm spec 0)
      (by simpa using hactionZero) (fun _value => rfl) hzero
  · intro i hi
    let fullCondition : Omega ->
        History.FinitePairHistory (Fin K) Rat i × Fin K :=
      fun omega =>
        (History.finitePairHistoryOfTrace
            (action omega) (reward omega) i,
          action omega (i + 1))
    have hfullCondition : Measurable fullCondition :=
      (History.measurable_finitePairHistoryOfTrace
        action reward haction hreward i).prod (haction (i + 1))
    exact RewardKernel.condDistrib_ae_eq_const_of_ae_eq_selected
      mu fullCondition hfullCondition
      (fun omega : Omega => reward omega (i + 1))
      Prod.snd measurable_snd
      (RewardKernel.contextIndependentOfActionLaws
        (Context := History.FinitePairHistory (Fin K) Rat i)
        armLaw hprob).kernel
      armLaw (ETC.exploreArm spec (i + 1))
      (by simpa [fullCondition] using hactionExplore i hi)
      (fun _value => rfl) (hcond i hi)

/--
External per-arm ETC regret from action-dependent stationary feedback kernels
and almost-sure exploration action identities.

The selector transport turns each action-indexed feedback kernel into the
constant law of the scheduled exploration arm. The full-history per-arm
consumer then preserves the gap-weighted armwise tails without a wrong-event
union.
-/
theorem integral_real_pseudoRegret_explorationArgmaxGeneratedAction_reward_le_canonicalBoundedArmPerArmIntegralRegretBoundReal_of_actionDependent_actionRewardHistory_condDistrib
    {Omega : Type*} {K : Nat}
    [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (action : Omega -> ActionTrace (Fin K))
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (lo hi : Real)
    (hmeas : forall arm, AEMeasurable
      (fun reward : Rat => (((reward : Rat) : Real))) (armLaw arm))
    (hbound : forall arm, Filter.Eventually
      (fun reward : Rat => Set.Icc lo hi (((reward : Rat) : Real)))
      (ae (armLaw arm)))
    (hmean : forall arm, integral (armLaw arm)
      (fun reward : Rat => (((reward : Rat) : Real))) =
        (((model.mean arm : Rat) : Real)))
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    (r : Nat)
    (hactionZero :
      (fun omega : Omega => action omega 0) =ᵐ[mu]
        fun _omega => ETC.exploreArm spec 0)
    (hactionExplore : forall i : Nat,
      i < spec.explorationPulls * K - 1 ->
        (fun omega : Omega => action omega (i + 1)) =ᵐ[mu]
          fun _omega => ETC.exploreArm spec (i + 1))
    (hzero : ProbabilityTheory.condDistrib
        (fun omega : Omega => reward omega 0)
        (fun omega : Omega => action omega 0) mu =ᵐ[
          mu.map (fun omega : Omega => action omega 0)]
      ProbabilityTheory.Kernel.ofFunOfCountable armLaw)
    (hcond : forall i : Nat, i < spec.explorationPulls * K - 1 ->
      let fullCondition := fun omega : Omega =>
        (History.finitePairHistoryOfTrace
            (action omega) (reward omega) i,
          action omega (i + 1))
      ProbabilityTheory.condDistrib
          (fun omega : Omega => reward omega (i + 1))
          fullCondition mu =ᵐ[mu.map fullCondition]
        (RewardKernel.contextIndependentOfActionLaws
          (Context := History.FinitePairHistory (Fin K) Rat i)
          armLaw hprob).kernel) :
    integral mu
      (fun omega : Omega =>
        (((pseudoRegret model
            (ETC.explorationArgmaxGeneratedAction spec model (reward omega))
            (spec.explorationPulls * K + r) : Rat) : Real))) <=
      ETC.canonicalBoundedArmPerArmIntegralRegretBoundReal
        spec model r lo hi := by
  apply
    ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_reward_le_canonicalBoundedArmPerArmIntegralRegretBoundReal_of_actionRewardHistory_explorationArm_condDistrib
      mu action haction reward hreward spec model armLaw hprob lo hi hmeas
      hbound hmean hexplorationPulls_pos r
  · exact RewardKernel.condDistrib_ae_eq_const_of_ae_eq_selected
      mu (fun omega : Omega => action omega 0) (haction 0)
      (fun omega : Omega => reward omega 0)
      id measurable_id
      (ProbabilityTheory.Kernel.ofFunOfCountable armLaw)
      armLaw (ETC.exploreArm spec 0)
      (by simpa using hactionZero) (fun _value => rfl) hzero
  · intro i hi
    let fullCondition : Omega ->
        History.FinitePairHistory (Fin K) Rat i × Fin K :=
      fun omega =>
        (History.finitePairHistoryOfTrace
            (action omega) (reward omega) i,
          action omega (i + 1))
    have hfullCondition : Measurable fullCondition :=
      (History.measurable_finitePairHistoryOfTrace
        action reward haction hreward i).prod (haction (i + 1))
    exact RewardKernel.condDistrib_ae_eq_const_of_ae_eq_selected
      mu fullCondition hfullCondition
      (fun omega : Omega => reward omega (i + 1))
      Prod.snd measurable_snd
      (RewardKernel.contextIndependentOfActionLaws
        (Context := History.FinitePairHistory (Fin K) Rat i)
        armLaw hprob).kernel
      armLaw (ETC.exploreArm spec (i + 1))
      (by simpa [fullCondition] using hactionExplore i hi)
      (fun _value => rfl) (hcond i hi)

/--
External direct-MGF per-arm ETC regret from action-dependent stationary
feedback kernels and almost-sure exploration action identities.

The selector transport converts the raw action-indexed initial and successor
feedback kernels into the constant laws of the scheduled exploration arms.
The full action/reward-history direct-MGF consumer then returns the same
gap-weighted armwise budget without bounded support or an arm union.
-/
theorem integral_real_pseudoRegret_explorationArgmaxGeneratedAction_reward_le_canonicalSubGaussianArmPerArmIntegralRegretBoundReal_of_actionDependent_actionRewardHistory_condDistrib
    {Omega : Type*} {K : Nat}
    [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (action : Omega -> ActionTrace (Fin K))
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (reward : Omega -> RewardTrace Rat)
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (spec : ETC.Spec K) (model : FiniteBanditModel K)
    (armLaw : Fin K -> Measure Rat)
    (hprob : forall arm, IsProbabilityMeasure (armLaw arm))
    (sigma2 : NNReal)
    (hmean : forall arm, integral (armLaw arm)
      (fun reward : Rat => (((reward : Rat) : Real))) =
        (((model.mean arm : Rat) : Real)))
    (hsubG : forall arm, ProbabilityTheory.HasSubgaussianMGF
      (fun reward : Rat =>
        ((reward : Rat) : Real) - (((model.mean arm : Rat) : Real)))
      sigma2 (armLaw arm))
    (hexplorationPulls_pos : 0 < spec.explorationPulls)
    (r : Nat)
    (hactionZero :
      (fun omega : Omega => action omega 0) =ᵐ[mu]
        fun _omega => ETC.exploreArm spec 0)
    (hactionExplore : forall i : Nat,
      i < spec.explorationPulls * K - 1 ->
        (fun omega : Omega => action omega (i + 1)) =ᵐ[mu]
          fun _omega => ETC.exploreArm spec (i + 1))
    (hzero : ProbabilityTheory.condDistrib
        (fun omega : Omega => reward omega 0)
        (fun omega : Omega => action omega 0) mu =ᵐ[
          mu.map (fun omega : Omega => action omega 0)]
      ProbabilityTheory.Kernel.ofFunOfCountable armLaw)
    (hcond : forall i : Nat, i < spec.explorationPulls * K - 1 ->
      let fullCondition := fun omega : Omega =>
        (History.finitePairHistoryOfTrace
            (action omega) (reward omega) i,
          action omega (i + 1))
      ProbabilityTheory.condDistrib
          (fun omega : Omega => reward omega (i + 1))
          fullCondition mu =ᵐ[mu.map fullCondition]
        (RewardKernel.contextIndependentOfActionLaws
          (Context := History.FinitePairHistory (Fin K) Rat i)
          armLaw hprob).kernel) :
    integral mu
      (fun omega : Omega =>
        (((pseudoRegret model
            (ETC.explorationArgmaxGeneratedAction spec model (reward omega))
            (spec.explorationPulls * K + r) : Rat) : Real))) <=
      ETC.canonicalSubGaussianArmPerArmIntegralRegretBoundReal
        spec model r sigma2 := by
  apply
    ETC.integral_real_pseudoRegret_explorationArgmaxGeneratedAction_reward_le_canonicalSubGaussianArmPerArmIntegralRegretBoundReal_of_actionRewardHistory_explorationArm_condDistrib
      mu action haction reward hreward spec model armLaw hprob sigma2 hmean
      hsubG hexplorationPulls_pos r
  · exact RewardKernel.condDistrib_ae_eq_const_of_ae_eq_selected
      mu (fun omega : Omega => action omega 0) (haction 0)
      (fun omega : Omega => reward omega 0)
      id measurable_id
      (ProbabilityTheory.Kernel.ofFunOfCountable armLaw)
      armLaw (ETC.exploreArm spec 0)
      (by simpa using hactionZero) (fun _value => rfl) hzero
  · intro i hi
    let fullCondition : Omega ->
        History.FinitePairHistory (Fin K) Rat i × Fin K :=
      fun omega =>
        (History.finitePairHistoryOfTrace
            (action omega) (reward omega) i,
          action omega (i + 1))
    have hfullCondition : Measurable fullCondition :=
      (History.measurable_finitePairHistoryOfTrace
        action reward haction hreward i).prod (haction (i + 1))
    exact RewardKernel.condDistrib_ae_eq_const_of_ae_eq_selected
      mu fullCondition hfullCondition
      (fun omega : Omega => reward omega (i + 1))
      Prod.snd measurable_snd
      (RewardKernel.contextIndependentOfActionLaws
        (Context := History.FinitePairHistory (Fin K) Rat i)
        armLaw hprob).kernel
      armLaw (ETC.exploreArm spec (i + 1))
      (by simpa [fullCondition] using hactionExplore i hi)
      (fun _value => rfl) (hcond i hi)

end ETC
end BanditRLProof
