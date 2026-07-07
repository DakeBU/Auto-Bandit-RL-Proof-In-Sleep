import Mathlib.Probability.Independence.Conditional
import BanditRLProof.RewardKernel
import BanditRLProof.Regret

/-!
# Conditional centered reward kernel bridge

This module exposes a narrow `COND-EXPECT-REWARD` support leaf: if the
conditional-expectation kernel already identifies the next centered reward law
and its conditional integral is zero, then the ordinary conditional expectation
of that centered reward is zero.

It does not construct the `condExpKernel`/trajectory-law identification, policy
predictability, conditional sub-Gaussian witnesses, or final adaptive regret
theorems.
-/

namespace BanditRLProof
namespace ConditionalExpectationReward

open MeasureTheory

universe u v w x

/--
Turn a trimmed-a.e. zero conditional-kernel integral into a true conditional
mean-zero statement.

This is the generic kernel-facing bridge for `COND-EXPECT-REWARD`.  The hard
future work is to prove `h_kernel_zero` from a trajectory/kernel law; this
wrapper only connects that law-shaped hypothesis to Mathlib's `condExp`.
-/
theorem condExp_eq_zero_of_condExpKernel_integral_eq_zero
    {Omega : Type u}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (mcond : MeasurableSpace Omega) (hm : mcond <= mOmega)
    (X : Omega -> Real)
    (h_integrable : Integrable X mu)
    (h_kernel_zero :
      Filter.Eventually
        (fun omega : Omega =>
          integral
            (ProbabilityTheory.condExpKernel
              (Ω := Omega) (mΩ := mOmega) mu mcond omega)
            X = 0)
        (ae (mu.trim hm))) :
    Filter.EventuallyEq (ae mu)
      (@condExp Omega Real mcond mOmega _ _ _ mu X)
      (fun _omega : Omega => (0 : Real)) := by
  have h_kernel :
      Filter.EventuallyEq (ae (mu.trim hm))
        (@condExp Omega Real mcond mOmega _ _ _ mu X)
        (fun omega : Omega =>
          integral
            (ProbabilityTheory.condExpKernel
              (Ω := Omega) (mΩ := mOmega) mu mcond omega)
            X) := by
    exact
      @ProbabilityTheory.condExp_ae_eq_trim_integral_condExpKernel
        Omega Real mcond mOmega inferInstance mu inferInstance
        inferInstance X inferInstance inferInstance hm h_integrable
  have h_trim_zero :
      Filter.EventuallyEq (ae (mu.trim hm))
        (@condExp Omega Real mcond mOmega _ _ _ mu X)
        (fun _omega : Omega => (0 : Real)) :=
    h_kernel.trans h_kernel_zero
  exact ae_eq_of_ae_eq_trim h_trim_zero

/--
Monotonicity of the variance proxy in Mathlib's unconditional sub-Gaussian
MGF predicate.

This small helper lets history-selected kernel witnesses with proxy `c` feed a
conditional theorem stated with a deterministic upper proxy `d`.
-/
theorem hasSubgaussianMGF_mono_varianceProxy
    {Omega : Type u} [MeasurableSpace Omega]
    {mu : Measure Omega} {X : Omega -> Real} {c d : NNReal}
    (hcd : c <= d)
    (h : ProbabilityTheory.HasSubgaussianMGF X c mu) :
    ProbabilityTheory.HasSubgaussianMGF X d mu where
  integrable_exp_mul := h.integrable_exp_mul
  mgf_le := by
    intro t
    calc
      ProbabilityTheory.mgf X mu t <=
          Real.exp (((c : NNReal) : Real) * t ^ 2 / 2) :=
        h.mgf_le t
      _ <= Real.exp (((d : NNReal) : Real) * t ^ 2 / 2) := by
        apply Real.exp_le_exp.mpr
        have hcd_real : ((c : NNReal) : Real) <= ((d : NNReal) : Real) := by
          exact_mod_cast hcd
        have ht2 : 0 <= t ^ 2 := sq_nonneg t
        nlinarith

/--
Convert a `condDistrib` law into a `condExpKernel` pushforward law on a
countable target.

Mathlib supplies eventwise equality between regular conditional distributions
and `condExpKernel` pushforwards.  This wrapper packages those singleton
equalities into a measure equality when the target type is countable.  It is a
local bridge from canonical `condDistrib` trajectory laws toward the
`condExpKernel` map-law consumers below; it does not itself construct the
trajectory law.
-/
theorem condExpKernel_map_eq_of_condDistrib_ae_eq_countable
    {Omega : Type u} {Target : Type v} {Condition : Type w}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [Nonempty Omega]
    [mTarget : MeasurableSpace Target] [StandardBorelSpace Target]
    [Nonempty Target] [MeasurableSingletonClass Target] [Countable Target]
    [mCondition : MeasurableSpace Condition]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (X : Omega -> Target) (Y : Omega -> Condition)
    (hX : @Measurable Omega Target mOmega mTarget X)
    (hY : @Measurable Omega Condition mOmega mCondition Y)
    (kernel : ProbabilityTheory.Kernel Condition Target)
    (hcond :
      Filter.EventuallyEq (ae (mu.map Y))
        (ProbabilityTheory.condDistrib X Y mu)
        kernel) :
    Filter.Eventually
      (fun omega : Omega =>
        @Measure.map Omega Target mOmega mTarget X
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
            (mCondition.comap Y) omega) =
        kernel (Y omega))
      (ae mu) := by
  have hcond_pullback :
      Filter.Eventually
        (fun omega : Omega =>
          ProbabilityTheory.condDistrib X Y mu (Y omega) =
          kernel (Y omega))
        (ae mu) :=
    MeasureTheory.ae_of_ae_map hY.aemeasurable hcond
  have hsingle :
      Filter.Eventually
        (fun omega : Omega =>
          forall z : Target,
            ((@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
                  (mCondition.comap Y)).map X omega) {z} =
              kernel (Y omega) {z})
        (ae mu) := by
    rw [ae_all_iff]
    intro z
    have h_event :
        Filter.EventuallyEq (ae mu)
          (fun omega : Omega =>
            ProbabilityTheory.condDistrib X Y mu (Y omega) {z})
          (fun omega : Omega =>
            ((@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
                (mCondition.comap Y)).map X omega) {z}) :=
      ProbabilityTheory.condDistrib_apply_ae_eq_condExpKernel_map
        (μ := mu) hX hY (MeasurableSet.singleton z)
    filter_upwards [h_event, hcond_pullback] with omega h_event_eq hcond_eq
    calc
      ((@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
            (mCondition.comap Y)).map X omega) {z}
          =
        ProbabilityTheory.condDistrib X Y mu (Y omega) {z} := h_event_eq.symm
      _ = kernel (Y omega) {z} := by rw [hcond_eq]
  filter_upwards [hsingle] with omega hsingle_omega
  have hkernel :
      ((@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
          (mCondition.comap Y)).map X omega) =
        kernel (Y omega) :=
    Measure.ext_of_singleton hsingle_omega
  simpa [ProbabilityTheory.Kernel.map_apply _ hX] using hkernel

/--
Canonical `trajMeasure` reward law in `condExpKernel.map` form.

This specializes `condExpKernel_map_eq_of_condDistrib_ae_eq_countable` to the
Mathlib Ionescu-Tulcea trajectory measure generated by
`RewardKernel.actionRewardHistoryStepKernelFamily`.  It converts the canonical
next-reward `condDistrib` law into the `condExpKernel` pushforward-map shape
used by the project-local conditional reward consumers.
-/
theorem actionRewardHistoryStepKernelFamily_reward_condExpKernel_map_trajMeasure
    {Context : Type x} {State : Type u} {Action : Type v}
    {Reward : Type w}
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSpace Reward]
    [StandardBorelSpace (Prod Action Reward)]
    [StandardBorelSpace Reward]
    [StandardBorelSpace ((t : Nat) -> Prod Action Reward)]
    [Nonempty (Prod Action Reward)] [Nonempty Reward]
    [Nonempty ((t : Nat) -> Prod Action Reward)]
    [MeasurableSingletonClass Reward] [Countable Reward]
    (mu0 : Measure (Prod Action Reward))
    [MeasureTheory.IsProbabilityMeasure mu0]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Reward)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context :
      (n : Nat) -> ((i : Finset.Iic n) -> Prod Action Reward) -> Context)
    (state :
      (n : Nat) -> ((i : Finset.Iic n) -> Prod Action Reward) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (n : Nat) :
    let stepKernel :=
      RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
        context state hcontext hstate
    let trajMeasure :=
      ProbabilityTheory.Kernel.trajMeasure
        (X := fun _ : Nat => Prod Action Reward) mu0 stepKernel
    Filter.Eventually
      (fun trajectory : (t : Nat) -> Prod Action Reward =>
        @Measure.map ((t : Nat) -> Prod Action Reward) Reward
          inferInstance inferInstance
          (fun y : (t : Nat) -> Prod Action Reward => (y (n + 1)).2)
          (@ProbabilityTheory.condExpKernel
            ((t : Nat) -> Prod Action Reward) inferInstance _
            trajMeasure _
            ((inferInstance :
              MeasurableSpace
                ((i : Finset.Iic n) -> Prod Action Reward)).comap
              (Preorder.frestrictLe n))
            trajectory) =
        ((stepKernel n).map Prod.snd) (Preorder.frestrictLe n trajectory))
      (ae trajMeasure) := by
  let stepKernel :=
    RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
      context state hcontext hstate
  let trajMeasure :=
    ProbabilityTheory.Kernel.trajMeasure
      (X := fun _ : Nat => Prod Action Reward) mu0 stepKernel
  let prefixMap :
      ((t : Nat) -> Prod Action Reward) ->
        ((i : Finset.Iic n) -> Prod Action Reward) :=
    Preorder.frestrictLe n
  let nextReward : ((t : Nat) -> Prod Action Reward) -> Reward :=
    fun trajectory => (trajectory (n + 1)).2
  have h_nextReward : Measurable nextReward := by
    exact measurable_snd.comp (measurable_pi_apply (n + 1))
  have h_prefix : Measurable prefixMap := by
    fun_prop
  have hcond :
      Filter.EventuallyEq (ae (trajMeasure.map prefixMap))
        (ProbabilityTheory.condDistrib nextReward prefixMap trajMeasure)
        ((stepKernel n).map Prod.snd) := by
    simpa [stepKernel, trajMeasure, prefixMap, nextReward] using
      RewardKernel.actionRewardHistoryStepKernelFamily_reward_condDistrib_trajMeasure
        mu0 rewardKernel policy context state hcontext hstate n
  have hbridge :=
    condExpKernel_map_eq_of_condDistrib_ae_eq_countable
      (mu := trajMeasure)
      (X := nextReward)
      (Y := prefixMap)
      h_nextReward h_prefix ((stepKernel n).map Prod.snd) hcond
  simpa [stepKernel, trajMeasure, prefixMap, nextReward] using hbridge

/--
Generic `condExpKernel` map-law consumer for conditional sub-Gaussianity.

If the conditional kernel pushed forward by `X` is trim-a.e. a target measure
whose identity random variable is sub-Gaussian with deterministic proxy `c`,
then `X` is conditionally sub-Gaussian.  The exponential-integrability field is
kept explicit because Mathlib's `Kernel.HasSubgaussianMGF` asks for global
integrability over `(mu.trim hm).bind (condExpKernel mu mcond)`.
-/
theorem hasCondSubgaussianMGF_of_condExpKernel_map_eq
    {Omega : Type u}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (mcond : MeasurableSpace Omega) (hm : mcond <= mOmega)
    (X : Omega -> Real) (c : NNReal)
    (hX : @Measurable Omega Real mOmega inferInstance X)
    (target : Omega -> Measure Real)
    (h_integrable_exp :
      forall t : Real,
        Integrable (fun omega : Omega => Real.exp (t * X omega)) mu)
    (h_kernel_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega Real mOmega inferInstance X
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ mcond
              omega) =
          target omega)
        (ae (mu.trim hm)))
    (h_target_subG :
      Filter.Eventually
        (fun omega : Omega =>
          ProbabilityTheory.HasSubgaussianMGF
            (fun z : Real => z) c (target omega))
        (ae (mu.trim hm))) :
    ProbabilityTheory.HasCondSubgaussianMGF mcond hm X c mu := by
  have h_integrable_comp :
      forall t : Real,
        Integrable (fun omega : Omega => Real.exp (t * X omega))
          ((mu.trim hm).bind
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ mcond)) := by
    intro t
    rw [@ProbabilityTheory.condExpKernel_comp_trim
      Omega mcond mOmega _ mu _ hm]
    exact h_integrable_exp t
  change
    ProbabilityTheory.Kernel.HasSubgaussianMGF X c
      (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ mcond)
      (mu.trim hm)
  refine ProbabilityTheory.Kernel.HasSubgaussianMGF.of_rat
    h_integrable_comp ?_
  intro q
  filter_upwards [h_kernel_map_eq, h_target_subG] with omega hmap hsub
  let condKernel : @Measure Omega mOmega :=
    @ProbabilityTheory.condExpKernel Omega mOmega _ mu _ mcond omega
  calc
    ProbabilityTheory.mgf X
        (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ mcond omega)
        (q : Real)
        =
      ProbabilityTheory.mgf (fun z : Real => z)
        (@Measure.map Omega Real mOmega inferInstance X
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ mcond
            omega))
        (q : Real) := by
          simpa [condKernel] using
            congrFun
              (@ProbabilityTheory.mgf_id_map Omega mOmega X condKernel
                hX.aemeasurable).symm
              (q : Real)
    _ = ProbabilityTheory.mgf (fun z : Real => z) (target omega)
        (q : Real) := by
          rw [hmap]
    _ <= Real.exp (((c : NNReal) : Real) * (q : Real) ^ 2 / 2) := by
          simpa using hsub.mgf_le (q : Real)

/--
Centered-reward specialization of
`condExp_eq_zero_of_condExpKernel_integral_eq_zero`.

The statement matches the succ-indexed shape used by Mathlib's conditional
tail API: the reward at `i + 1` is conditioned on filtration level `i`.
-/
theorem centeredReward_succ_condExp_eq_zero_of_condExpKernel_integral_eq_zero
    {Omega : Type u} {K : Nat}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (F : Filtration Nat mOmega)
    (model : FiniteBanditModel K)
    (reward : Omega -> RewardTrace Rat)
    (b : Fin K) (i : Nat)
    (h_integrable :
      Integrable
        (fun omega : Omega =>
          (((reward omega (i + 1) - model.mean b : Rat) : Real))) mu)
    (h_kernel_zero :
      Filter.Eventually
        (fun omega : Omega =>
          integral
            (ProbabilityTheory.condExpKernel
              (Ω := Omega) (mΩ := mOmega) mu (F i) omega)
            (fun y : Omega =>
              (((reward y (i + 1) - model.mean b : Rat) : Real))) = 0)
        (ae (mu.trim (F.le i)))) :
    Filter.EventuallyEq (ae mu)
      (@condExp Omega Real (F i) mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) - model.mean b : Rat) : Real))))
      (fun _omega : Omega => (0 : Real)) := by
  exact
    condExp_eq_zero_of_condExpKernel_integral_eq_zero
      (mu := mu)
      (mcond := F i)
      (hm := F.le i)
      (X := fun omega : Omega =>
        (((reward omega (i + 1) - model.mean b : Rat) : Real)))
      h_integrable
      h_kernel_zero

/--
Consumer bridge from a trajectory-law-shaped conditional-kernel identification
to ordinary conditional mean zero.

The hypothesis `h_kernel_eq` is intentionally explicit: it is the future
`condExpKernel`/history-step reward-law identification, already reduced to the
centered integral shape needed here.  The theorem then uses the compiled
`RewardKernel.historyStepKernelFamily_centeredReward_integral_eq_zero` leaf and
the generic `condExpKernel` bridge above.
-/
theorem condExp_eq_zero_of_condExpKernel_integral_eq_historyStepKernel_centeredReward
    {Omega : Type u} {Context : Type v} {State : Type w} {Action : Type x}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (mcond : MeasurableSpace Omega) (hm : mcond <= mOmega)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Context × Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((i : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((i : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (law :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (n : Nat)
    (history : Omega -> ((i : Finset.Iic n) -> Rat))
    (X : Omega -> Real)
    (h_integrable : Integrable X mu)
    (h_kernel_eq :
      Filter.Eventually
        (fun omega : Omega =>
          integral
            (ProbabilityTheory.condExpKernel
              (Ω := Omega) (mΩ := mOmega) mu mcond omega)
            X =
          integral
            (RewardKernel.historyStepKernelFamily rewardKernel policy context
              state hcontext hstate n (history omega))
            (fun reward : Rat =>
              (((reward -
                mean (context n (history omega))
                  ((policy n).action (state n (history omega))) :
                    Rat) : Real))))
        (ae (mu.trim hm))) :
    Filter.EventuallyEq (ae mu)
      (@condExp Omega Real mcond mOmega _ _ _ mu X)
      (fun _omega : Omega => (0 : Real)) := by
  refine
    @condExp_eq_zero_of_condExpKernel_integral_eq_zero
      Omega mOmega inferInstance mu inferInstance mcond hm X h_integrable ?_
  filter_upwards [h_kernel_eq] with omega h_eq
  rw [h_eq]
  exact
    RewardKernel.historyStepKernelFamily_centeredReward_integral_eq_zero
      rewardKernel policy context state hcontext hstate mean varianceProxy law
      n (history omega)

/--
Succ-indexed selected-reward specialization of
`condExp_eq_zero_of_condExpKernel_integral_eq_historyStepKernel_centeredReward`.

The centered variable uses the history-selected context/action mean.  The only
law-identification input is `h_kernel_eq`; constructing that equality from a
`partialTraj` trajectory measure is still a separate missing leaf.
-/
theorem centeredReward_succ_condExp_eq_zero_of_historyStepKernelFamily_condExpKernel_integral_eq
    {Omega : Type u} {Context : Type v} {State : Type w} {Action : Type x}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (F : Filtration Nat mOmega)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Context × Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (law :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (reward : Omega -> RewardTrace Rat)
    (i : Nat)
    (history : Omega -> ((j : Finset.Iic i) -> Rat))
    (h_integrable :
      Integrable
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean (context i (history omega))
              ((policy i).action (state i (history omega))) : Rat) :
                Real))) mu)
    (h_kernel_eq :
      Filter.Eventually
        (fun omega : Omega =>
          integral
            (ProbabilityTheory.condExpKernel
              (Ω := Omega) (mΩ := mOmega) mu (F i) omega)
            (fun y : Omega =>
              (((reward y (i + 1) -
                mean (context i (history y))
                  ((policy i).action (state i (history y))) : Rat) :
                    Real))) =
          integral
            (RewardKernel.historyStepKernelFamily rewardKernel policy context
              state hcontext hstate i (history omega))
            (fun reward : Rat =>
              (((reward -
                mean (context i (history omega))
                  ((policy i).action (state i (history omega))) :
                    Rat) : Real))))
        (ae (mu.trim (F.le i)))) :
    Filter.EventuallyEq (ae mu)
      (@condExp Omega Real (F i) mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean (context i (history omega))
              ((policy i).action (state i (history omega))) : Rat) :
                Real))))
      (fun _omega : Omega => (0 : Real)) := by
  exact
    condExp_eq_zero_of_condExpKernel_integral_eq_historyStepKernel_centeredReward
      (mu := mu)
      (mcond := F i)
      (hm := F.le i)
      (rewardKernel := rewardKernel)
      (policy := policy)
      (context := context)
      (state := state)
      (hcontext := hcontext)
      (hstate := hstate)
      (mean := mean)
      (varianceProxy := varianceProxy)
      (law := law)
      (n := i)
      (history := history)
      (X := fun omega : Omega =>
        (((reward omega (i + 1) -
          mean (context i (history omega))
            ((policy i).action (state i (history omega))) : Rat) :
              Real)))
      h_integrable
      h_kernel_eq

/--
Map-law consumer for the history-step conditional mean-zero route.

Compared with the integral-equality consumer above, this theorem assumes a
more structural reward-law identification: trim-a.e., the conditional kernel
pushed forward by the next-reward coordinate is the corresponding
`historyStepKernelFamily` reward law.  The separate `h_kernel_X_eq` hypothesis
records the usual "past is frozen under conditioning" obligation needed to
replace the actual target variable by the centered function with the outer
history fixed at `omega`.

This still does not construct the `partialTraj`/`condExpKernel` identity; it
only consumes a map-level version of that identity.
-/
theorem condExp_eq_zero_of_condExpKernel_map_eq_historyStepKernel_centeredReward
    {Omega : Type u} {Context : Type v} {State : Type w} {Action : Type x}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (mcond : MeasurableSpace Omega) (hm : mcond <= mOmega)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Context × Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((i : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((i : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (law :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (n : Nat)
    (history : Omega -> ((i : Finset.Iic n) -> Rat))
    (nextReward : Omega -> Rat)
    (X : Omega -> Real)
    (h_nextReward : @Measurable Omega Rat mOmega inferInstance nextReward)
    (h_integrable : Integrable X mu)
    (h_kernel_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega Rat mOmega inferInstance nextReward
            (ProbabilityTheory.condExpKernel
              (Ω := Omega) (mΩ := mOmega) mu mcond omega) =
          RewardKernel.historyStepKernelFamily rewardKernel policy context state
            hcontext hstate n (history omega))
        (ae (mu.trim hm)))
    (h_kernel_X_eq :
      Filter.Eventually
        (fun omega : Omega =>
          X =ᵐ[
            ProbabilityTheory.condExpKernel
              (Ω := Omega) (mΩ := mOmega) mu mcond omega]
            (fun y : Omega =>
              (((nextReward y -
                mean (context n (history omega))
                  ((policy n).action (state n (history omega))) :
                    Rat) : Real))))
        (ae (mu.trim hm))) :
    Filter.EventuallyEq (ae mu)
      (@condExp Omega Real mcond mOmega _ _ _ mu X)
      (fun _omega : Omega => (0 : Real)) := by
  refine
    @condExp_eq_zero_of_condExpKernel_integral_eq_zero
      Omega mOmega inferInstance mu inferInstance mcond hm X h_integrable ?_
  filter_upwards [h_kernel_map_eq, h_kernel_X_eq] with omega h_map h_X
  have h_centered_meas :
      Measurable
        (fun reward : Rat =>
          (((reward -
            mean (context n (history omega))
              ((policy n).action (state n (history omega))) : Rat) :
                Real))) := by
    exact
      measurable_of_countable
        (fun reward : Rat =>
          (((reward -
            mean (context n (history omega))
              ((policy n).action (state n (history omega))) : Rat) :
                Real)))
  calc
    integral
        (ProbabilityTheory.condExpKernel
          (Ω := Omega) (mΩ := mOmega) mu mcond omega)
        X
        =
      integral
        (ProbabilityTheory.condExpKernel
          (Ω := Omega) (mΩ := mOmega) mu mcond omega)
        (fun y : Omega =>
          (((nextReward y -
            mean (context n (history omega))
              ((policy n).action (state n (history omega))) : Rat) :
                Real))) := by
          exact integral_congr_ae h_X
    _ =
      integral
        (@Measure.map Omega Rat mOmega inferInstance nextReward
          (ProbabilityTheory.condExpKernel
            (Ω := Omega) (mΩ := mOmega) mu mcond omega))
        (fun reward : Rat =>
          (((reward -
            mean (context n (history omega))
              ((policy n).action (state n (history omega))) : Rat) :
                Real))) := by
          exact
            (integral_map
              h_nextReward.aemeasurable
              h_centered_meas.aestronglyMeasurable).symm
    _ =
      integral
        (RewardKernel.historyStepKernelFamily rewardKernel policy context state
          hcontext hstate n (history omega))
        (fun reward : Rat =>
          (((reward -
            mean (context n (history omega))
              ((policy n).action (state n (history omega))) : Rat) :
                Real))) := by
          rw [h_map]
    _ = 0 := by
      exact
        RewardKernel.historyStepKernelFamily_centeredReward_integral_eq_zero
          rewardKernel policy context state hcontext hstate mean varianceProxy
          law n (history omega)

/--
Map-law consumer for the history-step conditional sub-Gaussian route.

This is the MGF analogue of
`condExp_eq_zero_of_condExpKernel_map_eq_historyStepKernel_centeredReward`.
It keeps two contracts explicit: `h_kernel_X_eq` freezes the history-dependent
centering under the conditional kernel, and `h_variance_le` bounds the
history-selected variance proxy by the deterministic proxy `c` required by
Mathlib's `HasCondSubgaussianMGF`.
-/
theorem hasCondSubgaussianMGF_of_condExpKernel_map_eq_historyStepKernel_centeredReward
    {Omega : Type u} {Context : Type v} {State : Type w} {Action : Type x}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (mcond : MeasurableSpace Omega) (hm : mcond <= mOmega)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((i : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((i : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (law :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (n : Nat)
    (history : Omega -> ((i : Finset.Iic n) -> Rat))
    (nextReward : Omega -> Rat)
    (X : Omega -> Real)
    (c : NNReal)
    (h_nextReward : @Measurable Omega Rat mOmega inferInstance nextReward)
    (hX : @Measurable Omega Real mOmega inferInstance X)
    (h_integrable_exp :
      forall t : Real,
        Integrable (fun omega : Omega => Real.exp (t * X omega)) mu)
    (h_kernel_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega Rat mOmega inferInstance nextReward
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ mcond
              omega) =
          RewardKernel.historyStepKernelFamily rewardKernel policy context
            state hcontext hstate n (history omega))
        (ae (mu.trim hm)))
    (h_kernel_X_eq :
      Filter.Eventually
        (fun omega : Omega =>
          Filter.EventuallyEq
            (ae (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ mcond
              omega))
            X
            (fun y : Omega =>
              (((nextReward y - mean (context n (history omega))
                ((policy n).action (state n (history omega))) : Rat) : Real))))
        (ae (mu.trim hm)))
    (h_variance_le :
      Filter.Eventually
        (fun omega : Omega =>
          varianceProxy (context n (history omega))
            ((policy n).action (state n (history omega))) <= c)
        (ae (mu.trim hm))) :
    ProbabilityTheory.HasCondSubgaussianMGF mcond hm X c mu := by
  let target : Omega -> Measure Real :=
    fun omega : Omega =>
      @Measure.map Rat Real inferInstance inferInstance
        (fun reward : Rat =>
          (((reward - mean (context n (history omega))
            ((policy n).action (state n (history omega))) : Rat) : Real)))
        (RewardKernel.historyStepKernelFamily rewardKernel policy context
          state hcontext hstate n (history omega))
  have h_target_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega Real mOmega inferInstance X
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ mcond
              omega) =
          target omega)
        (ae (mu.trim hm)) := by
    filter_upwards [h_kernel_map_eq, h_kernel_X_eq] with omega hmap hXeq
    let condKernel : @Measure Omega mOmega :=
      @ProbabilityTheory.condExpKernel Omega mOmega _ mu _ mcond omega
    let centeredReward : Rat -> Real :=
      fun reward : Rat =>
        (((reward - mean (context n (history omega))
          ((policy n).action (state n (history omega))) : Rat) : Real))
    have h_centered_meas : Measurable centeredReward := by
      exact measurable_of_countable centeredReward
    have h_X_map :
        @Measure.map Omega Real mOmega inferInstance X condKernel =
          @Measure.map Omega Real mOmega inferInstance
            (fun y : Omega => centeredReward (nextReward y)) condKernel := by
      exact Measure.map_congr hXeq
    have h_comp :
        @Measure.map Rat Real inferInstance inferInstance centeredReward
            (@Measure.map Omega Rat mOmega inferInstance nextReward
              condKernel) =
          @Measure.map Omega Real mOmega inferInstance
            (fun y : Omega => centeredReward (nextReward y)) condKernel := by
      rw [Measure.map_map h_centered_meas h_nextReward]
      rfl
    calc
      @Measure.map Omega Real mOmega inferInstance X
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ mcond
            omega)
          =
        @Measure.map Omega Real mOmega inferInstance X condKernel := by
          rfl
      _ =
        @Measure.map Omega Real mOmega inferInstance
          (fun y : Omega => centeredReward (nextReward y)) condKernel :=
        h_X_map
      _ =
        @Measure.map Rat Real inferInstance inferInstance centeredReward
          (@Measure.map Omega Rat mOmega inferInstance nextReward
            condKernel) :=
        h_comp.symm
      _ =
        @Measure.map Rat Real inferInstance inferInstance centeredReward
          (RewardKernel.historyStepKernelFamily rewardKernel policy context
            state hcontext hstate n (history omega)) := by
        rw [hmap]
      _ = target omega := by
        rfl
  have h_target_subG :
      Filter.Eventually
        (fun omega : Omega =>
          ProbabilityTheory.HasSubgaussianMGF (fun z : Real => z) c
            (target omega))
        (ae (mu.trim hm)) := by
    filter_upwards [h_variance_le] with omega hvar
    let centeredReward : Rat -> Real :=
      fun reward : Rat =>
        (((reward - mean (context n (history omega))
          ((policy n).action (state n (history omega))) : Rat) : Real))
    have h_centered_meas : Measurable centeredReward := by
      exact measurable_of_countable centeredReward
    have h_subG :
        ProbabilityTheory.HasSubgaussianMGF centeredReward
          (varianceProxy (context n (history omega))
            ((policy n).action (state n (history omega))))
          (RewardKernel.historyStepKernelFamily rewardKernel policy context
            state hcontext hstate n (history omega)) := by
      simpa [centeredReward] using
        RewardKernel.historyStepKernelFamily_centeredReward_hasSubgaussianMGF
          rewardKernel policy context state hcontext hstate mean
          varianceProxy law n (history omega)
    have h_id_subG :
        ProbabilityTheory.HasSubgaussianMGF (fun z : Real => z)
          (varianceProxy (context n (history omega))
            ((policy n).action (state n (history omega))))
          (@Measure.map Rat Real inferInstance inferInstance centeredReward
            (RewardKernel.historyStepKernelFamily rewardKernel policy context
              state hcontext hstate n (history omega))) := by
      exact
        (ProbabilityTheory.HasSubgaussianMGF.id_map_iff
          h_centered_meas.aemeasurable).2 h_subG
    simpa [target, centeredReward] using
      hasSubgaussianMGF_mono_varianceProxy hvar h_id_subG
  exact
    hasCondSubgaussianMGF_of_condExpKernel_map_eq
      (mOmega := mOmega)
      (mu := mu)
      (mcond := mcond)
      (hm := hm)
      (X := X)
      (c := c)
      hX
      target
      h_integrable_exp
      h_target_map_eq
      h_target_subG

/--
Succ-indexed selected-reward specialization of the conditional sub-Gaussian
map-law consumer.

This is the MGF analogue of
`centeredReward_succ_condExp_eq_zero_of_historyStepKernelFamily_condExpKernel_map_eq`.
It keeps exponential integrability, measurability, and deterministic variance
domination explicit; the theorem only discharges the kernel-side
sub-Gaussian law from the history-step reward-kernel contract.
-/
theorem centeredReward_succ_hasCondSubgaussianMGF_of_historyStepKernelFamily_condExpKernel_map_eq
    {Omega : Type u} {Context : Type v} {State : Type w} {Action : Type x}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (F : Filtration Nat mOmega)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (law :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (reward : Omega -> RewardTrace Rat)
    (i : Nat)
    (history : Omega -> ((j : Finset.Iic i) -> Rat))
    (c : NNReal)
    (h_reward :
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega (i + 1)))
    (h_centered_meas :
      @Measurable Omega Real mOmega inferInstance
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean (context i (history omega))
              ((policy i).action (state i (history omega))) : Rat) :
                Real))))
    (h_integrable_exp :
      forall t : Real,
        Integrable
          (fun omega : Omega =>
            Real.exp (t *
              (((reward omega (i + 1) -
                mean (context i (history omega))
                  ((policy i).action (state i (history omega))) : Rat) :
                    Real)))) mu)
    (h_kernel_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega Rat mOmega inferInstance
            (fun y : Omega => reward y (i + 1))
            (ProbabilityTheory.condExpKernel
              (Ω := Omega) (mΩ := mOmega) mu (F i) omega) =
          RewardKernel.historyStepKernelFamily rewardKernel policy context state
            hcontext hstate i (history omega))
        (ae (mu.trim (F.le i))))
    (h_kernel_X_eq :
      Filter.Eventually
        (fun omega : Omega =>
          Filter.EventuallyEq
            (ae
              (ProbabilityTheory.condExpKernel
                (Ω := Omega) (mΩ := mOmega) mu (F i) omega))
            (fun y : Omega =>
              (((reward y (i + 1) -
                mean (context i (history y))
                  ((policy i).action (state i (history y))) : Rat) :
                    Real)))
            (fun y : Omega =>
              (((reward y (i + 1) -
                mean (context i (history omega))
                  ((policy i).action (state i (history omega))) : Rat) :
                    Real))))
        (ae (mu.trim (F.le i))))
    (h_variance_le :
      Filter.Eventually
        (fun omega : Omega =>
          varianceProxy (context i (history omega))
            ((policy i).action (state i (history omega))) <= c)
        (ae (mu.trim (F.le i)))) :
    ProbabilityTheory.HasCondSubgaussianMGF (F i) (F.le i)
      (fun omega : Omega =>
        (((reward omega (i + 1) -
          mean (context i (history omega))
            ((policy i).action (state i (history omega))) : Rat) : Real)))
      c mu := by
  exact
    hasCondSubgaussianMGF_of_condExpKernel_map_eq_historyStepKernel_centeredReward
      (mu := mu)
      (mcond := F i)
      (hm := F.le i)
      (rewardKernel := rewardKernel)
      (policy := policy)
      (context := context)
      (state := state)
      (hcontext := hcontext)
      (hstate := hstate)
      (mean := mean)
      (varianceProxy := varianceProxy)
      (law := law)
      (n := i)
      (history := history)
      (nextReward := fun omega : Omega => reward omega (i + 1))
      (X := fun omega : Omega =>
        (((reward omega (i + 1) -
          mean (context i (history omega))
            ((policy i).action (state i (history omega))) : Rat) :
              Real)))
      (c := c)
      h_reward
      h_centered_meas
      h_integrable_exp
      h_kernel_map_eq
      h_kernel_X_eq
      h_variance_le

/--
Event-level frozen-past canary for conditional-expectation kernels.

If an event is measurable in the conditioning sigma-algebra, then trim-a.e. the
conditional kernel assigns its real mass as the event indicator.  This is the
0/1 event support fact used to freeze countable-valued past summaries below.
-/
theorem condExpKernel_event_real_eq_indicator_of_measurableSet
    {Omega : Type u}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (mcond : MeasurableSpace Omega) (hm : mcond <= mOmega)
    (s : Set Omega) (hs : @MeasurableSet Omega mcond s) :
    Filter.Eventually
      (fun omega : Omega =>
        (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ mcond omega).real s =
        Set.indicator s (fun _omega : Omega => (1 : Real)) omega)
      (ae (mu.trim hm)) := by
  let f : Omega -> Real :=
    Set.indicator s (fun _omega : Omega => (1 : Real))
  have hs_mOmega : @MeasurableSet Omega mOmega s := hm s hs
  have h_kernel :
      Filter.EventuallyEq (ae (mu.trim hm))
        (fun omega : Omega =>
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ mcond omega).real s)
        (@condExp Omega Real mcond mOmega _ _ _ mu f) := by
    simpa [f] using
      (@ProbabilityTheory.condExpKernel_ae_eq_trim_condExp
        Omega mcond mOmega _ mu _ hm s hs_mOmega)
  have hf_strong : StronglyMeasurable[mcond] f := by
    exact (Measurable.indicator measurable_const hs).stronglyMeasurable
  have hf_integrable : Integrable f mu := by
    exact (integrable_const (1 : Real)).indicator hs_mOmega
  have h_cond :
      @condExp Omega Real mcond mOmega _ _ _ mu f = f := by
    exact condExp_of_stronglyMeasurable hm hf_strong hf_integrable
  exact h_kernel.trans (Filter.EventuallyEq.of_eq h_cond)

/--
Countable-valued frozen-past theorem for conditional-expectation kernels.

Any countable-valued random variable measurable in the conditioning
sigma-algebra is trim-a.e. constant under the corresponding conditional
kernel.  This packages the event-level 0/1 fact over all singleton fibers.
-/
theorem condExpKernel_ae_eq_const_of_countable_measurable
    {Omega : Type u} {A : Type v}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace A] [MeasurableSingletonClass A] [Countable A]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (mcond : MeasurableSpace Omega) (hm : mcond <= mOmega)
    (Y : Omega -> A)
    (hY : @Measurable Omega A mcond inferInstance Y) :
    Filter.Eventually
      (fun omega : Omega =>
        Filter.EventuallyEq
          (ae (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ mcond omega))
          Y
          (fun _y : Omega => Y omega))
      (ae (mu.trim hm)) := by
  classical
  have h_fibers :
      Filter.Eventually
        (fun omega : Omega =>
          forall a : A,
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ mcond omega).real
                (fun z : Omega => Y z = a) =
              Set.indicator (fun z : Omega => Y z = a)
                (fun _z : Omega => (1 : Real)) omega)
        (ae (mu.trim hm)) := by
    rw [ae_all_iff]
    intro a
    have hs_fiber : @MeasurableSet Omega mcond (fun z : Omega => Y z = a) := by
      exact hY (MeasurableSet.singleton a)
    exact
      @condExpKernel_event_real_eq_indicator_of_measurableSet
        Omega mOmega inferInstance mu inferInstance mcond hm
        (fun z : Omega => Y z = a) hs_fiber
  filter_upwards [h_fibers] with omega homega
  let fiber : Set Omega := fun z : Omega => Y z = Y omega
  have hs_mcond : @MeasurableSet Omega mcond fiber := by
    exact hY (MeasurableSet.singleton (Y omega))
  have hs_mOmega : @MeasurableSet Omega mOmega fiber := hm fiber hs_mcond
  have h_indicator :
      Set.indicator (fun z : Omega => Y z = Y omega)
        (fun _z : Omega => (1 : Real)) omega = 1 := by
    rw [Set.indicator_of_mem]
    rfl
  have h_real_one :
      (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ mcond omega).real
        fiber = 1 := by
    have h := homega (Y omega)
    rw [h_indicator] at h
    simpa [fiber] using h
  have h_measure_one :
      (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ mcond omega)
        fiber = 1 := by
    exact (ENNReal.toReal_eq_one_iff _).mp (by
      simpa [Measure.real, measureReal_def] using h_real_one)
  haveI : IsProbabilityMeasure
      (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ mcond omega) := by
    infer_instance
  have h_ae_mem :
      Filter.Eventually
        (fun x : Omega => fiber x)
        (ae (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ mcond omega)) := by
    exact (mem_ae_iff_prob_eq_one hs_mOmega).2 h_measure_one
  change Filter.Eventually
    (fun z : Omega => Y z = Y omega)
    (ae (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ mcond omega))
  exact h_ae_mem

/--
Action-freezing hookup for the next-pair split-law route.

If the next action is measurable at filtration level `F i`, the conditional
kernel freezes it.  If that frozen action is also trim-a.e. the
policy-selected action for the finite pair history, this supplies exactly the
conditional a.e. action equality consumed by
`actionRewardHistoryStepKernelFamily_pair_map_eq_of_action_ae_eq_policy_reward_map_eq`.
It does not prove the predictability or policy-generation equality hypotheses.
-/
theorem action_condExpKernel_ae_eq_policy_of_measurable_of_policy_eq
    {Omega : Type u} {State : Type w} {Action : Type x}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace State] [MeasurableSpace Action]
    [MeasurableSingletonClass Action] [Countable Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (F : Filtration Nat mOmega)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (pairState :
      (n : Nat) -> ((j : Finset.Iic n) -> Prod Action Rat) -> State)
    (action : Omega -> ActionTrace Action)
    (i : Nat)
    (pairHistory : Omega -> ((j : Finset.Iic i) -> Prod Action Rat))
    (h_action_next_meas :
      @Measurable Omega Action (F i) inferInstance
        (fun omega : Omega => action omega (i + 1)))
    (h_action_policy_eq :
      Filter.Eventually
        (fun omega : Omega =>
          action omega (i + 1) =
            (policy i).action (pairState i (pairHistory omega)))
        (ae (mu.trim (F.le i)))) :
    Filter.Eventually
      (fun omega : Omega =>
        Filter.EventuallyEq
          (ae (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ (F i)
            omega))
          (fun y : Omega => action y (i + 1))
          (fun _y : Omega =>
            (policy i).action (pairState i (pairHistory omega))))
      (ae (mu.trim (F.le i))) := by
  have h_frozen :
      Filter.Eventually
        (fun omega : Omega =>
          Filter.EventuallyEq
            (ae (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ (F i)
              omega))
            (fun y : Omega => action y (i + 1))
            (fun _y : Omega => action omega (i + 1)))
        (ae (mu.trim (F.le i))) :=
    condExpKernel_ae_eq_const_of_countable_measurable
      (mu := mu)
      (mcond := F i)
      (hm := F.le i)
      (Y := fun omega : Omega => action omega (i + 1))
      h_action_next_meas
  filter_upwards [h_frozen, h_action_policy_eq] with omega homega hpolicy
  simpa [hpolicy] using homega

/--
Pair-history measurability hookup for the action side of the next-pair split.

If the finite pair history is visible at `F i`, the pair-state extractor is
measurable, and the next action is pointwise the policy action selected from
that pair state, then the previous action-freezing theorem supplies the
conditional a.e. action equality consumed by the split-law builder.
-/
theorem action_condExpKernel_ae_eq_policy_of_pairHistory_measurable_of_action_eq
    {Omega : Type u} {State : Type w} {Action : Type x}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace State] [MeasurableSpace Action]
    [MeasurableSingletonClass Action] [Countable Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (F : Filtration Nat mOmega)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (pairState :
      (n : Nat) -> ((j : Finset.Iic n) -> Prod Action Rat) -> State)
    (hpairState : forall n : Nat, Measurable (pairState n))
    (action : Omega -> ActionTrace Action)
    (i : Nat)
    (pairHistory : Omega -> ((j : Finset.Iic i) -> Prod Action Rat))
    (h_pairHistory_meas :
      @Measurable Omega ((j : Finset.Iic i) -> Prod Action Rat)
        (F i) inferInstance pairHistory)
    (h_action_eq :
      (fun omega : Omega => action omega (i + 1)) =
        (fun omega : Omega =>
          (policy i).action (pairState i (pairHistory omega)))) :
    Filter.Eventually
      (fun omega : Omega =>
        Filter.EventuallyEq
          (ae (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ (F i)
            omega))
          (fun y : Omega => action y (i + 1))
          (fun _y : Omega =>
            (policy i).action (pairState i (pairHistory omega))))
      (ae (mu.trim (F.le i))) := by
  have h_pairState_meas :
      @Measurable Omega State (F i) inferInstance
        (fun omega : Omega => pairState i (pairHistory omega)) := by
    exact (hpairState i).comp h_pairHistory_meas
  have h_action_next_meas :
      @Measurable Omega Action (F i) inferInstance
        (fun omega : Omega => action omega (i + 1)) := by
    have h_selected_meas :
        @Measurable Omega Action (F i) inferInstance
          (fun omega : Omega =>
            (policy i).action (pairState i (pairHistory omega))) :=
      (policy i).measurable_action.comp h_pairState_meas
    simpa [h_action_eq] using h_selected_meas
  have h_action_policy_eq :
      Filter.Eventually
        (fun omega : Omega =>
          action omega (i + 1) =
            (policy i).action (pairState i (pairHistory omega)))
        (ae (mu.trim (F.le i))) := by
    exact Filter.Eventually.of_forall (fun omega => congrFun h_action_eq omega)
  exact
    action_condExpKernel_ae_eq_policy_of_measurable_of_policy_eq
      (mu := mu)
      (F := F)
      (policy := policy)
      (pairState := pairState)
      (action := action)
      (i := i)
      (pairHistory := pairHistory)
      h_action_next_meas
      h_action_policy_eq

/--
Generated-history specialization of the action side of the next-pair split.

For `History.historyFiltrationSucc`, the finite action/reward pair prefix up
to `i` is visible.  Therefore a pointwise policy-generation equality for the
next action supplies the conditional action a.e. side condition required by
the split-law builder.  The reward-coordinate law remains a separate input.
-/
theorem action_condExpKernel_ae_eq_policy_historyFiltrationSucc_finitePairHistoryOfTrace_of_action_eq
    {Omega : Type u} {State : Type w} {Action : Type x}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (pairState :
      (n : Nat) -> ((j : Finset.Iic n) -> Prod Action Rat) -> State)
    (hpairState : forall n : Nat, Measurable (pairState n))
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (i : Nat)
    (h_action_eq :
      (fun omega : Omega => action omega (i + 1)) =
        (fun omega : Omega =>
          (policy i).action
            (pairState i
              (History.finitePairHistoryOfTrace
                (action omega) (reward omega) i)))) :
    Filter.Eventually
      (fun omega : Omega =>
        Filter.EventuallyEq
          (ae
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega))
          (fun y : Omega => action y (i + 1))
          (fun _y : Omega =>
            (policy i).action
              (pairState i
                (History.finitePairHistoryOfTrace
                  (action omega) (reward omega) i))))
      (ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i))) := by
  have h_pairHistory_meas :
      @Measurable Omega ((j : Finset.Iic i) -> Prod Action Rat)
        ((History.historyFiltrationSucc action reward haction hreward) i)
        inferInstance
        (fun omega : Omega =>
          History.finitePairHistoryOfTrace (action omega) (reward omega) i) := by
    letI : MeasurableSpace Omega :=
      (History.historyFiltrationSucc action reward haction hreward) i
    change Measurable
      (fun omega : Omega =>
        History.finitePairHistoryOfTrace (action omega) (reward omega) i)
    exact measurable_pi_lambda _ (fun j : Finset.Iic i => by
      have ha : Measurable (fun omega : Omega => action omega j.1) := by
        simpa [History.historyFiltrationSucc_apply] using
          (@History.measurable_action_mem_historyFiltration_of_lt
            Omega Action Rat mOmega inferInstance inferInstance inferInstance
            inferInstance inferInstance
            action reward haction hreward j.1 (i + 1)
            (Nat.lt_succ_of_le (Finset.mem_Iic.mp j.2)))
      have hr : Measurable (fun omega : Omega => reward omega j.1) := by
        simpa [History.historyFiltrationSucc_apply] using
          (@History.measurable_reward_mem_historyFiltration_of_lt
            Omega Action Rat mOmega inferInstance inferInstance inferInstance
            inferInstance inferInstance
            action reward haction hreward j.1 (i + 1)
            (Nat.lt_succ_of_le (Finset.mem_Iic.mp j.2)))
      have hp : Measurable
          (fun omega : Omega => (action omega j.1, reward omega j.1)) :=
        ha.prod hr
      simpa [History.finitePairHistoryOfTrace] using hp)
  exact
    action_condExpKernel_ae_eq_policy_of_pairHistory_measurable_of_action_eq
      (mu := mu)
      (F := History.historyFiltrationSucc action reward haction hreward)
      (policy := policy)
      (pairState := pairState)
      (hpairState := hpairState)
      (action := action)
      (i := i)
      (pairHistory := fun omega : Omega =>
        History.finitePairHistoryOfTrace (action omega) (reward omega) i)
      h_pairHistory_meas
      h_action_eq

/--
Generated-trace source for the action side of the next-pair split.

If the action trace is the shifted policy-generated trace from finite
action/reward pair histories, the pointwise policy-generation equality required
by `..._finitePairHistoryOfTrace_of_action_eq` follows from the definition of
`Policy.generatedActionTraceSucc`.
-/
theorem action_condExpKernel_ae_eq_policy_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc
    {Omega : Type u} {State : Type w} {Action : Type x}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (pairState :
      (n : Nat) -> ((j : Finset.Iic n) -> Prod Action Rat) -> State)
    (hpairState : forall n : Nat, Measurable (pairState n))
    (defaultAction : Action)
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (i : Nat)
    (h_action_generated :
      action =
        Policy.generatedActionTraceSucc policy
          (fun n omega =>
            pairState n
              (History.finitePairHistoryOfTrace
                (action omega) (reward omega) n))
          defaultAction) :
    Filter.Eventually
      (fun omega : Omega =>
        Filter.EventuallyEq
          (ae
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega))
          (fun y : Omega => action y (i + 1))
          (fun _y : Omega =>
            (policy i).action
              (pairState i
                (History.finitePairHistoryOfTrace
                  (action omega) (reward omega) i))))
      (ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i))) := by
  have h_action_eq :
      (fun omega : Omega => action omega (i + 1)) =
        (fun omega : Omega =>
          (policy i).action
            (pairState i
              (History.finitePairHistoryOfTrace
                (action omega) (reward omega) i))) := by
    funext omega
    have h_point := congrFun (congrFun h_action_generated omega) (i + 1)
    simpa [Policy.generatedActionTraceSucc] using h_point
  exact
    action_condExpKernel_ae_eq_policy_historyFiltrationSucc_finitePairHistoryOfTrace_of_action_eq
      (mu := mu)
      (policy := policy)
      (pairState := pairState)
      (hpairState := hpairState)
      (action := action)
      (reward := reward)
      (haction := haction)
      (hreward := hreward)
      (i := i)
      h_action_eq

/--
Reward-law rewrite for the next-pair split route.

Some future trajectory/source theorem may naturally identify the conditional
reward law using the actual next action at the conditioning point.  If that
actual action is trim-a.e. equal to the policy-selected action, this adapter
rewrites the reward-coordinate map law into the policy-selected shape consumed
by `actionRewardHistoryStepKernelFamily_pair_map_eq_of_action_ae_eq_policy_reward_map_eq`.
-/
theorem reward_condExpKernel_map_eq_selected_policy_of_action_eq
    {Omega : Type u} {Context : Type v} {State : Type w} {Action : Type x}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (F : Filtration Nat mOmega)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (pairContext :
      (n : Nat) -> ((j : Finset.Iic n) -> Prod Action Rat) -> Context)
    (pairState :
      (n : Nat) -> ((j : Finset.Iic n) -> Prod Action Rat) -> State)
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Rat)
    (i : Nat)
    (pairHistory : Omega -> ((j : Finset.Iic i) -> Prod Action Rat))
    (h_action_policy_eq :
      Filter.Eventually
        (fun omega : Omega =>
          action omega (i + 1) =
            (policy i).action (pairState i (pairHistory omega)))
        (ae (mu.trim (F.le i))))
    (h_reward_map_eq_actual_action :
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega Rat mOmega inferInstance
            (fun y : Omega => reward y (i + 1))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ (F i)
              omega) =
          RewardKernel.selectedMeasure rewardKernel
            (pairContext i (pairHistory omega))
            (action omega (i + 1)))
        (ae (mu.trim (F.le i)))) :
    Filter.Eventually
      (fun omega : Omega =>
        @Measure.map Omega Rat mOmega inferInstance
          (fun y : Omega => reward y (i + 1))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ (F i)
            omega) =
        RewardKernel.selectedMeasure rewardKernel
          (pairContext i (pairHistory omega))
          ((policy i).action (pairState i (pairHistory omega))))
      (ae (mu.trim (F.le i))) := by
  filter_upwards [h_reward_map_eq_actual_action, h_action_policy_eq] with
    omega h_reward h_action
  simpa [h_action] using h_reward

/--
Actual-action pair-law marginalization for the reward-coordinate route.

Future trajectory-law work may identify, under the conditional kernel, the
pair `(actual next action, next reward)` as a fixed-action product of the
selected reward law.  Mapping that pair law through `Prod.snd` gives the
actual-action reward-coordinate map law consumed by the generated-action
route below.
-/
theorem reward_condExpKernel_map_eq_selected_actual_action_of_pair_map_eq
    {Omega : Type u} {Context : Type v} {Action : Type x}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (F : Filtration Nat mOmega)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (pairContext :
      (n : Nat) -> ((j : Finset.Iic n) -> Prod Action Rat) -> Context)
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Rat)
    (i : Nat)
    (pairHistory : Omega -> ((j : Finset.Iic i) -> Prod Action Rat))
    (h_reward_next :
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega (i + 1)))
    (h_pair_map_eq_actual_action :
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega (Prod Action Rat) mOmega inferInstance
            (fun y : Omega => (action omega (i + 1), reward y (i + 1)))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ (F i)
              omega) =
          Measure.map
            (Prod.mk (action omega (i + 1)))
            (RewardKernel.selectedMeasure rewardKernel
              (pairContext i (pairHistory omega))
              (action omega (i + 1))))
        (ae (mu.trim (F.le i)))) :
    Filter.Eventually
      (fun omega : Omega =>
        @Measure.map Omega Rat mOmega inferInstance
          (fun y : Omega => reward y (i + 1))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ (F i)
            omega) =
        RewardKernel.selectedMeasure rewardKernel
          (pairContext i (pairHistory omega))
          (action omega (i + 1)))
      (ae (mu.trim (F.le i))) := by
  filter_upwards [h_pair_map_eq_actual_action] with omega h_pair
  let condKernel : Measure Omega :=
    @ProbabilityTheory.condExpKernel Omega mOmega _ mu _ (F i) omega
  let selectedReward : Measure Rat :=
    RewardKernel.selectedMeasure rewardKernel
      (pairContext i (pairHistory omega)) (action omega (i + 1))
  let actualPair : Omega -> Prod Action Rat :=
    fun y : Omega => (action omega (i + 1), reward y (i + 1))
  have h_actualPair_meas : Measurable actualPair := by
    have h_action_const :
        Measurable (fun _y : Omega => action omega (i + 1)) := measurable_const
    exact h_action_const.prod h_reward_next
  have h_left :
      Measure.map Prod.snd (Measure.map actualPair condKernel) =
        @Measure.map Omega Rat mOmega inferInstance
          (fun y : Omega => reward y (i + 1)) condKernel := by
    rw [Measure.map_map measurable_snd h_actualPair_meas]
    rfl
  have h_prod_mk_meas :
      Measurable (Prod.mk (action omega (i + 1)) : Rat -> Prod Action Rat) := by
    fun_prop
  have h_right :
      Measure.map Prod.snd
          (Measure.map (Prod.mk (action omega (i + 1))) selectedReward) =
        selectedReward := by
    rw [Measure.map_map measurable_snd h_prod_mk_meas]
    simp [Function.comp_def, selectedReward]
  calc
    @Measure.map Omega Rat mOmega inferInstance
        (fun y : Omega => reward y (i + 1)) condKernel
        =
      Measure.map Prod.snd (Measure.map actualPair condKernel) := by
        exact h_left.symm
    _ =
      Measure.map Prod.snd
        (Measure.map (Prod.mk (action omega (i + 1))) selectedReward) := by
        simpa [condKernel, selectedReward, actualPair] using
          congrArg (Measure.map Prod.snd) h_pair
    _ = selectedReward := h_right

/--
Freeze the action coordinate in a random next-pair law.

A trajectory source may identify the conditional law of the fully random pair
`(action y (i+1), reward y (i+1))`, while the actual-action marginal route
expects the action coordinate frozen at the conditioning point `omega`.  Under
the shifted generated-action trace, both action coordinates are conditionally
equal to the same policy-selected action, so Mathlib's `Measure.map_congr`
transfers the random-pair map law to the frozen-action map law.
-/
theorem pair_condExpKernel_map_eq_frozen_actual_action_of_generatedActionTraceSucc_random_pair_map_eq
    {Omega : Type u} {Context : Type v} {State : Type w} {Action : Type x}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (pairContext :
      (n : Nat) -> ((j : Finset.Iic n) -> Prod Action Rat) -> Context)
    (pairState :
      (n : Nat) -> ((j : Finset.Iic n) -> Prod Action Rat) -> State)
    (hpairState : forall n : Nat, Measurable (pairState n))
    (defaultAction : Action)
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (i : Nat)
    (h_action_generated :
      action =
        Policy.generatedActionTraceSucc policy
          (fun n omega =>
            pairState n
              (History.finitePairHistoryOfTrace
                (action omega) (reward omega) n))
          defaultAction)
    (h_random_pair_map_eq_actual_action :
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega (Prod Action Rat) mOmega inferInstance
            (fun y : Omega => (action y (i + 1), reward y (i + 1)))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          Measure.map
            (Prod.mk (action omega (i + 1)))
            (RewardKernel.selectedMeasure rewardKernel
              (pairContext i
                (History.finitePairHistoryOfTrace
                  (action omega) (reward omega) i))
              (action omega (i + 1))))
        (ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.Eventually
      (fun omega : Omega =>
        @Measure.map Omega (Prod Action Rat) mOmega inferInstance
          (fun y : Omega => (action omega (i + 1), reward y (i + 1)))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
            ((History.historyFiltrationSucc action reward haction hreward) i)
            omega) =
        Measure.map
          (Prod.mk (action omega (i + 1)))
          (RewardKernel.selectedMeasure rewardKernel
            (pairContext i
              (History.finitePairHistoryOfTrace
                (action omega) (reward omega) i))
            (action omega (i + 1))))
      (ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i))) := by
  let F : Filtration Nat mOmega :=
    History.historyFiltrationSucc action reward haction hreward
  let pairHistory : Omega -> ((j : Finset.Iic i) -> Prod Action Rat) :=
    fun omega : Omega =>
      History.finitePairHistoryOfTrace (action omega) (reward omega) i
  have h_action_ae_eq_policy :
      Filter.Eventually
        (fun omega : Omega =>
          Filter.EventuallyEq
            (ae (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ (F i)
              omega))
            (fun y : Omega => action y (i + 1))
            (fun _y : Omega =>
              (policy i).action (pairState i (pairHistory omega))))
        (ae (mu.trim (F.le i))) := by
    simpa [F, pairHistory] using
      action_condExpKernel_ae_eq_policy_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc
        (mu := mu)
        (policy := policy)
        (pairState := pairState)
        (hpairState := hpairState)
        (defaultAction := defaultAction)
        (action := action)
        (reward := reward)
        (haction := haction)
        (hreward := hreward)
        (i := i)
        h_action_generated
  have h_action_policy_eq :
      Filter.Eventually
        (fun omega : Omega =>
          action omega (i + 1) =
            (policy i).action (pairState i (pairHistory omega)))
        (ae (mu.trim (F.le i))) := by
    exact Filter.Eventually.of_forall (fun omega => by
      have h_point := congrFun (congrFun h_action_generated omega) (i + 1)
      simpa [F, pairHistory, Policy.generatedActionTraceSucc] using h_point)
  filter_upwards
    [h_random_pair_map_eq_actual_action, h_action_ae_eq_policy,
      h_action_policy_eq]
    with omega h_random h_action_ae h_action_point
  let condKernel : Measure Omega :=
    @ProbabilityTheory.condExpKernel Omega mOmega _ mu _ (F i) omega
  let randomPair : Omega -> Prod Action Rat :=
    fun y : Omega => (action y (i + 1), reward y (i + 1))
  let frozenPair : Omega -> Prod Action Rat :=
    fun y : Omega => (action omega (i + 1), reward y (i + 1))
  have h_pair_ae :
      Filter.EventuallyEq (ae condKernel) randomPair frozenPair := by
    filter_upwards [h_action_ae] with y hy
    simp [randomPair, frozenPair, h_action_point, hy]
  have h_random_to_frozen :
      Measure.map randomPair condKernel =
        Measure.map frozenPair condKernel := by
    exact Measure.map_congr h_pair_ae
  calc
    @Measure.map Omega (Prod Action Rat) mOmega inferInstance
        (fun y : Omega => (action omega (i + 1), reward y (i + 1)))
        (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
          ((History.historyFiltrationSucc action reward haction hreward) i)
          omega)
        =
      Measure.map frozenPair condKernel := by
        rfl
    _ = Measure.map randomPair condKernel := h_random_to_frozen.symm
    _ =
      Measure.map
        (Prod.mk (action omega (i + 1)))
        (RewardKernel.selectedMeasure rewardKernel
          (pairContext i
            (History.finitePairHistoryOfTrace
              (action omega) (reward omega) i))
          (action omega (i + 1))) := by
        simpa [F, pairHistory, condKernel, randomPair] using h_random

/--
Random next-pair source law in canonical history-step-kernel form.

This rewrites a generated-action random next-pair law whose right side is
stated as `Measure.map (Prod.mk actualAction) selectedMeasure` into the
standard `RewardKernel.actionRewardHistoryStepKernelFamily` form consumed by
the pair-law route.  It is a law-shape adapter; the random next-pair law
itself remains an explicit hypothesis.
-/
theorem actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc_random_pair_map_eq_actual_action
    {Omega : Type u} {Context : Type v} {State : Type w} {Action : Type x}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (pairContext :
      (n : Nat) -> ((j : Finset.Iic n) -> Prod Action Rat) -> Context)
    (pairState :
      (n : Nat) -> ((j : Finset.Iic n) -> Prod Action Rat) -> State)
    (hpairContext : forall n : Nat, Measurable (pairContext n))
    (hpairState : forall n : Nat, Measurable (pairState n))
    (defaultAction : Action)
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (i : Nat)
    (h_action_generated :
      action =
        Policy.generatedActionTraceSucc policy
          (fun n omega =>
            pairState n
              (History.finitePairHistoryOfTrace
                (action omega) (reward omega) n))
          defaultAction)
    (h_random_pair_map_eq_actual_action :
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega (Prod Action Rat) mOmega inferInstance
            (fun y : Omega => (action y (i + 1), reward y (i + 1)))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          Measure.map
            (Prod.mk (action omega (i + 1)))
            (RewardKernel.selectedMeasure rewardKernel
              (pairContext i
                (History.finitePairHistoryOfTrace
                  (action omega) (reward omega) i))
              (action omega (i + 1))))
        (ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.Eventually
      (fun omega : Omega =>
        @Measure.map Omega (Prod Action Rat) mOmega inferInstance
          (fun y : Omega => (action y (i + 1), reward y (i + 1)))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
            ((History.historyFiltrationSucc action reward haction hreward) i)
            omega) =
        RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
          pairContext pairState hpairContext hpairState i
          (History.finitePairHistoryOfTrace
            (action omega) (reward omega) i))
      (ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i))) := by
  have h_action_policy_eq :
      Filter.Eventually
        (fun omega : Omega =>
          action omega (i + 1) =
            (policy i).action
              (pairState i
                (History.finitePairHistoryOfTrace
                  (action omega) (reward omega) i)))
        (ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i))) := by
    exact Filter.Eventually.of_forall (fun omega => by
      have h_point := congrFun (congrFun h_action_generated omega) (i + 1)
      simpa [Policy.generatedActionTraceSucc] using h_point)
  filter_upwards [h_random_pair_map_eq_actual_action, h_action_policy_eq]
    with omega h_random h_action
  calc
    @Measure.map Omega (Prod Action Rat) mOmega inferInstance
        (fun y : Omega => (action y (i + 1), reward y (i + 1)))
        (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
          ((History.historyFiltrationSucc action reward haction hreward) i)
          omega)
        =
      Measure.map
        (Prod.mk (action omega (i + 1)))
        (RewardKernel.selectedMeasure rewardKernel
          (pairContext i
            (History.finitePairHistoryOfTrace
              (action omega) (reward omega) i))
          (action omega (i + 1))) := h_random
    _ =
      RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
        pairContext pairState hpairContext hpairState i
        (History.finitePairHistoryOfTrace
          (action omega) (reward omega) i) := by
      simpa [h_action] using
        (RewardKernel.actionRewardHistoryStepKernelFamily_apply_eq_map_prod_mk
          rewardKernel policy pairContext pairState hpairContext hpairState
          i
          (History.finitePairHistoryOfTrace
            (action omega) (reward omega) i)).symm

/--
Finite reward-history frozen-past specialization.

Once the finite reward history at time `i` is measurable with respect to
filtration level `F i`, the conditional-expectation kernel at that level
freezes the whole finite history trim-a.e.  This supplies the direct
`h_history_frozen` hypothesis needed by
`centeredReward_succ_frozenPast_ae_of_history_frozen`.
-/
theorem finiteRewardHistory_condExpKernel_frozen_of_measurable
    {Omega : Type u}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (F : Filtration Nat mOmega)
    (i : Nat)
    (history : Omega -> ((j : Finset.Iic i) -> Rat))
    (hhistory :
      @Measurable Omega ((j : Finset.Iic i) -> Rat)
        (F i) inferInstance history) :
    Filter.Eventually
      (fun omega : Omega =>
        history =ᵐ[
          ProbabilityTheory.condExpKernel
            (Ω := Omega) (mΩ := mOmega) mu (F i) omega]
          (fun _y : Omega => history omega))
      (ae (mu.trim (F.le i))) := by
  exact
    condExpKernel_ae_eq_const_of_countable_measurable
      (mu := mu)
      (mcond := F i)
      (hm := F.le i)
      (Y := history)
      hhistory

/--
Coordinate-measurability hookup for finite reward histories.

If every coordinate in the finite reward prefix is measurable at filtration
level `F i`, the whole `finiteRewardHistoryOfTrace` object is measurable and
therefore frozen by the conditional-expectation kernel.  This is still only a
measurability bridge; it does not identify the conditional kernel with a
trajectory/history-step reward law.
-/
theorem finiteRewardHistory_condExpKernel_frozen_of_coordinate_measurable
    {Omega : Type u}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (F : Filtration Nat mOmega)
    (reward : Omega -> RewardTrace Rat)
    (i : Nat)
    (hreward :
      forall j : Finset.Iic i,
        @Measurable Omega Rat (F i) inferInstance
          (fun omega : Omega => reward omega j.1)) :
    Filter.Eventually
      (fun omega : Omega =>
        Filter.EventuallyEq
          (ae
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ (F i) omega))
          (fun y : Omega =>
            History.finiteRewardHistoryOfTrace (reward y) i)
          (fun _y : Omega =>
            History.finiteRewardHistoryOfTrace (reward omega) i))
      (ae (mu.trim (F.le i))) := by
  refine
    finiteRewardHistory_condExpKernel_frozen_of_measurable
      (mu := mu)
      (F := F)
      (i := i)
      (history := fun omega : Omega =>
        History.finiteRewardHistoryOfTrace (reward omega) i)
      ?_
  letI : MeasurableSpace Omega := F i
  exact measurable_pi_lambda _ (fun j : Finset.Iic i => hreward j)

/--
Generated-history-filtration specialization of finite reward-history freezing.

For the shifted history filtration `historyFiltrationSucc`, all reward
coordinates up to `i` are visible at level `i`, so the finite reward history
prefix is frozen trim-a.e. under its conditional-expectation kernel.  This
closes the concrete finite-history measurability side of the frozen-past route;
the remaining missing leaf is the reward-law/trajectory-law identification.
-/
theorem finiteRewardHistory_condExpKernel_frozen_historyFiltrationSucc
    {Omega : Type u} {Action : Type v}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (i : Nat) :
    Filter.Eventually
      (fun omega : Omega =>
        Filter.EventuallyEq
          (ae
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega))
          (fun y : Omega =>
            History.finiteRewardHistoryOfTrace (reward y) i)
          (fun _y : Omega =>
            History.finiteRewardHistoryOfTrace (reward omega) i))
      (ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i))) := by
  refine
    finiteRewardHistory_condExpKernel_frozen_of_coordinate_measurable
      (mu := mu)
      (F := History.historyFiltrationSucc action reward haction hreward)
      (reward := reward)
      (i := i)
      ?_
  intro j
  simpa [History.historyFiltrationSucc_apply] using
    (History.measurable_reward_mem_historyFiltration_of_lt
      action reward haction hreward
      (Nat.lt_succ_of_le (Finset.mem_Iic.mp j.2)))

/--
Finite action/reward pair-history frozen-past specialization.

This is the pair-coordinate companion to
`finiteRewardHistory_condExpKernel_frozen_of_measurable`.  It needs a
countable action space because the frozen object contains action coordinates.
-/
theorem finitePairHistory_condExpKernel_frozen_of_measurable
    {Omega : Type u} {Action : Type v}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (F : Filtration Nat mOmega)
    (i : Nat)
    (history : Omega -> ((j : Finset.Iic i) -> Prod Action Rat))
    (hhistory :
      @Measurable Omega ((j : Finset.Iic i) -> Prod Action Rat)
        (F i) inferInstance history) :
    Filter.Eventually
      (fun omega : Omega =>
        Filter.EventuallyEq
          (ae
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ (F i) omega))
          history
          (fun _y : Omega => history omega))
      (ae (mu.trim (F.le i))) := by
  exact
    condExpKernel_ae_eq_const_of_countable_measurable
      (mu := mu)
      (mcond := F i)
      (hm := F.le i)
      (Y := history)
      hhistory

/--
Coordinate-measurability hookup for finite action/reward pair histories.

If every action and reward coordinate in the finite pair prefix is measurable
at filtration level `F i`, the whole `finitePairHistoryOfTrace` object is
measurable and therefore frozen under the conditional-expectation kernel.
-/
theorem finitePairHistory_condExpKernel_frozen_of_coordinate_measurable
    {Omega : Type u} {Action : Type v}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (F : Filtration Nat mOmega)
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Rat)
    (i : Nat)
    (haction :
      forall j : Finset.Iic i,
        @Measurable Omega Action (F i) inferInstance
          (fun omega : Omega => action omega j.1))
    (hreward :
      forall j : Finset.Iic i,
        @Measurable Omega Rat (F i) inferInstance
          (fun omega : Omega => reward omega j.1)) :
    Filter.Eventually
      (fun omega : Omega =>
        Filter.EventuallyEq
          (ae
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ (F i) omega))
          (fun y : Omega =>
            History.finitePairHistoryOfTrace (action y) (reward y) i)
          (fun _y : Omega =>
            History.finitePairHistoryOfTrace (action omega) (reward omega) i))
      (ae (mu.trim (F.le i))) := by
  refine
    finitePairHistory_condExpKernel_frozen_of_measurable
      (mu := mu)
      (F := F)
      (i := i)
      (history := fun omega : Omega =>
        History.finitePairHistoryOfTrace (action omega) (reward omega) i)
      ?_
  letI : MeasurableSpace Omega := F i
  exact measurable_pi_lambda _ (fun j : Finset.Iic i =>
    (haction j).prod (hreward j))

/--
Generated-history-filtration specialization of finite pair-history freezing.

For `History.historyFiltrationSucc`, all action and reward coordinates up to
`i` are visible at level `i`, so the finite `(Action, Reward)` pair prefix is
frozen trim-a.e. under its conditional-expectation kernel.  This is a frozen
past hook for future `partialTraj`/`condExpKernel` pair-law identification; it
does not prove that law.
-/
theorem finitePairHistory_condExpKernel_frozen_historyFiltrationSucc
    {Omega : Type u} {Action : Type v}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (i : Nat) :
    Filter.Eventually
      (fun omega : Omega =>
        Filter.EventuallyEq
          (ae
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega))
          (fun y : Omega =>
            History.finitePairHistoryOfTrace (action y) (reward y) i)
          (fun _y : Omega =>
            History.finitePairHistoryOfTrace (action omega) (reward omega) i))
      (ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i))) := by
  refine
    finitePairHistory_condExpKernel_frozen_of_coordinate_measurable
      (mu := mu)
      (F := History.historyFiltrationSucc action reward haction hreward)
      (action := action)
      (reward := reward)
      (i := i)
      ?_
      ?_
  · intro j
    simpa [History.historyFiltrationSucc_apply] using
      (History.measurable_action_mem_historyFiltration_of_lt
        action reward haction hreward
        (Nat.lt_succ_of_le (Finset.mem_Iic.mp j.2)))
  · intro j
    simpa [History.historyFiltrationSucc_apply] using
      (History.measurable_reward_mem_historyFiltration_of_lt
        action reward haction hreward
        (Nat.lt_succ_of_le (Finset.mem_Iic.mp j.2)))

/--
Successor finite-pair trace decomposition under any frozen-prefix hypothesis.

If the old finite pair prefix is a.e. frozen at `omega`, then the full
`i + 1` prefix is a.e. the deterministic successor extension of that frozen
prefix by the random next `(Action, Reward)` pair.
-/
theorem finitePairHistory_succ_ae_eq_extend_of_pairHistory_frozen
    {Omega : Type u} {Action : Type v}
    [mOmega : MeasurableSpace Omega]
    (nu : Measure Omega)
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Rat)
    (i : Nat) (omega : Omega)
    (h_pair_history_frozen :
      Filter.EventuallyEq (ae nu)
        (fun y : Omega =>
          History.finitePairHistoryOfTrace (action y) (reward y) i)
        (fun _y : Omega =>
          History.finitePairHistoryOfTrace (action omega) (reward omega) i)) :
    Filter.EventuallyEq (ae nu)
      (fun y : Omega =>
        History.finitePairHistoryOfTrace (action y) (reward y) (i + 1))
      (fun y : Omega =>
        History.extendPairHistorySucc
          (History.finitePairHistoryOfTrace (action omega) (reward omega) i)
          (action y (i + 1), reward y (i + 1))) := by
  filter_upwards [h_pair_history_frozen] with y h_frozen
  calc
    History.finitePairHistoryOfTrace (action y) (reward y) (i + 1) =
        History.extendPairHistorySucc
          (History.finitePairHistoryOfTrace (action y) (reward y) i)
          (action y (i + 1), reward y (i + 1)) := by
          rw [History.finitePairHistoryOfTrace_succ]
    _ =
        History.extendPairHistorySucc
          (History.finitePairHistoryOfTrace (action omega) (reward omega) i)
          (action y (i + 1), reward y (i + 1)) := by
          rw [h_frozen]

/--
Generated-history conditional-kernel successor decomposition for pair traces.

This packages the previous frozen pair-prefix theorem into the concrete
`History.historyFiltrationSucc` conditional kernel.  It is not a joint law
identification; it only rewrites the random `i + 1` pair trace into a frozen
prefix plus random next pair under the conditional kernel.
-/
theorem finitePairHistory_succ_condExpKernel_ae_eq_extend_historyFiltrationSucc
    {Omega : Type u} {Action : Type v}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (i : Nat) :
    Filter.Eventually
      (fun omega : Omega =>
        Filter.EventuallyEq
          (ae
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega))
          (fun y : Omega =>
            History.finitePairHistoryOfTrace (action y) (reward y) (i + 1))
          (fun y : Omega =>
            History.extendPairHistorySucc
              (History.finitePairHistoryOfTrace (action omega) (reward omega) i)
              (action y (i + 1), reward y (i + 1))))
      (ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i))) := by
  have h_frozen :=
    finitePairHistory_condExpKernel_frozen_historyFiltrationSucc
      (mu := mu)
      (action := action)
      (reward := reward)
      (haction := haction)
      (hreward := hreward)
      (i := i)
  filter_upwards [h_frozen] with omega h_pair_history_frozen
  exact
    finitePairHistory_succ_ae_eq_extend_of_pairHistory_frozen
      (nu :=
        @ProbabilityTheory.condExpKernel Omega mOmega _ mu _
          ((History.historyFiltrationSucc action reward haction hreward) i)
          omega)
      (action := action)
      (reward := reward)
      (i := i)
      (omega := omega)
      h_pair_history_frozen

/--
Pushforward form of the generated-history successor decomposition.

The previous theorem is an a.e. equality under the conditional kernel.  This
lemma upgrades it via Mathlib's `Measure.map_congr`, so later route cards can
state the remaining trajectory-law input against the deterministic
`extendPairHistorySucc` map instead of the full `i + 1` trace restriction.
-/
theorem finitePairHistory_succ_condExpKernel_map_eq_extend_historyFiltrationSucc
    {Omega : Type u} {Action : Type v}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (i : Nat) :
    Filter.Eventually
      (fun omega : Omega =>
        @Measure.map Omega ((j : Finset.Iic (i + 1)) -> Prod Action Rat)
          mOmega inferInstance
          (fun y : Omega =>
            History.finitePairHistoryOfTrace (action y) (reward y) (i + 1))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
            ((History.historyFiltrationSucc action reward haction hreward) i)
            omega) =
        @Measure.map Omega ((j : Finset.Iic (i + 1)) -> Prod Action Rat)
          mOmega inferInstance
          (fun y : Omega =>
            History.extendPairHistorySucc
              (History.finitePairHistoryOfTrace
                (action omega) (reward omega) i)
              (action y (i + 1), reward y (i + 1)))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
            ((History.historyFiltrationSucc action reward haction hreward) i)
            omega))
      (ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i))) := by
  have h_ae :=
    finitePairHistory_succ_condExpKernel_ae_eq_extend_historyFiltrationSucc
      (mu := mu)
      (action := action)
      (reward := reward)
      (haction := haction)
      (hreward := hreward)
      (i := i)
  filter_upwards [h_ae] with omega h_eq
  exact Measure.map_congr h_eq

/--
Frozen-history bridge for the succ-indexed map-law route.

If the finite reward history is already frozen under the conditional kernel,
then the history-selected context/action mean in the centered next-reward
variable is frozen as well.  This is the deterministic part of the
`h_kernel_X_eq` side condition consumed by the map-law conditional-expectation
bridge; it deliberately does not prove that the history itself is frozen.
-/
theorem centeredReward_succ_frozenPast_ae_of_history_frozen
    {Omega : Type u} {Context : Type v} {State : Type w} {Action : Type x}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace State] [MeasurableSpace Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (F : Filtration Nat mOmega)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (mean : Context -> Action -> Rat)
    (reward : Omega -> RewardTrace Rat)
    (i : Nat)
    (history : Omega -> ((j : Finset.Iic i) -> Rat))
    (h_history_frozen :
      Filter.Eventually
        (fun omega : Omega =>
          history =ᵐ[
            ProbabilityTheory.condExpKernel
              (Ω := Omega) (mΩ := mOmega) mu (F i) omega]
            (fun _y : Omega => history omega))
        (ae (mu.trim (F.le i)))) :
    Filter.Eventually
      (fun omega : Omega =>
        (fun y : Omega =>
          (((reward y (i + 1) -
            mean (context i (history y))
              ((policy i).action (state i (history y))) : Rat) :
                Real))) =ᵐ[
          ProbabilityTheory.condExpKernel
            (Ω := Omega) (mΩ := mOmega) mu (F i) omega]
        (fun y : Omega =>
          (((reward y (i + 1) -
            mean (context i (history omega))
              ((policy i).action (state i (history omega))) : Rat) :
                Real))))
      (ae (mu.trim (F.le i))) := by
  filter_upwards [h_history_frozen] with omega hhistory
  filter_upwards [hhistory] with y hy
  simp [hy]

/--
Conditional sub-Gaussian map-law consumer with the frozen-past side condition
discharged from prefix coordinate measurability.

The remaining structural input is the reward-coordinate pushforward identity
from `condExpKernel` to the history-step reward kernel.  Exponential
integrability, ambient measurability of the centered reward, and the
deterministic variance-proxy upper bound remain explicit regularity contracts.
-/
theorem centeredReward_succ_hasCondSubgaussianMGF_of_historyStepKernelFamily_condExpKernel_map_eq_of_coordinate_measurable
    {Omega : Type u} {Context : Type v} {State : Type w} {Action : Type x}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (F : Filtration Nat mOmega)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (law :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (reward : Omega -> RewardTrace Rat)
    (i : Nat)
    (c : NNReal)
    (h_reward :
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega (i + 1)))
    (h_prefix_meas :
      forall j : Finset.Iic i,
        @Measurable Omega Rat (F i) inferInstance
          (fun omega : Omega => reward omega j.1))
    (h_centered_meas :
      @Measurable Omega Real mOmega inferInstance
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))))
    (h_integrable_exp :
      forall t : Real,
        Integrable
          (fun omega : Omega =>
            Real.exp (t *
              (((reward omega (i + 1) -
                mean
                  (context i
                    (History.finiteRewardHistoryOfTrace (reward omega) i))
                  ((policy i).action
                    (state i
                      (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                    Rat) : Real)))) mu)
    (h_kernel_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega Rat mOmega inferInstance
            (fun y : Omega => reward y (i + 1))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ (F i)
              omega) =
          RewardKernel.historyStepKernelFamily rewardKernel policy context state
            hcontext hstate i
            (History.finiteRewardHistoryOfTrace (reward omega) i))
        (ae (mu.trim (F.le i))))
    (h_variance_le :
      Filter.Eventually
        (fun omega : Omega =>
          varianceProxy
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) <=
            c)
        (ae (mu.trim (F.le i)))) :
    ProbabilityTheory.HasCondSubgaussianMGF (F i) (F.le i)
      (fun omega : Omega =>
        (((reward omega (i + 1) -
          mean
            (context i
              (History.finiteRewardHistoryOfTrace (reward omega) i))
            ((policy i).action
              (state i
                (History.finiteRewardHistoryOfTrace (reward omega) i))) :
            Rat) : Real)))
      c mu := by
  let history : Omega -> ((j : Finset.Iic i) -> Rat) :=
    fun omega : Omega => History.finiteRewardHistoryOfTrace (reward omega) i
  have h_history_frozen :
      Filter.Eventually
        (fun omega : Omega =>
          Filter.EventuallyEq
            (ae
              (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ (F i)
                omega))
            history
            (fun _y : Omega => history omega))
        (ae (mu.trim (F.le i))) := by
    simpa [history] using
      finiteRewardHistory_condExpKernel_frozen_of_coordinate_measurable
        (mu := mu)
        (F := F)
        (reward := reward)
        (i := i)
        h_prefix_meas
  have h_kernel_X_eq :
      Filter.Eventually
        (fun omega : Omega =>
          Filter.EventuallyEq
            (ae
              (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ (F i)
                omega))
            (fun y : Omega =>
              (((reward y (i + 1) -
                mean (context i (history y))
                  ((policy i).action (state i (history y))) : Rat) :
                    Real)))
            (fun y : Omega =>
              (((reward y (i + 1) -
                mean (context i (history omega))
                  ((policy i).action (state i (history omega))) : Rat) :
                    Real))))
        (ae (mu.trim (F.le i))) := by
    exact
      centeredReward_succ_frozenPast_ae_of_history_frozen
        (mu := mu)
        (F := F)
        (policy := policy)
        (context := context)
        (state := state)
        (mean := mean)
        (reward := reward)
        (i := i)
        (history := history)
        h_history_frozen
  exact
    centeredReward_succ_hasCondSubgaussianMGF_of_historyStepKernelFamily_condExpKernel_map_eq
      (mu := mu)
      (F := F)
      (rewardKernel := rewardKernel)
      (policy := policy)
      (context := context)
      (state := state)
      (hcontext := hcontext)
      (hstate := hstate)
      (mean := mean)
      (varianceProxy := varianceProxy)
      (law := law)
      (reward := reward)
      (i := i)
      (history := history)
      (c := c)
      h_reward
      (by simpa [history] using h_centered_meas)
      (by simpa [history] using h_integrable_exp)
      (by simpa [history] using h_kernel_map_eq)
      h_kernel_X_eq
      (by simpa [history] using h_variance_le)

/--
Generated-history-filtration specialization of the conditional sub-Gaussian
map-law consumer.

At filtration level `History.historyFiltrationSucc ... i`, the reward prefix
up to `i` is visible by construction, so the coordinate-measurable consumer
applies directly.  The reward-coordinate pushforward identity and analytic
regularity contracts remain explicit.
-/
theorem centeredReward_succ_hasCondSubgaussianMGF_of_historyStepKernelFamily_condExpKernel_map_eq_historyFiltrationSucc
    {Omega : Type u} {Context : Type v} {State : Type w} {Action : Type x}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (law :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (i : Nat)
    (c : NNReal)
    (h_centered_meas :
      @Measurable Omega Real mOmega inferInstance
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))))
    (h_integrable_exp :
      forall t : Real,
        Integrable
          (fun omega : Omega =>
            Real.exp (t *
              (((reward omega (i + 1) -
                mean
                  (context i
                    (History.finiteRewardHistoryOfTrace (reward omega) i))
                  ((policy i).action
                    (state i
                      (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                    Rat) : Real)))) mu)
    (h_kernel_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega Rat mOmega inferInstance
            (fun y : Omega => reward y (i + 1))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          RewardKernel.historyStepKernelFamily rewardKernel policy context state
            hcontext hstate i
            (History.finiteRewardHistoryOfTrace (reward omega) i))
        (ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i))))
    (h_variance_le :
      Filter.Eventually
        (fun omega : Omega =>
          varianceProxy
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) <=
            c)
        (ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    ProbabilityTheory.HasCondSubgaussianMGF
      ((History.historyFiltrationSucc action reward haction hreward) i)
      ((History.historyFiltrationSucc action reward haction hreward).le i)
      (fun omega : Omega =>
        (((reward omega (i + 1) -
          mean
            (context i
              (History.finiteRewardHistoryOfTrace (reward omega) i))
            ((policy i).action
              (state i
                (History.finiteRewardHistoryOfTrace (reward omega) i))) :
            Rat) : Real)))
      c mu := by
  refine
    centeredReward_succ_hasCondSubgaussianMGF_of_historyStepKernelFamily_condExpKernel_map_eq_of_coordinate_measurable
      (mu := mu)
      (F := History.historyFiltrationSucc action reward haction hreward)
      (rewardKernel := rewardKernel)
      (policy := policy)
      (context := context)
      (state := state)
      (hcontext := hcontext)
      (hstate := hstate)
      (mean := mean)
      (varianceProxy := varianceProxy)
      (law := law)
      (reward := reward)
      (i := i)
      (c := c)
      (h_reward := hreward (i + 1))
      ?_
      h_centered_meas
      h_integrable_exp
      h_kernel_map_eq
      h_variance_le
  intro j
  simpa [History.historyFiltrationSucc_apply] using
    (History.measurable_reward_mem_historyFiltration_of_lt
      action reward haction hreward
      (Nat.lt_succ_of_le (Finset.mem_Iic.mp j.2)))

/--
Succ-indexed selected-reward specialization of the map-law consumer.

The `h_kernel_map_eq` hypothesis is the reward-coordinate pushforward form of
the future trajectory-law identification.  The `h_kernel_X_eq` hypothesis is
the matching frozen-past condition for the centered variable.
-/
theorem centeredReward_succ_condExp_eq_zero_of_historyStepKernelFamily_condExpKernel_map_eq
    {Omega : Type u} {Context : Type v} {State : Type w} {Action : Type x}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (F : Filtration Nat mOmega)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Context × Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (law :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (reward : Omega -> RewardTrace Rat)
    (i : Nat)
    (history : Omega -> ((j : Finset.Iic i) -> Rat))
    (h_reward :
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega (i + 1)))
    (h_integrable :
      Integrable
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean (context i (history omega))
              ((policy i).action (state i (history omega))) : Rat) :
                Real))) mu)
    (h_kernel_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega Rat mOmega inferInstance
            (fun y : Omega => reward y (i + 1))
            (ProbabilityTheory.condExpKernel
              (Ω := Omega) (mΩ := mOmega) mu (F i) omega) =
          RewardKernel.historyStepKernelFamily rewardKernel policy context state
            hcontext hstate i (history omega))
        (ae (mu.trim (F.le i))))
    (h_kernel_X_eq :
      Filter.Eventually
        (fun omega : Omega =>
          (fun y : Omega =>
            (((reward y (i + 1) -
              mean (context i (history y))
                ((policy i).action (state i (history y))) : Rat) :
                  Real))) =ᵐ[
            ProbabilityTheory.condExpKernel
              (Ω := Omega) (mΩ := mOmega) mu (F i) omega]
            (fun y : Omega =>
              (((reward y (i + 1) -
                mean (context i (history omega))
                  ((policy i).action (state i (history omega))) : Rat) :
                    Real))))
        (ae (mu.trim (F.le i)))) :
    Filter.EventuallyEq (ae mu)
      (@condExp Omega Real (F i) mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean (context i (history omega))
              ((policy i).action (state i (history omega))) : Rat) :
                Real))))
      (fun _omega : Omega => (0 : Real)) := by
  exact
    condExp_eq_zero_of_condExpKernel_map_eq_historyStepKernel_centeredReward
      (mu := mu)
      (mcond := F i)
      (hm := F.le i)
      (rewardKernel := rewardKernel)
      (policy := policy)
      (context := context)
      (state := state)
      (hcontext := hcontext)
      (hstate := hstate)
      (mean := mean)
      (varianceProxy := varianceProxy)
      (law := law)
      (n := i)
      (history := history)
      (nextReward := fun omega : Omega => reward omega (i + 1))
      (X := fun omega : Omega =>
        (((reward omega (i + 1) -
          mean (context i (history omega))
            ((policy i).action (state i (history omega))) : Rat) :
              Real)))
      h_reward
      h_integrable
      h_kernel_map_eq
      h_kernel_X_eq

/--
Map-law consumer with the frozen-past side condition discharged from prefix
coordinate measurability.

The remaining structural input is still `h_kernel_map_eq`: the
reward-coordinate pushforward identity from `condExpKernel` to the
history-step reward kernel.  This theorem only removes the separate
`h_kernel_X_eq` obligation by proving finite-history frozen-past from
coordinate measurability at `F i`.
-/
theorem centeredReward_succ_condExp_eq_zero_of_historyStepKernelFamily_condExpKernel_map_eq_of_coordinate_measurable
    {Omega : Type u} {Context : Type v} {State : Type w} {Action : Type x}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (F : Filtration Nat mOmega)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (law :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (reward : Omega -> RewardTrace Rat)
    (i : Nat)
    (h_reward :
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega (i + 1)))
    (h_prefix_meas :
      forall j : Finset.Iic i,
        @Measurable Omega Rat (F i) inferInstance
          (fun omega : Omega => reward omega j.1))
    (h_integrable :
      Integrable
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))) mu)
    (h_kernel_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega Rat mOmega inferInstance
            (fun y : Omega => reward y (i + 1))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ (F i)
              omega) =
          RewardKernel.historyStepKernelFamily rewardKernel policy context state
            hcontext hstate i
            (History.finiteRewardHistoryOfTrace (reward omega) i))
        (ae (mu.trim (F.le i)))) :
    Filter.EventuallyEq (ae mu)
      (@condExp Omega Real (F i) mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))))
      (fun _omega : Omega => (0 : Real)) := by
  let history : Omega -> ((j : Finset.Iic i) -> Rat) :=
    fun omega : Omega => History.finiteRewardHistoryOfTrace (reward omega) i
  have h_history_frozen :
      Filter.Eventually
        (fun omega : Omega =>
          Filter.EventuallyEq
            (ae
              (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ (F i)
                omega))
            history
            (fun _y : Omega => history omega))
        (ae (mu.trim (F.le i))) := by
    simpa [history] using
      finiteRewardHistory_condExpKernel_frozen_of_coordinate_measurable
        (mu := mu)
        (F := F)
        (reward := reward)
        (i := i)
        h_prefix_meas
  have h_kernel_X_eq :
      Filter.Eventually
        (fun omega : Omega =>
          Filter.EventuallyEq
            (ae
              (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ (F i)
                omega))
            (fun y : Omega =>
              (((reward y (i + 1) -
                mean (context i (history y))
                  ((policy i).action (state i (history y))) : Rat) :
                    Real)))
            (fun y : Omega =>
              (((reward y (i + 1) -
                mean (context i (history omega))
                  ((policy i).action (state i (history omega))) : Rat) :
                    Real))))
        (ae (mu.trim (F.le i))) := by
    exact
      centeredReward_succ_frozenPast_ae_of_history_frozen
        (mu := mu)
        (F := F)
        (policy := policy)
        (context := context)
        (state := state)
        (mean := mean)
        (reward := reward)
        (i := i)
        (history := history)
        h_history_frozen
  exact
    centeredReward_succ_condExp_eq_zero_of_historyStepKernelFamily_condExpKernel_map_eq
      (mu := mu)
      (F := F)
      (rewardKernel := rewardKernel)
      (policy := policy)
      (context := context)
      (state := state)
      (hcontext := hcontext)
      (hstate := hstate)
      (mean := mean)
      (varianceProxy := varianceProxy)
      (law := law)
      (reward := reward)
      (i := i)
      (history := history)
      h_reward
      h_integrable
      (by simpa [history] using h_kernel_map_eq)
      h_kernel_X_eq

/--
Generated-history-filtration specialization of the map-law consumer.

At filtration level `History.historyFiltrationSucc ... i`, the reward prefix
up to `i` is visible by construction, so the preceding coordinate-measurable
consumer applies directly.  The reward-coordinate pushforward identity remains
an explicit assumption.
-/
theorem centeredReward_succ_condExp_eq_zero_of_historyStepKernelFamily_condExpKernel_map_eq_historyFiltrationSucc
    {Omega : Type u} {Context : Type v} {State : Type w} {Action : Type x}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (law :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (i : Nat)
    (h_integrable :
      Integrable
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))) mu)
    (h_kernel_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega Rat mOmega inferInstance
            (fun y : Omega => reward y (i + 1))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          RewardKernel.historyStepKernelFamily rewardKernel policy context state
            hcontext hstate i
            (History.finiteRewardHistoryOfTrace (reward omega) i))
        (ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.EventuallyEq (ae mu)
      (@condExp Omega Real
        ((History.historyFiltrationSucc action reward haction hreward) i)
        mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))))
      (fun _omega : Omega => (0 : Real)) := by
  refine
    centeredReward_succ_condExp_eq_zero_of_historyStepKernelFamily_condExpKernel_map_eq_of_coordinate_measurable
      (mu := mu)
      (F := History.historyFiltrationSucc action reward haction hreward)
      (rewardKernel := rewardKernel)
      (policy := policy)
      (context := context)
      (state := state)
      (hcontext := hcontext)
      (hstate := hstate)
      (mean := mean)
      (varianceProxy := varianceProxy)
      (law := law)
      (reward := reward)
      (i := i)
      (h_reward := hreward (i + 1))
      ?_
      h_integrable
      h_kernel_map_eq
  intro j
  simpa [History.historyFiltrationSucc_apply] using
    (History.measurable_reward_mem_historyFiltration_of_lt
      action reward haction hreward
      (Nat.lt_succ_of_le (Finset.mem_Iic.mp j.2)))

/--
Pair-law route into the map-law conditional mean-zero consumer.

If the conditional kernel has the correct next `(Action × Reward)` law, then
mapping both sides through `Prod.snd` gives the reward-coordinate law consumed
by the map-law conditional-expectation bridge.  This theorem still assumes the
pair-law identity; it only packages the marginalization step through
`RewardKernel.actionRewardHistoryStepKernelFamily_reward_map`.
-/
theorem centeredReward_succ_condExp_eq_zero_of_actionRewardHistoryStepKernelFamily_pair_map_eq_of_coordinate_measurable
    {Omega : Type u} {Context : Type v} {State : Type w} {Action : Type x}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (F : Filtration Nat mOmega)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (pairContext :
      (n : Nat) -> ((j : Finset.Iic n) -> Prod Action Rat) -> Context)
    (pairState :
      (n : Nat) -> ((j : Finset.Iic n) -> Prod Action Rat) -> State)
    (hpairContext : forall n : Nat, Measurable (pairContext n))
    (hpairState : forall n : Nat, Measurable (pairState n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (law :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Rat)
    (i : Nat)
    (pairHistory : Omega -> ((j : Finset.Iic i) -> Prod Action Rat))
    (h_action_next :
      @Measurable Omega Action mOmega inferInstance
        (fun omega : Omega => action omega (i + 1)))
    (h_reward_next :
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega (i + 1)))
    (h_prefix_meas :
      forall j : Finset.Iic i,
        @Measurable Omega Rat (F i) inferInstance
          (fun omega : Omega => reward omega j.1))
    (h_pair_context_eq :
      forall omega : Omega,
        pairContext i (pairHistory omega) =
          context i (History.finiteRewardHistoryOfTrace (reward omega) i))
    (h_pair_state_eq :
      forall omega : Omega,
        pairState i (pairHistory omega) =
          state i (History.finiteRewardHistoryOfTrace (reward omega) i))
    (h_integrable :
      Integrable
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))) mu)
    (h_kernel_pair_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega (Prod Action Rat) mOmega inferInstance
            (fun y : Omega => (action y (i + 1), reward y (i + 1)))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ (F i)
              omega) =
          RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
            pairContext pairState hpairContext hpairState i
            (pairHistory omega))
        (ae (mu.trim (F.le i)))) :
    Filter.EventuallyEq (ae mu)
      (@condExp Omega Real (F i) mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))))
      (fun _omega : Omega => (0 : Real)) := by
  have h_pair_next_meas :
      Measurable
        (fun y : Omega => (action y (i + 1), reward y (i + 1))) :=
    h_action_next.prod h_reward_next
  have h_kernel_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega Rat mOmega inferInstance
            (fun y : Omega => reward y (i + 1))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ (F i)
              omega) =
          RewardKernel.historyStepKernelFamily rewardKernel policy context state
            hcontext hstate i
            (History.finiteRewardHistoryOfTrace (reward omega) i))
        (ae (mu.trim (F.le i))) := by
    filter_upwards [h_kernel_pair_map_eq] with omega h_pair
    let condKernel : Measure Omega :=
      @ProbabilityTheory.condExpKernel Omega mOmega _ mu _ (F i) omega
    let nextPair : Omega -> Prod Action Rat :=
      fun y : Omega => (action y (i + 1), reward y (i + 1))
    have h_map_map :
        Measure.map Prod.snd (Measure.map nextPair condKernel) =
          Measure.map (fun y : Omega => reward y (i + 1)) condKernel := by
      rw [Measure.map_map measurable_snd h_pair_next_meas]
      rfl
    calc
      @Measure.map Omega Rat mOmega inferInstance
          (fun y : Omega => reward y (i + 1))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ (F i) omega)
          =
        Measure.map Prod.snd
          (@Measure.map Omega (Prod Action Rat) mOmega inferInstance
            (fun y : Omega => (action y (i + 1), reward y (i + 1)))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ (F i)
              omega)) := by
          simpa [condKernel, nextPair] using h_map_map.symm
      _ =
        Measure.map Prod.snd
          (RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
            pairContext pairState hpairContext hpairState i
            (pairHistory omega)) := by
          rw [h_pair]
      _ =
        RewardKernel.selectedMeasure rewardKernel
          (pairContext i (pairHistory omega))
          ((policy i).action (pairState i (pairHistory omega))) := by
          exact
            RewardKernel.actionRewardHistoryStepKernelFamily_reward_map
              rewardKernel policy pairContext pairState hpairContext hpairState
              i (pairHistory omega)
      _ =
        RewardKernel.historyStepKernelFamily rewardKernel policy context state
          hcontext hstate i
          (History.finiteRewardHistoryOfTrace (reward omega) i) := by
          rw [h_pair_context_eq omega, h_pair_state_eq omega]
          rfl
  exact
    centeredReward_succ_condExp_eq_zero_of_historyStepKernelFamily_condExpKernel_map_eq_of_coordinate_measurable
      (mu := mu)
      (F := F)
      (rewardKernel := rewardKernel)
      (policy := policy)
      (context := context)
      (state := state)
      (hcontext := hcontext)
      (hstate := hstate)
      (mean := mean)
      (varianceProxy := varianceProxy)
      (law := law)
      (reward := reward)
      (i := i)
      (h_reward := h_reward_next)
      h_prefix_meas
      h_integrable
      h_kernel_map_eq

/--
Generated-history-filtration specialization of the action/reward pair-law route.

At `History.historyFiltrationSucc ... i`, the next action/reward coordinates
are measurable in the ambient space and the reward prefix up to `i` is visible
at filtration level `i`.  Thus the coordinate-measurable pair-map consumer
applies directly.  The actual action/reward pair-law pushforward identity
remains an explicit assumption.
-/
theorem centeredReward_succ_condExp_eq_zero_of_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc
    {Omega : Type u} {Context : Type v} {State : Type w} {Action : Type x}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (pairContext :
      (n : Nat) -> ((j : Finset.Iic n) -> Prod Action Rat) -> Context)
    (pairState :
      (n : Nat) -> ((j : Finset.Iic n) -> Prod Action Rat) -> State)
    (hpairContext : forall n : Nat, Measurable (pairContext n))
    (hpairState : forall n : Nat, Measurable (pairState n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (law :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (i : Nat)
    (pairHistory : Omega -> ((j : Finset.Iic i) -> Prod Action Rat))
    (h_pair_context_eq :
      forall omega : Omega,
        pairContext i (pairHistory omega) =
          context i (History.finiteRewardHistoryOfTrace (reward omega) i))
    (h_pair_state_eq :
      forall omega : Omega,
        pairState i (pairHistory omega) =
          state i (History.finiteRewardHistoryOfTrace (reward omega) i))
    (h_integrable :
      Integrable
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))) mu)
    (h_kernel_pair_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega (Prod Action Rat) mOmega inferInstance
            (fun y : Omega => (action y (i + 1), reward y (i + 1)))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
            pairContext pairState hpairContext hpairState i
            (pairHistory omega))
        (ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.EventuallyEq (ae mu)
      (@condExp Omega Real
        ((History.historyFiltrationSucc action reward haction hreward) i)
        mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))))
      (fun _omega : Omega => (0 : Real)) := by
  refine
    centeredReward_succ_condExp_eq_zero_of_actionRewardHistoryStepKernelFamily_pair_map_eq_of_coordinate_measurable
      (mu := mu)
      (F := History.historyFiltrationSucc action reward haction hreward)
      (rewardKernel := rewardKernel)
      (policy := policy)
      (context := context)
      (state := state)
      (hcontext := hcontext)
      (hstate := hstate)
      (pairContext := pairContext)
      (pairState := pairState)
      (hpairContext := hpairContext)
      (hpairState := hpairState)
      (mean := mean)
      (varianceProxy := varianceProxy)
      (law := law)
      (action := action)
      (reward := reward)
      (i := i)
      (pairHistory := pairHistory)
      (h_action_next := haction (i + 1))
      (h_reward_next := hreward (i + 1))
      ?_
      h_pair_context_eq
      h_pair_state_eq
      h_integrable
      h_kernel_pair_map_eq
  intro j
  simpa [History.historyFiltrationSucc_apply] using
    (History.measurable_reward_mem_historyFiltration_of_lt
      action reward haction hreward
      (Nat.lt_succ_of_le (Finset.mem_Iic.mp j.2)))

/--
Generated-history pair-law route with the concrete trace pair-history.

This specializes the previous generated-history consumer to the finite
action/reward pair history obtained from the actual traces, and to context/state
extractors that read only the reward projection of that pair history.  It
removes the separate pair-history compatibility hypotheses; the remaining
structural assumption is exactly the generated-history `condExpKernel`
pushforward equality for the next `(Action, Reward)` pair.
-/
theorem centeredReward_succ_condExp_eq_zero_of_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_projected
    {Omega : Type u} {Context : Type v} {State : Type w} {Action : Type x}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (hpairContext :
      forall n : Nat,
        Measurable
          (fun history : (j : Finset.Iic n) -> Prod Action Rat =>
            context n (fun j : Finset.Iic n => (history j).2)))
    (hpairState :
      forall n : Nat,
        Measurable
          (fun history : (j : Finset.Iic n) -> Prod Action Rat =>
            state n (fun j : Finset.Iic n => (history j).2)))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (law :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (i : Nat)
    (h_integrable :
      Integrable
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))) mu)
    (h_kernel_pair_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega (Prod Action Rat) mOmega inferInstance
            (fun y : Omega => (action y (i + 1), reward y (i + 1)))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
            (fun n history =>
              context n (fun j : Finset.Iic n => (history j).2))
            (fun n history =>
              state n (fun j : Finset.Iic n => (history j).2))
            hpairContext hpairState i
            (fun j : Finset.Iic i =>
              (action omega j.1, reward omega j.1)))
        (ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.EventuallyEq (ae mu)
      (@condExp Omega Real
        ((History.historyFiltrationSucc action reward haction hreward) i)
        mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))))
      (fun _omega : Omega => (0 : Real)) := by
  refine
    centeredReward_succ_condExp_eq_zero_of_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc
      (mu := mu)
      (action := action)
      (rewardKernel := rewardKernel)
      (policy := policy)
      (context := context)
      (state := state)
      (hcontext := hcontext)
      (hstate := hstate)
      (pairContext := fun n history =>
        context n (fun j : Finset.Iic n => (history j).2))
      (pairState := fun n history =>
        state n (fun j : Finset.Iic n => (history j).2))
      (hpairContext := hpairContext)
      (hpairState := hpairState)
      (mean := mean)
      (varianceProxy := varianceProxy)
      (law := law)
      (reward := reward)
      (haction := haction)
      (hreward := hreward)
      (i := i)
      (pairHistory := fun omega : Omega =>
        fun j : Finset.Iic i => (action omega j.1, reward omega j.1))
      ?_
      ?_
      h_integrable
      h_kernel_pair_map_eq
  · intro omega
    rfl
  · intro omega
    rfl

/--
Projected trace-pair route with projection measurability supplied locally.

The remaining hypothesis is the concrete generated-history pair-law equality.
The reward-projection context/state measurability proofs are derived from the
original reward-history `context`/`state` measurability and
`History.measurable_pairHistoryRewardProjection`.
-/
theorem centeredReward_succ_condExp_eq_zero_of_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_projected_of_context_state_measurable
    {Omega : Type u} {Context : Type v} {State : Type w} {Action : Type x}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (law :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (i : Nat)
    (h_integrable :
      Integrable
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))) mu)
    (h_kernel_pair_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega (Prod Action Rat) mOmega inferInstance
            (fun y : Omega => (action y (i + 1), reward y (i + 1)))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
            (fun n history =>
              context n (History.pairHistoryRewardProjection history))
            (fun n history =>
              state n (History.pairHistoryRewardProjection history))
            (fun n : Nat =>
              (hcontext n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            (fun n : Nat =>
              (hstate n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            i
            (fun j : Finset.Iic i =>
              (action omega j.1, reward omega j.1)))
        (ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.EventuallyEq (ae mu)
      (@condExp Omega Real
        ((History.historyFiltrationSucc action reward haction hreward) i)
        mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))))
      (fun _omega : Omega => (0 : Real)) := by
  exact
    centeredReward_succ_condExp_eq_zero_of_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_projected
      (mu := mu)
      (action := action)
      (rewardKernel := rewardKernel)
      (policy := policy)
      (context := context)
      (state := state)
      (hcontext := hcontext)
      (hstate := hstate)
      (hpairContext := fun n : Nat =>
        (hcontext n).comp
          (History.measurable_pairHistoryRewardProjection
            (Action := Action) (Reward := Rat) n))
      (hpairState := fun n : Nat =>
        (hstate n).comp
          (History.measurable_pairHistoryRewardProjection
            (Action := Action) (Reward := Rat) n))
      (mean := mean)
      (varianceProxy := varianceProxy)
      (law := law)
      (reward := reward)
      (haction := haction)
      (hreward := hreward)
      (i := i)
      h_integrable
      h_kernel_pair_map_eq

/--
Projected trace-pair route using the named finite pair-history prefix.

This is the same route as
`..._projected_of_context_state_measurable`, but the remaining pair-law
hypothesis is stated with `History.finitePairHistoryOfTrace`.  That is the
finite-prefix object aligned with `RewardKernel.actionRewardPartialTrajectoryKernel`.
-/
theorem centeredReward_succ_condExp_eq_zero_of_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace
    {Omega : Type u} {Context : Type v} {State : Type w} {Action : Type x}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (law :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (i : Nat)
    (h_integrable :
      Integrable
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))) mu)
    (h_kernel_pair_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega (Prod Action Rat) mOmega inferInstance
            (fun y : Omega => (action y (i + 1), reward y (i + 1)))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
            (fun n history =>
              context n (History.pairHistoryRewardProjection history))
            (fun n history =>
              state n (History.pairHistoryRewardProjection history))
            (fun n : Nat =>
              (hcontext n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            (fun n : Nat =>
              (hstate n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            i
            (History.finitePairHistoryOfTrace
              (action omega) (reward omega) i))
        (ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.EventuallyEq (ae mu)
      (@condExp Omega Real
        ((History.historyFiltrationSucc action reward haction hreward) i)
        mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))))
      (fun _omega : Omega => (0 : Real)) := by
  exact
    centeredReward_succ_condExp_eq_zero_of_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_projected_of_context_state_measurable
      (mu := mu)
      (action := action)
      (rewardKernel := rewardKernel)
      (policy := policy)
      (context := context)
      (state := state)
      (hcontext := hcontext)
      (hstate := hstate)
      (mean := mean)
      (varianceProxy := varianceProxy)
      (law := law)
      (reward := reward)
      (haction := haction)
      (hreward := hreward)
      (i := i)
      h_integrable
      (by simpa [History.finitePairHistoryOfTrace] using h_kernel_pair_map_eq)

/--
Project a generated-history `partialTraj` trace law to the next-pair law.

This names the reusable law-identification step that was previously only
embedded inside the centered-reward consumer below.  If the conditional kernel
of the full finite pair trace at `i + 1` agrees with the one-step action/reward
`partialTraj` kernel, then mapping both sides to the successor coordinate gives
the concrete next `(Action, Reward)` pushforward law consumed by the pair-map
route.
-/
theorem actionRewardHistoryStepKernelFamily_pair_map_eq_of_actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace
    {Omega : Type u} {Context : Type v} {State : Type w} {Action : Type x}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (i : Nat)
    (h_kernel_partialtraj_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega ((j : Finset.Iic (i + 1)) -> Prod Action Rat)
            mOmega inferInstance
            (fun y : Omega =>
              History.finitePairHistoryOfTrace (action y) (reward y) (i + 1))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
            (fun n history =>
              context n (History.pairHistoryRewardProjection history))
            (fun n history =>
              state n (History.pairHistoryRewardProjection history))
            (fun n : Nat =>
              (hcontext n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            (fun n : Nat =>
              (hstate n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            i (i + 1)
            (History.finitePairHistoryOfTrace
              (action omega) (reward omega) i))
        (ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.Eventually
      (fun omega : Omega =>
        @Measure.map Omega (Prod Action Rat) mOmega inferInstance
          (fun y : Omega => (action y (i + 1), reward y (i + 1)))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
            ((History.historyFiltrationSucc action reward haction hreward) i)
            omega) =
        RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
          (fun n history =>
            context n (History.pairHistoryRewardProjection history))
          (fun n history =>
            state n (History.pairHistoryRewardProjection history))
          (fun n : Nat =>
            (hcontext n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          (fun n : Nat =>
            (hstate n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          i
          (History.finitePairHistoryOfTrace
            (action omega) (reward omega) i))
      (ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i))) := by
  filter_upwards [h_kernel_partialtraj_map_eq] with omega h_partial
  let condKernel : Measure Omega :=
    @ProbabilityTheory.condExpKernel Omega mOmega _ mu _
      ((History.historyFiltrationSucc action reward haction hreward) i) omega
  let finiteTraceSucc :
      Omega -> ((j : Finset.Iic (i + 1)) -> Prod Action Rat) :=
    fun y : Omega =>
      History.finitePairHistoryOfTrace (action y) (reward y) (i + 1)
  let nextCoord :
      ((j : Finset.Iic (i + 1)) -> Prod Action Rat) -> Prod Action Rat :=
    fun history =>
      history (Subtype.mk (i + 1) (Finset.mem_Iic.mpr le_rfl))
  have h_finiteTraceSucc_meas : Measurable finiteTraceSucc := by
    simpa [finiteTraceSucc] using
      History.measurable_finitePairHistoryOfTrace action reward haction hreward
        (i + 1)
  have h_nextCoord_meas : Measurable nextCoord := by
    exact measurable_pi_apply _
  have h_next_pair_map :
      Measure.map nextCoord (Measure.map finiteTraceSucc condKernel) =
        @Measure.map Omega (Prod Action Rat) mOmega inferInstance
          (fun y : Omega => (action y (i + 1), reward y (i + 1)))
          condKernel := by
    rw [Measure.map_map h_nextCoord_meas h_finiteTraceSucc_meas]
    rfl
  have h_partial_step :
      Measure.map nextCoord
        (RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
          (fun n history =>
            context n (History.pairHistoryRewardProjection history))
          (fun n history =>
            state n (History.pairHistoryRewardProjection history))
          (fun n : Nat =>
            (hcontext n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          (fun n : Nat =>
            (hstate n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          i (i + 1)
          (History.finitePairHistoryOfTrace
            (action omega) (reward omega) i)) =
        RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
          (fun n history =>
            context n (History.pairHistoryRewardProjection history))
          (fun n history =>
            state n (History.pairHistoryRewardProjection history))
          (fun n : Nat =>
            (hcontext n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          (fun n : Nat =>
            (hstate n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          i
          (History.finitePairHistoryOfTrace
            (action omega) (reward omega) i) := by
    simpa [nextCoord] using
      RewardKernel.actionRewardPartialTrajectoryKernel_succ_next_map_apply
        rewardKernel policy
        (fun n history =>
          context n (History.pairHistoryRewardProjection history))
        (fun n history =>
          state n (History.pairHistoryRewardProjection history))
        (fun n : Nat =>
          (hcontext n).comp
            (History.measurable_pairHistoryRewardProjection
              (Action := Action) (Reward := Rat) n))
        (fun n : Nat =>
          (hstate n).comp
            (History.measurable_pairHistoryRewardProjection
              (Action := Action) (Reward := Rat) n))
        i
        (History.finitePairHistoryOfTrace
          (action omega) (reward omega) i)
  calc
    @Measure.map Omega (Prod Action Rat) mOmega inferInstance
        (fun y : Omega => (action y (i + 1), reward y (i + 1)))
        (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
          ((History.historyFiltrationSucc action reward haction hreward) i)
          omega)
        =
      Measure.map nextCoord (Measure.map finiteTraceSucc condKernel) := by
        simpa [condKernel] using h_next_pair_map.symm
    _ =
      Measure.map nextCoord
        (RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
          (fun n history =>
            context n (History.pairHistoryRewardProjection history))
          (fun n history =>
            state n (History.pairHistoryRewardProjection history))
          (fun n : Nat =>
            (hcontext n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          (fun n : Nat =>
            (hstate n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          i (i + 1)
          (History.finitePairHistoryOfTrace
            (action omega) (reward omega) i)) := by
        simpa [condKernel, finiteTraceSucc] using
          congrArg (Measure.map nextCoord) h_partial
    _ =
      RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
        (fun n history =>
          context n (History.pairHistoryRewardProjection history))
        (fun n history =>
          state n (History.pairHistoryRewardProjection history))
        (fun n : Nat =>
          (hcontext n).comp
            (History.measurable_pairHistoryRewardProjection
              (Action := Action) (Reward := Rat) n))
        (fun n : Nat =>
          (hstate n).comp
            (History.measurable_pairHistoryRewardProjection
              (Action := Action) (Reward := Rat) n))
        i
        (History.finitePairHistoryOfTrace
          (action omega) (reward omega) i) := h_partial_step

/--
Project a history-step next-pair law to the actual-action reward law.

This is the direct reward-coordinate adapter for a conditional kernel law
already stated at the next `(Action, Reward)` level.  Mapping both sides
through `Prod.snd` reduces the target to
`RewardKernel.actionRewardHistoryStepKernelFamily_reward_map`; the only
remaining rewrite is the trim-a.e. successor action equality.
-/
theorem reward_condExpKernel_map_eq_selected_actual_action_of_actionRewardHistoryStepKernelFamily_pair_map_eq
    {Omega : Type u} {Context : Type v} {State : Type w} {Action : Type x}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (F : Filtration Nat mOmega)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (pairContext :
      (n : Nat) -> ((j : Finset.Iic n) -> Prod Action Rat) -> Context)
    (pairState :
      (n : Nat) -> ((j : Finset.Iic n) -> Prod Action Rat) -> State)
    (hpairContext : forall n : Nat, Measurable (pairContext n))
    (hpairState : forall n : Nat, Measurable (pairState n))
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (i : Nat)
    (pairHistory : Omega -> ((j : Finset.Iic i) -> Prod Action Rat))
    (h_action_policy_eq :
      Filter.Eventually
        (fun omega : Omega =>
          action omega (i + 1) =
            (policy i).action (pairState i (pairHistory omega)))
        (ae (mu.trim (F.le i))))
    (h_kernel_pair_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega (Prod Action Rat) mOmega inferInstance
            (fun y : Omega => (action y (i + 1), reward y (i + 1)))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ (F i)
              omega) =
          RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
            pairContext pairState hpairContext hpairState i
            (pairHistory omega))
        (ae (mu.trim (F.le i)))) :
    Filter.Eventually
      (fun omega : Omega =>
        @Measure.map Omega Rat mOmega inferInstance
          (fun y : Omega => reward y (i + 1))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ (F i)
            omega) =
        RewardKernel.selectedMeasure rewardKernel
          (pairContext i (pairHistory omega))
          (action omega (i + 1)))
      (ae (mu.trim (F.le i))) := by
  filter_upwards [h_kernel_pair_map_eq, h_action_policy_eq] with omega
    h_pair h_action_eq
  let condKernel : Measure Omega :=
    @ProbabilityTheory.condExpKernel Omega mOmega _ mu _ (F i) omega
  let nextPair : Omega -> Prod Action Rat :=
    fun y : Omega => (action y (i + 1), reward y (i + 1))
  have h_nextPair_meas : Measurable nextPair := by
    exact (haction (i + 1)).prod (hreward (i + 1))
  have h_left :
      Measure.map Prod.snd (Measure.map nextPair condKernel) =
        @Measure.map Omega Rat mOmega inferInstance
          (fun y : Omega => reward y (i + 1)) condKernel := by
    rw [Measure.map_map measurable_snd h_nextPair_meas]
    rfl
  have h_step_reward :
      Measure.map Prod.snd
          (RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
            pairContext pairState hpairContext hpairState i
            (pairHistory omega)) =
        RewardKernel.selectedMeasure rewardKernel
          (pairContext i (pairHistory omega))
          ((policy i).action (pairState i (pairHistory omega))) := by
    exact
      RewardKernel.actionRewardHistoryStepKernelFamily_reward_map
        rewardKernel policy pairContext pairState hpairContext hpairState i
        (pairHistory omega)
  calc
    @Measure.map Omega Rat mOmega inferInstance
        (fun y : Omega => reward y (i + 1))
        (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ (F i) omega)
        =
      Measure.map Prod.snd (Measure.map nextPair condKernel) := by
        simpa [condKernel] using h_left.symm
    _ =
      Measure.map Prod.snd
        (RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
          pairContext pairState hpairContext hpairState i
          (pairHistory omega)) := by
        rw [h_pair]
    _ =
      RewardKernel.selectedMeasure rewardKernel
        (pairContext i (pairHistory omega))
        ((policy i).action (pairState i (pairHistory omega))) :=
        h_step_reward
    _ =
      RewardKernel.selectedMeasure rewardKernel
        (pairContext i (pairHistory omega))
        (action omega (i + 1)) := by
        rw [h_action_eq]

/--
Specialize the next-pair reward adapter to generated pair histories.

The hypothesis is already the history-step next-pair `condExpKernel` law for
`History.finitePairHistoryOfTrace`.  The theorem only projects it through the
reward coordinate and rewrites the selected policy action to the actual next
action by the supplied successor equality.
-/
theorem reward_condExpKernel_map_eq_selected_actual_action_of_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace
    {Omega : Type u} {Context : Type v} {State : Type w} {Action : Type x}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (i : Nat)
    (h_action_policy_eq :
      Filter.Eventually
        (fun omega : Omega =>
          action omega (i + 1) =
            (policy i).action
              (state i
                (History.finiteRewardHistoryOfTrace (reward omega) i)))
        (ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i))))
    (h_kernel_pair_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega (Prod Action Rat) mOmega inferInstance
            (fun y : Omega => (action y (i + 1), reward y (i + 1)))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
            (fun n history =>
              context n (History.pairHistoryRewardProjection history))
            (fun n history =>
              state n (History.pairHistoryRewardProjection history))
            (fun n : Nat =>
              (hcontext n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            (fun n : Nat =>
              (hstate n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            i
            (History.finitePairHistoryOfTrace
              (action omega) (reward omega) i))
        (ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.Eventually
      (fun omega : Omega =>
        @Measure.map Omega Rat mOmega inferInstance
          (fun y : Omega => reward y (i + 1))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
            ((History.historyFiltrationSucc action reward haction hreward) i)
            omega) =
        RewardKernel.selectedMeasure rewardKernel
          (context i (History.finiteRewardHistoryOfTrace (reward omega) i))
          (action omega (i + 1)))
      (ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i))) := by
  let F : Filtration Nat mOmega :=
    History.historyFiltrationSucc action reward haction hreward
  let pairContext :
      (n : Nat) -> ((j : Finset.Iic n) -> Prod Action Rat) -> Context :=
    fun n history =>
      context n (History.pairHistoryRewardProjection history)
  let pairState :
      (n : Nat) -> ((j : Finset.Iic n) -> Prod Action Rat) -> State :=
    fun n history =>
      state n (History.pairHistoryRewardProjection history)
  let hpairContext : forall n : Nat, Measurable (pairContext n) :=
    fun n : Nat =>
      (hcontext n).comp
        (History.measurable_pairHistoryRewardProjection
          (Action := Action) (Reward := Rat) n)
  let hpairState : forall n : Nat, Measurable (pairState n) :=
    fun n : Nat =>
      (hstate n).comp
        (History.measurable_pairHistoryRewardProjection
          (Action := Action) (Reward := Rat) n)
  let pairHistory :
      Omega -> ((j : Finset.Iic i) -> Prod Action Rat) :=
    fun omega : Omega =>
      History.finitePairHistoryOfTrace (action omega) (reward omega) i
  simpa [F, pairContext, pairState, hpairContext, hpairState, pairHistory,
    History.pairHistoryRewardProjection_finitePairHistoryOfTrace] using
    reward_condExpKernel_map_eq_selected_actual_action_of_actionRewardHistoryStepKernelFamily_pair_map_eq
      (mu := mu)
      (F := F)
      (rewardKernel := rewardKernel)
      (policy := policy)
      (pairContext := pairContext)
      (pairState := pairState)
      (hpairContext := hpairContext)
      (hpairState := hpairState)
      (action := action)
      (reward := reward)
      (haction := haction)
      (hreward := hreward)
      (i := i)
      (pairHistory := pairHistory)
      (by
        simpa [F, pairContext, pairState, pairHistory,
          History.pairHistoryRewardProjection_finitePairHistoryOfTrace]
          using h_action_policy_eq)
      (by
        simpa [F, pairContext, pairState, hpairContext, hpairState,
          pairHistory] using h_kernel_pair_map_eq)

/--
Generated-action wrapper for the finite-pair-history next-pair adapter.

This removes the explicit successor action equality when the action trace is
definitionally generated from the reward-history state.
-/
theorem reward_condExpKernel_map_eq_selected_actual_action_of_generatedActionTraceSucc_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace
    {Omega : Type u} {Context : Type v} {State : Type w} {Action : Type x}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (i : Nat)
    (h_action_generated :
      action =
        Policy.generatedActionTraceSucc policy
          (fun n omega =>
            state n (History.finiteRewardHistoryOfTrace (reward omega) n))
          defaultAction)
    (h_kernel_pair_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega (Prod Action Rat) mOmega inferInstance
            (fun y : Omega => (action y (i + 1), reward y (i + 1)))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
            (fun n history =>
              context n (History.pairHistoryRewardProjection history))
            (fun n history =>
              state n (History.pairHistoryRewardProjection history))
            (fun n : Nat =>
              (hcontext n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            (fun n : Nat =>
              (hstate n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            i
            (History.finitePairHistoryOfTrace
              (action omega) (reward omega) i))
        (ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.Eventually
      (fun omega : Omega =>
        @Measure.map Omega Rat mOmega inferInstance
          (fun y : Omega => reward y (i + 1))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
            ((History.historyFiltrationSucc action reward haction hreward) i)
            omega) =
        RewardKernel.selectedMeasure rewardKernel
          (context i (History.finiteRewardHistoryOfTrace (reward omega) i))
          (action omega (i + 1)))
      (ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i))) := by
  have h_action_policy_eq :
      Filter.Eventually
        (fun omega : Omega =>
          action omega (i + 1) =
            (policy i).action
              (state i
                (History.finiteRewardHistoryOfTrace (reward omega) i)))
        (ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i))) := by
    exact Filter.Eventually.of_forall (fun omega => by
      have h_point := congrFun (congrFun h_action_generated omega) (i + 1)
      simpa [Policy.generatedActionTraceSucc] using h_point)
  exact
    reward_condExpKernel_map_eq_selected_actual_action_of_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace
      (mu := mu)
      (action := action)
      (rewardKernel := rewardKernel)
      (policy := policy)
      (context := context)
      (state := state)
      (hcontext := hcontext)
      (hstate := hstate)
      (reward := reward)
      (haction := haction)
      (hreward := hreward)
      (i := i)
      h_action_policy_eq
      h_kernel_pair_map_eq

/--
Project a full finite-pair `partialTraj` law to the actual-action reward law.

The full trace law first gives the next `(Action, Reward)` marginal by the
compiled `partialTraj` next-coordinate adapter.  Mapping that marginal through
`Prod.snd` and using `RewardKernel.actionRewardHistoryStepKernelFamily_reward_map`
then gives the reward-coordinate law.  The final rewrite only needs an
`i + 1` action equality against the policy-selected action.
-/
theorem reward_condExpKernel_map_eq_selected_actual_action_of_actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace
    {Omega : Type u} {Context : Type v} {State : Type w} {Action : Type x}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (i : Nat)
    (h_action_policy_eq :
      Filter.Eventually
        (fun omega : Omega =>
          action omega (i + 1) =
            (policy i).action
              (state i
                (History.finiteRewardHistoryOfTrace (reward omega) i)))
        (ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i))))
    (h_kernel_partialtraj_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega ((j : Finset.Iic (i + 1)) -> Prod Action Rat)
            mOmega inferInstance
            (fun y : Omega =>
              History.finitePairHistoryOfTrace (action y) (reward y) (i + 1))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
            (fun n history =>
              context n (History.pairHistoryRewardProjection history))
            (fun n history =>
              state n (History.pairHistoryRewardProjection history))
            (fun n : Nat =>
              (hcontext n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            (fun n : Nat =>
              (hstate n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            i (i + 1)
            (History.finitePairHistoryOfTrace
              (action omega) (reward omega) i))
        (ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.Eventually
      (fun omega : Omega =>
        @Measure.map Omega Rat mOmega inferInstance
          (fun y : Omega => reward y (i + 1))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
            ((History.historyFiltrationSucc action reward haction hreward) i)
            omega) =
        RewardKernel.selectedMeasure rewardKernel
          (context i (History.finiteRewardHistoryOfTrace (reward omega) i))
          (action omega (i + 1)))
      (ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i))) := by
  let F : Filtration Nat mOmega :=
    History.historyFiltrationSucc action reward haction hreward
  let pairContext :
      (n : Nat) -> ((j : Finset.Iic n) -> Prod Action Rat) -> Context :=
    fun n history =>
      context n (History.pairHistoryRewardProjection history)
  let pairState :
      (n : Nat) -> ((j : Finset.Iic n) -> Prod Action Rat) -> State :=
    fun n history =>
      state n (History.pairHistoryRewardProjection history)
  let hpairContext : forall n : Nat, Measurable (pairContext n) :=
    fun n : Nat =>
      (hcontext n).comp
        (History.measurable_pairHistoryRewardProjection
          (Action := Action) (Reward := Rat) n)
  let hpairState : forall n : Nat, Measurable (pairState n) :=
    fun n : Nat =>
      (hstate n).comp
        (History.measurable_pairHistoryRewardProjection
          (Action := Action) (Reward := Rat) n)
  let pairHistory :
      Omega -> ((j : Finset.Iic i) -> Prod Action Rat) :=
    fun omega : Omega =>
      History.finitePairHistoryOfTrace (action omega) (reward omega) i
  have h_pair_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega (Prod Action Rat) mOmega inferInstance
            (fun y : Omega => (action y (i + 1), reward y (i + 1)))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ (F i)
              omega) =
          RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
            pairContext pairState hpairContext hpairState i
            (pairHistory omega))
        (ae (mu.trim (F.le i))) := by
    simpa [F, pairContext, pairState, hpairContext, hpairState, pairHistory]
      using
        actionRewardHistoryStepKernelFamily_pair_map_eq_of_actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace
          (mu := mu)
          (action := action)
          (rewardKernel := rewardKernel)
          (policy := policy)
          (context := context)
          (state := state)
          (hcontext := hcontext)
          (hstate := hstate)
          (reward := reward)
          (haction := haction)
          (hreward := hreward)
          (i := i)
          h_kernel_partialtraj_map_eq
  filter_upwards [h_pair_map_eq, h_action_policy_eq] with omega
    h_pair h_action_eq
  let condKernel : Measure Omega :=
    @ProbabilityTheory.condExpKernel Omega mOmega _ mu _ (F i) omega
  let nextPair : Omega -> Prod Action Rat :=
    fun y : Omega => (action y (i + 1), reward y (i + 1))
  have h_nextPair_meas : Measurable nextPair := by
    exact (haction (i + 1)).prod (hreward (i + 1))
  have h_left :
      Measure.map Prod.snd (Measure.map nextPair condKernel) =
        @Measure.map Omega Rat mOmega inferInstance
          (fun y : Omega => reward y (i + 1)) condKernel := by
    rw [Measure.map_map measurable_snd h_nextPair_meas]
    rfl
  have h_step_reward :
      Measure.map Prod.snd
          (RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
            pairContext pairState hpairContext hpairState i
            (pairHistory omega)) =
        RewardKernel.selectedMeasure rewardKernel
          (context i (History.finiteRewardHistoryOfTrace (reward omega) i))
          ((policy i).action
            (state i
              (History.finiteRewardHistoryOfTrace (reward omega) i))) := by
    simpa [pairContext, pairState, hpairContext, hpairState, pairHistory,
      History.pairHistoryRewardProjection_finitePairHistoryOfTrace] using
      RewardKernel.actionRewardHistoryStepKernelFamily_reward_map
        rewardKernel policy pairContext pairState hpairContext hpairState i
        (pairHistory omega)
  calc
    @Measure.map Omega Rat mOmega inferInstance
        (fun y : Omega => reward y (i + 1))
        (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ (F i) omega)
        =
      Measure.map Prod.snd (Measure.map nextPair condKernel) := by
        simpa [condKernel] using h_left.symm
    _ =
      Measure.map Prod.snd
        (RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
          pairContext pairState hpairContext hpairState i
          (pairHistory omega)) := by
        rw [h_pair]
    _ =
      RewardKernel.selectedMeasure rewardKernel
        (context i (History.finiteRewardHistoryOfTrace (reward omega) i))
        ((policy i).action
          (state i
            (History.finiteRewardHistoryOfTrace (reward omega) i))) :=
        h_step_reward
    _ =
      RewardKernel.selectedMeasure rewardKernel
        (context i (History.finiteRewardHistoryOfTrace (reward omega) i))
        (action omega (i + 1)) := by
        rw [h_action_eq]

/--
Generated-action specialization of the full finite-pair `partialTraj` to
actual-action reward-map adapter.

`Policy.generatedActionTraceSucc` supplies the pointwise successor action
equality required by
`reward_condExpKernel_map_eq_selected_actual_action_of_actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace`.
-/
theorem reward_condExpKernel_map_eq_selected_actual_action_of_generatedActionTraceSucc_actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace
    {Omega : Type u} {Context : Type v} {State : Type w} {Action : Type x}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (i : Nat)
    (h_action_generated :
      action =
        Policy.generatedActionTraceSucc policy
          (fun n omega =>
            state n (History.finiteRewardHistoryOfTrace (reward omega) n))
          defaultAction)
    (h_kernel_partialtraj_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega ((j : Finset.Iic (i + 1)) -> Prod Action Rat)
            mOmega inferInstance
            (fun y : Omega =>
              History.finitePairHistoryOfTrace (action y) (reward y) (i + 1))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
            (fun n history =>
              context n (History.pairHistoryRewardProjection history))
            (fun n history =>
              state n (History.pairHistoryRewardProjection history))
            (fun n : Nat =>
              (hcontext n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            (fun n : Nat =>
              (hstate n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            i (i + 1)
            (History.finitePairHistoryOfTrace
              (action omega) (reward omega) i))
        (ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.Eventually
      (fun omega : Omega =>
        @Measure.map Omega Rat mOmega inferInstance
          (fun y : Omega => reward y (i + 1))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
            ((History.historyFiltrationSucc action reward haction hreward) i)
            omega) =
        RewardKernel.selectedMeasure rewardKernel
          (context i (History.finiteRewardHistoryOfTrace (reward omega) i))
          (action omega (i + 1)))
      (ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i))) := by
  have h_action_policy_eq :
      Filter.Eventually
        (fun omega : Omega =>
          action omega (i + 1) =
            (policy i).action
              (state i
                (History.finiteRewardHistoryOfTrace (reward omega) i)))
        (ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i))) := by
    exact Filter.Eventually.of_forall (fun omega => by
      have h_point := congrFun (congrFun h_action_generated omega) (i + 1)
      simpa [Policy.generatedActionTraceSucc] using h_point)
  exact
    reward_condExpKernel_map_eq_selected_actual_action_of_actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace
      (mu := mu)
      (action := action)
      (rewardKernel := rewardKernel)
      (policy := policy)
      (context := context)
      (state := state)
      (hcontext := hcontext)
      (hstate := hstate)
      (reward := reward)
      (haction := haction)
      (hreward := hreward)
      (i := i)
      h_action_policy_eq
      h_kernel_partialtraj_map_eq

/--
Generated-history route from a one-step `partialTraj` law assumption.

If the conditional kernel pushed forward to the extended finite pair trace
agrees with the local action/reward `partialTraj` kernel from `i` to `i + 1`,
then Mathlib's `partialTraj` next-coordinate marginal wrapper turns that into
the concrete next `(Action, Reward)` pair-law consumed by
`..._finitePairHistoryOfTrace`.
-/
theorem centeredReward_succ_condExp_eq_zero_of_actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace
    {Omega : Type u} {Context : Type v} {State : Type w} {Action : Type x}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (law :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (i : Nat)
    (h_integrable :
      Integrable
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))) mu)
    (h_kernel_partialtraj_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega ((j : Finset.Iic (i + 1)) -> Prod Action Rat)
            mOmega inferInstance
            (fun y : Omega =>
              History.finitePairHistoryOfTrace (action y) (reward y) (i + 1))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
            (fun n history =>
              context n (History.pairHistoryRewardProjection history))
            (fun n history =>
              state n (History.pairHistoryRewardProjection history))
            (fun n : Nat =>
              (hcontext n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            (fun n : Nat =>
              (hstate n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            i (i + 1)
            (History.finitePairHistoryOfTrace
              (action omega) (reward omega) i))
        (ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.EventuallyEq (ae mu)
      (@condExp Omega Real
        ((History.historyFiltrationSucc action reward haction hreward) i)
        mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))))
      (fun _omega : Omega => (0 : Real)) := by
  have h_kernel_pair_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega (Prod Action Rat) mOmega inferInstance
            (fun y : Omega => (action y (i + 1), reward y (i + 1)))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
            (fun n history =>
              context n (History.pairHistoryRewardProjection history))
            (fun n history =>
              state n (History.pairHistoryRewardProjection history))
            (fun n : Nat =>
              (hcontext n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            (fun n : Nat =>
              (hstate n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            i
            (History.finitePairHistoryOfTrace
              (action omega) (reward omega) i))
        (ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i))) := by
    filter_upwards [h_kernel_partialtraj_map_eq] with omega h_partial
    let condKernel : Measure Omega :=
      @ProbabilityTheory.condExpKernel Omega mOmega _ mu _
        ((History.historyFiltrationSucc action reward haction hreward) i) omega
    let finiteTraceSucc :
        Omega -> ((j : Finset.Iic (i + 1)) -> Prod Action Rat) :=
      fun y : Omega =>
        History.finitePairHistoryOfTrace (action y) (reward y) (i + 1)
    let nextCoord :
        ((j : Finset.Iic (i + 1)) -> Prod Action Rat) -> Prod Action Rat :=
      fun history =>
        history ⟨i + 1, Finset.mem_Iic.mpr le_rfl⟩
    have h_finiteTraceSucc_meas : Measurable finiteTraceSucc := by
      simpa [finiteTraceSucc] using
        History.measurable_finitePairHistoryOfTrace action reward haction hreward
          (i + 1)
    have h_nextCoord_meas : Measurable nextCoord := by
      exact measurable_pi_apply _
    have h_next_pair_map :
        Measure.map nextCoord (Measure.map finiteTraceSucc condKernel) =
          @Measure.map Omega (Prod Action Rat) mOmega inferInstance
            (fun y : Omega => (action y (i + 1), reward y (i + 1)))
            condKernel := by
      rw [Measure.map_map h_nextCoord_meas h_finiteTraceSucc_meas]
      rfl
    have h_partial_step :
        Measure.map nextCoord
          (RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
            (fun n history =>
              context n (History.pairHistoryRewardProjection history))
            (fun n history =>
              state n (History.pairHistoryRewardProjection history))
            (fun n : Nat =>
              (hcontext n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            (fun n : Nat =>
              (hstate n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            i (i + 1)
            (History.finitePairHistoryOfTrace
              (action omega) (reward omega) i)) =
          RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
            (fun n history =>
              context n (History.pairHistoryRewardProjection history))
            (fun n history =>
              state n (History.pairHistoryRewardProjection history))
            (fun n : Nat =>
              (hcontext n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            (fun n : Nat =>
              (hstate n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            i
            (History.finitePairHistoryOfTrace
              (action omega) (reward omega) i) := by
      exact
        RewardKernel.actionRewardPartialTrajectoryKernel_succ_next_map_apply
          rewardKernel policy
          (fun n history =>
            context n (History.pairHistoryRewardProjection history))
          (fun n history =>
            state n (History.pairHistoryRewardProjection history))
          (fun n : Nat =>
            (hcontext n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          (fun n : Nat =>
            (hstate n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          i
          (History.finitePairHistoryOfTrace
            (action omega) (reward omega) i)
    calc
      @Measure.map Omega (Prod Action Rat) mOmega inferInstance
          (fun y : Omega => (action y (i + 1), reward y (i + 1)))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
            ((History.historyFiltrationSucc action reward haction hreward) i)
            omega)
          =
        Measure.map nextCoord (Measure.map finiteTraceSucc condKernel) := by
          simpa [condKernel] using h_next_pair_map.symm
      _ =
        Measure.map nextCoord
          (RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
            (fun n history =>
              context n (History.pairHistoryRewardProjection history))
            (fun n history =>
              state n (History.pairHistoryRewardProjection history))
            (fun n : Nat =>
              (hcontext n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            (fun n : Nat =>
              (hstate n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            i (i + 1)
            (History.finitePairHistoryOfTrace
              (action omega) (reward omega) i)) := by
          simpa [condKernel, finiteTraceSucc] using
            congrArg (Measure.map nextCoord) h_partial
      _ =
        RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
          (fun n history =>
            context n (History.pairHistoryRewardProjection history))
          (fun n history =>
            state n (History.pairHistoryRewardProjection history))
          (fun n : Nat =>
            (hcontext n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          (fun n : Nat =>
            (hstate n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          i
          (History.finitePairHistoryOfTrace
            (action omega) (reward omega) i) := h_partial_step
  exact
    centeredReward_succ_condExp_eq_zero_of_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace
      (mu := mu)
      (action := action)
      (rewardKernel := rewardKernel)
      (policy := policy)
      (context := context)
      (state := state)
      (hcontext := hcontext)
      (hstate := hstate)
      (mean := mean)
      (varianceProxy := varianceProxy)
      (law := law)
      (reward := reward)
      (haction := haction)
      (hreward := hreward)
      (i := i)
      h_integrable
      h_kernel_pair_map_eq

/--
Build the full next `(Action, Reward)` conditional-kernel law from split
action and reward laws.

The action side is deterministic/predictable under the conditional kernel, and
the reward side supplies the selected reward law.  Together they identify the
next-pair pushforward with the local history-step action/reward kernel.
-/
theorem actionRewardHistoryStepKernelFamily_pair_map_eq_of_action_ae_eq_policy_reward_map_eq
    {Omega : Type u} {Context : Type v} {State : Type w} {Action : Type x}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (F : Filtration Nat mOmega)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (pairContext :
      (n : Nat) -> ((j : Finset.Iic n) -> Prod Action Rat) -> Context)
    (pairState :
      (n : Nat) -> ((j : Finset.Iic n) -> Prod Action Rat) -> State)
    (hpairContext : forall n : Nat, Measurable (pairContext n))
    (hpairState : forall n : Nat, Measurable (pairState n))
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Rat)
    (i : Nat)
    (pairHistory : Omega -> ((j : Finset.Iic i) -> Prod Action Rat))
    (h_action_next :
      @Measurable Omega Action mOmega inferInstance
        (fun omega : Omega => action omega (i + 1)))
    (h_reward_next :
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega (i + 1)))
    (h_action_ae_eq_policy :
      Filter.Eventually
        (fun omega : Omega =>
          Filter.EventuallyEq
            (ae (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ (F i)
              omega))
            (fun y : Omega => action y (i + 1))
            (fun _y : Omega =>
              (policy i).action (pairState i (pairHistory omega))))
        (ae (mu.trim (F.le i))))
    (h_reward_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega Rat mOmega inferInstance
            (fun y : Omega => reward y (i + 1))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ (F i)
              omega) =
          RewardKernel.selectedMeasure rewardKernel
            (pairContext i (pairHistory omega))
            ((policy i).action (pairState i (pairHistory omega))))
        (ae (mu.trim (F.le i)))) :
    Filter.Eventually
      (fun omega : Omega =>
        @Measure.map Omega (Prod Action Rat) mOmega inferInstance
          (fun y : Omega => (action y (i + 1), reward y (i + 1)))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ (F i)
            omega) =
        RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
          pairContext pairState hpairContext hpairState i
          (pairHistory omega))
      (ae (mu.trim (F.le i))) := by
  have h_pair_next_meas :
      Measurable
        (fun y : Omega => (action y (i + 1), reward y (i + 1))) :=
    h_action_next.prod h_reward_next
  filter_upwards [h_action_ae_eq_policy, h_reward_map_eq] with omega
    h_action h_reward
  let condKernel : Measure Omega :=
    @ProbabilityTheory.condExpKernel Omega mOmega _ mu _ (F i) omega
  let selectedAction : Action :=
    (policy i).action (pairState i (pairHistory omega))
  let rewardNext : Omega -> Rat :=
    fun y : Omega => reward y (i + 1)
  let nextPair : Omega -> Prod Action Rat :=
    fun y : Omega => (action y (i + 1), reward y (i + 1))
  let frozenPair : Omega -> Prod Action Rat :=
    fun y : Omega => (selectedAction, reward y (i + 1))
  have h_pair_ae :
      Filter.EventuallyEq (ae condKernel) nextPair frozenPair := by
    filter_upwards [h_action] with y hy
    simp [nextPair, frozenPair, selectedAction, hy]
  have h_next_to_frozen :
      Measure.map nextPair condKernel =
        Measure.map frozenPair condKernel := by
    exact Measure.map_congr h_pair_ae
  have h_prod_mk_meas : Measurable (Prod.mk selectedAction : Rat -> Prod Action Rat) := by
    fun_prop
  have h_frozen_map :
      Measure.map frozenPair condKernel =
        Measure.map (Prod.mk selectedAction)
          (Measure.map rewardNext condKernel) := by
    rw [Measure.map_map h_prod_mk_meas h_reward_next]
    rfl
  calc
    @Measure.map Omega (Prod Action Rat) mOmega inferInstance
        (fun y : Omega => (action y (i + 1), reward y (i + 1)))
        (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ (F i)
          omega)
        =
      Measure.map nextPair condKernel := by
        rfl
    _ = Measure.map frozenPair condKernel := h_next_to_frozen
    _ =
      Measure.map (Prod.mk selectedAction)
        (Measure.map rewardNext condKernel) := h_frozen_map
    _ =
      Measure.map (Prod.mk selectedAction)
        (RewardKernel.selectedMeasure rewardKernel
          (pairContext i (pairHistory omega))
          ((policy i).action (pairState i (pairHistory omega)))) := by
        rw [h_reward]
    _ =
      RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
        pairContext pairState hpairContext hpairState i
        (pairHistory omega) := by
        simpa [selectedAction] using
          (RewardKernel.actionRewardHistoryStepKernelFamily_apply_eq_map_prod_mk
            rewardKernel policy pairContext pairState hpairContext hpairState
            i (pairHistory omega)).symm

/--
Generated-action source plus an actual-action reward law gives the full
next-pair law.

This is the generated-history specialization of the split-law builder.  The
action side is supplied by `Policy.generatedActionTraceSucc`; the remaining
reward assumption may be stated with the actual next action at the conditioning
point, and is rewritten to the policy-selected action before invoking the
generic split-law theorem.
-/
theorem actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc_reward_map_eq_actual_action
    {Omega : Type u} {Context : Type v} {State : Type w} {Action : Type x}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (pairContext :
      (n : Nat) -> ((j : Finset.Iic n) -> Prod Action Rat) -> Context)
    (pairState :
      (n : Nat) -> ((j : Finset.Iic n) -> Prod Action Rat) -> State)
    (hpairContext : forall n : Nat, Measurable (pairContext n))
    (hpairState : forall n : Nat, Measurable (pairState n))
    (defaultAction : Action)
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (i : Nat)
    (h_action_generated :
      action =
        Policy.generatedActionTraceSucc policy
          (fun n omega =>
            pairState n
              (History.finitePairHistoryOfTrace
                (action omega) (reward omega) n))
          defaultAction)
    (h_reward_map_eq_actual_action :
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega Rat mOmega inferInstance
            (fun y : Omega => reward y (i + 1))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          RewardKernel.selectedMeasure rewardKernel
            (pairContext i
              (History.finitePairHistoryOfTrace
                (action omega) (reward omega) i))
            (action omega (i + 1)))
        (ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.Eventually
      (fun omega : Omega =>
        @Measure.map Omega (Prod Action Rat) mOmega inferInstance
          (fun y : Omega => (action y (i + 1), reward y (i + 1)))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
            ((History.historyFiltrationSucc action reward haction hreward) i)
            omega) =
        RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
          pairContext pairState hpairContext hpairState i
          (History.finitePairHistoryOfTrace
            (action omega) (reward omega) i))
      (ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i))) := by
  let F : Filtration Nat mOmega :=
    History.historyFiltrationSucc action reward haction hreward
  let pairHistory : Omega -> ((j : Finset.Iic i) -> Prod Action Rat) :=
    fun omega : Omega =>
      History.finitePairHistoryOfTrace (action omega) (reward omega) i
  have h_action_ae_eq_policy :
      Filter.Eventually
        (fun omega : Omega =>
          Filter.EventuallyEq
            (ae (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ (F i)
              omega))
            (fun y : Omega => action y (i + 1))
            (fun _y : Omega =>
              (policy i).action (pairState i (pairHistory omega))))
        (ae (mu.trim (F.le i))) := by
    simpa [F, pairHistory] using
      action_condExpKernel_ae_eq_policy_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc
        (mu := mu)
        (policy := policy)
        (pairState := pairState)
        (hpairState := hpairState)
        (defaultAction := defaultAction)
        (action := action)
        (reward := reward)
        (haction := haction)
        (hreward := hreward)
        (i := i)
        h_action_generated
  have h_action_policy_eq :
      Filter.Eventually
        (fun omega : Omega =>
          action omega (i + 1) =
            (policy i).action (pairState i (pairHistory omega)))
        (ae (mu.trim (F.le i))) := by
    exact Filter.Eventually.of_forall (fun omega => by
      have h_point := congrFun (congrFun h_action_generated omega) (i + 1)
      simpa [F, pairHistory, Policy.generatedActionTraceSucc] using h_point)
  have h_reward_map_eq_policy :
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega Rat mOmega inferInstance
            (fun y : Omega => reward y (i + 1))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ (F i)
              omega) =
          RewardKernel.selectedMeasure rewardKernel
            (pairContext i (pairHistory omega))
            ((policy i).action (pairState i (pairHistory omega))))
        (ae (mu.trim (F.le i))) := by
    exact
      reward_condExpKernel_map_eq_selected_policy_of_action_eq
        (mu := mu)
        (F := F)
        (rewardKernel := rewardKernel)
        (policy := policy)
        (pairContext := pairContext)
        (pairState := pairState)
        (action := action)
        (reward := reward)
        (i := i)
        (pairHistory := pairHistory)
        h_action_policy_eq
        (by simpa [F, pairHistory] using h_reward_map_eq_actual_action)
  exact
    actionRewardHistoryStepKernelFamily_pair_map_eq_of_action_ae_eq_policy_reward_map_eq
      (mu := mu)
      (F := F)
      (rewardKernel := rewardKernel)
      (policy := policy)
      (pairContext := pairContext)
      (pairState := pairState)
      (hpairContext := hpairContext)
      (hpairState := hpairState)
      (action := action)
      (reward := reward)
      (i := i)
      (pairHistory := pairHistory)
      (h_action_next := haction (i + 1))
      (h_reward_next := hreward (i + 1))
      h_action_ae_eq_policy
      h_reward_map_eq_policy

/--
Turn a next-pair `condExpKernel` law into the extension-map `partialTraj` law.

This is the law-shaped bridge between the pair-map consumer and the
extension-map `partialTraj` route: once the conditional kernel of the next
`(Action, Reward)` pair is identified with the configured history-step kernel,
pushing both sides through `History.extendPairHistorySucc` identifies the
one-step finite-prefix trajectory kernel.
-/
theorem actionRewardPartialTrajectoryKernel_extend_map_eq_of_actionRewardHistoryStepKernelFamily_pair_map_eq
    {Omega : Type u} {Context : Type v} {State : Type w} {Action : Type x}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (F : Filtration Nat mOmega)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (pairContext :
      (n : Nat) -> ((j : Finset.Iic n) -> Prod Action Rat) -> Context)
    (pairState :
      (n : Nat) -> ((j : Finset.Iic n) -> Prod Action Rat) -> State)
    (hpairContext : forall n : Nat, Measurable (pairContext n))
    (hpairState : forall n : Nat, Measurable (pairState n))
    (action : Omega -> ActionTrace Action)
    (reward : Omega -> RewardTrace Rat)
    (i : Nat)
    (pairHistory : Omega -> ((j : Finset.Iic i) -> Prod Action Rat))
    (h_action_next :
      @Measurable Omega Action mOmega inferInstance
        (fun omega : Omega => action omega (i + 1)))
    (h_reward_next :
      @Measurable Omega Rat mOmega inferInstance
        (fun omega : Omega => reward omega (i + 1)))
    (h_kernel_pair_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega (Prod Action Rat) mOmega inferInstance
            (fun y : Omega => (action y (i + 1), reward y (i + 1)))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ (F i)
              omega) =
          RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
            pairContext pairState hpairContext hpairState i
            (pairHistory omega))
        (ae (mu.trim (F.le i)))) :
    Filter.Eventually
      (fun omega : Omega =>
        @Measure.map Omega ((j : Finset.Iic (i + 1)) -> Prod Action Rat)
          mOmega inferInstance
          (fun y : Omega =>
            History.extendPairHistorySucc
              (pairHistory omega)
              (action y (i + 1), reward y (i + 1)))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ (F i)
            omega) =
        RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
          pairContext pairState hpairContext hpairState i (i + 1)
          (pairHistory omega))
      (ae (mu.trim (F.le i))) := by
  have h_pair_next_meas :
      Measurable
        (fun y : Omega => (action y (i + 1), reward y (i + 1))) :=
    h_action_next.prod h_reward_next
  filter_upwards [h_kernel_pair_map_eq] with omega h_pair
  let condKernel : Measure Omega :=
    @ProbabilityTheory.condExpKernel Omega mOmega _ mu _ (F i) omega
  let histPrefix : (j : Finset.Iic i) -> Prod Action Rat := pairHistory omega
  let nextPair : Omega -> Prod Action Rat :=
    fun y : Omega => (action y (i + 1), reward y (i + 1))
  let extendNext :
      Prod Action Rat -> ((j : Finset.Iic (i + 1)) -> Prod Action Rat) :=
    fun next => History.extendPairHistorySucc histPrefix next
  have h_extend_input_meas :
      Measurable
        (fun next : Prod Action Rat =>
          (histPrefix, next)) := by
    fun_prop
  have h_extendNext_meas : Measurable extendNext := by
    simpa [extendNext] using
      (History.measurable_extendPairHistorySucc
        (Action := Action) (Reward := Rat) (t := i)).comp
        h_extend_input_meas
  have h_extend_map :
      Measure.map extendNext (Measure.map nextPair condKernel) =
        @Measure.map Omega ((j : Finset.Iic (i + 1)) -> Prod Action Rat)
          mOmega inferInstance
          (fun y : Omega =>
            History.extendPairHistorySucc
              (pairHistory omega)
              (action y (i + 1), reward y (i + 1)))
          condKernel := by
    rw [Measure.map_map h_extendNext_meas h_pair_next_meas]
    rfl
  calc
    @Measure.map Omega ((j : Finset.Iic (i + 1)) -> Prod Action Rat)
        mOmega inferInstance
        (fun y : Omega =>
          History.extendPairHistorySucc
            (pairHistory omega)
            (action y (i + 1), reward y (i + 1)))
        (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _ (F i)
          omega)
        =
      Measure.map extendNext (Measure.map nextPair condKernel) := by
        simpa [condKernel, histPrefix, nextPair, extendNext] using
          h_extend_map.symm
    _ =
      Measure.map extendNext
        (RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
          pairContext pairState hpairContext hpairState i
          (pairHistory omega)) := by
        simpa [condKernel, histPrefix, nextPair] using
          congrArg (Measure.map extendNext) h_pair
    _ =
      RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
        pairContext pairState hpairContext hpairState i (i + 1)
        (pairHistory omega) := by
        simpa [extendNext, histPrefix] using
          (RewardKernel.actionRewardPartialTrajectoryKernel_succ_extend_map_apply
            rewardKernel policy pairContext pairState hpairContext hpairState
            i (pairHistory omega)).symm

/--
Generated-history finite-pair-trace specialization of the extension-map law
builder.

The remaining assumption is the concrete conditional next-pair law against
`RewardKernel.actionRewardHistoryStepKernelFamily`; this theorem packages the
pushforward through `History.extendPairHistorySucc` and the local
`partialTraj` wrapper.
-/
theorem actionRewardPartialTrajectoryKernel_extend_map_eq_of_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace
    {Omega : Type u} {Context : Type v} {State : Type w} {Action : Type x}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (i : Nat)
    (h_kernel_pair_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega (Prod Action Rat) mOmega inferInstance
            (fun y : Omega => (action y (i + 1), reward y (i + 1)))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
            (fun n history =>
              context n (History.pairHistoryRewardProjection history))
            (fun n history =>
              state n (History.pairHistoryRewardProjection history))
            (fun n : Nat =>
              (hcontext n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            (fun n : Nat =>
              (hstate n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            i
            (History.finitePairHistoryOfTrace
              (action omega) (reward omega) i))
        (ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.Eventually
      (fun omega : Omega =>
        @Measure.map Omega ((j : Finset.Iic (i + 1)) -> Prod Action Rat)
          mOmega inferInstance
          (fun y : Omega =>
            History.extendPairHistorySucc
              (History.finitePairHistoryOfTrace
                (action omega) (reward omega) i)
              (action y (i + 1), reward y (i + 1)))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
            ((History.historyFiltrationSucc action reward haction hreward) i)
            omega) =
        RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
          (fun n history =>
            context n (History.pairHistoryRewardProjection history))
          (fun n history =>
            state n (History.pairHistoryRewardProjection history))
          (fun n : Nat =>
            (hcontext n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          (fun n : Nat =>
            (hstate n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          i (i + 1)
          (History.finitePairHistoryOfTrace
            (action omega) (reward omega) i))
      (ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i))) := by
  exact
    actionRewardPartialTrajectoryKernel_extend_map_eq_of_actionRewardHistoryStepKernelFamily_pair_map_eq
      (mu := mu)
      (F := History.historyFiltrationSucc action reward haction hreward)
      (rewardKernel := rewardKernel)
      (policy := policy)
      (pairContext := fun n history =>
        context n (History.pairHistoryRewardProjection history))
      (pairState := fun n history =>
        state n (History.pairHistoryRewardProjection history))
      (hpairContext := fun n : Nat =>
        (hcontext n).comp
          (History.measurable_pairHistoryRewardProjection
            (Action := Action) (Reward := Rat) n))
      (hpairState := fun n : Nat =>
        (hstate n).comp
          (History.measurable_pairHistoryRewardProjection
            (Action := Action) (Reward := Rat) n))
      (action := action)
      (reward := reward)
      (i := i)
      (pairHistory := fun omega : Omega =>
        History.finitePairHistoryOfTrace (action omega) (reward omega) i)
      (h_action_next := haction (i + 1))
      (h_reward_next := hreward (i + 1))
      h_kernel_pair_map_eq

/--
Generated-action and actual-action reward law source for the extension-map
`partialTraj` route.

This composes the generated-action next-pair split-law hookup with the
extension-map `partialTraj` builder.  The remaining law input is only the
reward-coordinate conditional map law selected by the actual next action; the
wrapper rewrites that action to the policy-selected action and pushes the
resulting next-pair law through `History.extendPairHistorySucc`.
-/
theorem actionRewardPartialTrajectoryKernel_extend_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc_reward_map_eq_actual_action
    {Omega : Type u} {Context : Type v} {State : Type w} {Action : Type x}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (i : Nat)
    (h_action_generated :
      action =
        Policy.generatedActionTraceSucc policy
          (fun n omega =>
            state n (History.finiteRewardHistoryOfTrace (reward omega) n))
          defaultAction)
    (h_reward_map_eq_actual_action :
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega Rat mOmega inferInstance
            (fun y : Omega => reward y (i + 1))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          RewardKernel.selectedMeasure rewardKernel
            (context i
              (History.finiteRewardHistoryOfTrace (reward omega) i))
            (action omega (i + 1)))
        (ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.Eventually
      (fun omega : Omega =>
        @Measure.map Omega ((j : Finset.Iic (i + 1)) -> Prod Action Rat)
          mOmega inferInstance
          (fun y : Omega =>
            History.extendPairHistorySucc
              (History.finitePairHistoryOfTrace
                (action omega) (reward omega) i)
              (action y (i + 1), reward y (i + 1)))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
            ((History.historyFiltrationSucc action reward haction hreward) i)
            omega) =
        RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
          (fun n history =>
            context n (History.pairHistoryRewardProjection history))
          (fun n history =>
            state n (History.pairHistoryRewardProjection history))
          (fun n : Nat =>
            (hcontext n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          (fun n : Nat =>
            (hstate n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          i (i + 1)
          (History.finitePairHistoryOfTrace
            (action omega) (reward omega) i))
      (ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i))) := by
  have h_action_generated_pair :
      action =
        Policy.generatedActionTraceSucc policy
          (fun n omega =>
            state n
              (History.pairHistoryRewardProjection
                (History.finitePairHistoryOfTrace
                  (action omega) (reward omega) n)))
          defaultAction := by
    simpa [History.pairHistoryRewardProjection_finitePairHistoryOfTrace]
      using h_action_generated
  have h_pair_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega (Prod Action Rat) mOmega inferInstance
            (fun y : Omega => (action y (i + 1), reward y (i + 1)))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          RewardKernel.actionRewardHistoryStepKernelFamily rewardKernel policy
            (fun n history =>
              context n (History.pairHistoryRewardProjection history))
            (fun n history =>
              state n (History.pairHistoryRewardProjection history))
            (fun n : Nat =>
              (hcontext n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            (fun n : Nat =>
              (hstate n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            i
            (History.finitePairHistoryOfTrace
              (action omega) (reward omega) i))
        (ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i))) := by
    exact
      actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc_reward_map_eq_actual_action
        (mu := mu)
        (rewardKernel := rewardKernel)
        (policy := policy)
        (pairContext := fun n history =>
          context n (History.pairHistoryRewardProjection history))
        (pairState := fun n history =>
          state n (History.pairHistoryRewardProjection history))
        (hpairContext := fun n : Nat =>
          (hcontext n).comp
            (History.measurable_pairHistoryRewardProjection
              (Action := Action) (Reward := Rat) n))
        (hpairState := fun n : Nat =>
          (hstate n).comp
            (History.measurable_pairHistoryRewardProjection
              (Action := Action) (Reward := Rat) n))
        (defaultAction := defaultAction)
        (action := action)
        (reward := reward)
        (haction := haction)
        (hreward := hreward)
        (i := i)
        h_action_generated_pair
        (by
          simpa [History.pairHistoryRewardProjection_finitePairHistoryOfTrace]
            using h_reward_map_eq_actual_action)
  exact
    actionRewardPartialTrajectoryKernel_extend_map_eq_of_actionRewardHistoryStepKernelFamily_pair_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace
      (mu := mu)
      (action := action)
      (rewardKernel := rewardKernel)
      (policy := policy)
      (context := context)
      (state := state)
      (hcontext := hcontext)
      (hstate := hstate)
      (reward := reward)
      (haction := haction)
      (hreward := hreward)
      (i := i)
      h_pair_map_eq

/--
Turn an extension-map `partialTraj` law into the full finite-pair-trace law.

The generated history filtration already freezes the old pair prefix under the
conditional kernel, so the full `i + 1` trace pushforward agrees a.e. with the
deterministic extension of the frozen `i` prefix by the random next pair.  This
adapter packages that successor decomposition separately from the centered
reward consumer.
-/
theorem actionRewardPartialTrajectoryKernel_map_eq_of_extend_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace
    {Omega : Type u} {Context : Type v} {State : Type w} {Action : Type x}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (i : Nat)
    (h_kernel_extend_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega ((j : Finset.Iic (i + 1)) -> Prod Action Rat)
            mOmega inferInstance
            (fun y : Omega =>
              History.extendPairHistorySucc
                (History.finitePairHistoryOfTrace
                  (action omega) (reward omega) i)
                (action y (i + 1), reward y (i + 1)))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
            (fun n history =>
              context n (History.pairHistoryRewardProjection history))
            (fun n history =>
              state n (History.pairHistoryRewardProjection history))
            (fun n : Nat =>
              (hcontext n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            (fun n : Nat =>
              (hstate n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            i (i + 1)
            (History.finitePairHistoryOfTrace
              (action omega) (reward omega) i))
        (ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.Eventually
      (fun omega : Omega =>
        @Measure.map Omega ((j : Finset.Iic (i + 1)) -> Prod Action Rat)
          mOmega inferInstance
          (fun y : Omega =>
            History.finitePairHistoryOfTrace (action y) (reward y) (i + 1))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
            ((History.historyFiltrationSucc action reward haction hreward) i)
            omega) =
        RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
          (fun n history =>
            context n (History.pairHistoryRewardProjection history))
          (fun n history =>
            state n (History.pairHistoryRewardProjection history))
          (fun n : Nat =>
            (hcontext n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          (fun n : Nat =>
            (hstate n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          i (i + 1)
          (History.finitePairHistoryOfTrace
            (action omega) (reward omega) i))
      (ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i))) := by
  have h_trace_to_extend :
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega ((j : Finset.Iic (i + 1)) -> Prod Action Rat)
            mOmega inferInstance
            (fun y : Omega =>
              History.finitePairHistoryOfTrace (action y) (reward y) (i + 1))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          @Measure.map Omega ((j : Finset.Iic (i + 1)) -> Prod Action Rat)
            mOmega inferInstance
            (fun y : Omega =>
              History.extendPairHistorySucc
                (History.finitePairHistoryOfTrace
                  (action omega) (reward omega) i)
                (action y (i + 1), reward y (i + 1)))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega))
        (ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i))) :=
    finitePairHistory_succ_condExpKernel_map_eq_extend_historyFiltrationSucc
      (mu := mu)
      (action := action)
      (reward := reward)
      (haction := haction)
      (hreward := hreward)
      (i := i)
  filter_upwards [h_trace_to_extend, h_kernel_extend_map_eq] with omega
    h_trace_extend h_extend_partial
  exact h_trace_extend.trans h_extend_partial

/--
Project an extension-map `partialTraj` law to the actual-action reward law.

This is the reward-coordinate counterpart of
`actionRewardPartialTrajectoryKernel_map_eq_of_extend_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace`:
first lift the deterministic frozen-prefix extension law back to the full
finite-pair trace law, then reuse the finite-pair trace reward-map adapter.
-/
theorem reward_condExpKernel_map_eq_selected_actual_action_of_actionRewardPartialTrajectoryKernel_extend_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace
    {Omega : Type u} {Context : Type v} {State : Type w} {Action : Type x}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (i : Nat)
    (h_action_policy_eq :
      Filter.Eventually
        (fun omega : Omega =>
          action omega (i + 1) =
            (policy i).action
              (state i
                (History.finiteRewardHistoryOfTrace (reward omega) i)))
        (ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i))))
    (h_kernel_extend_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega ((j : Finset.Iic (i + 1)) -> Prod Action Rat)
            mOmega inferInstance
            (fun y : Omega =>
              History.extendPairHistorySucc
                (History.finitePairHistoryOfTrace
                  (action omega) (reward omega) i)
                (action y (i + 1), reward y (i + 1)))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
            (fun n history =>
              context n (History.pairHistoryRewardProjection history))
            (fun n history =>
              state n (History.pairHistoryRewardProjection history))
            (fun n : Nat =>
              (hcontext n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            (fun n : Nat =>
              (hstate n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            i (i + 1)
            (History.finitePairHistoryOfTrace
              (action omega) (reward omega) i))
        (ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.Eventually
      (fun omega : Omega =>
        @Measure.map Omega Rat mOmega inferInstance
          (fun y : Omega => reward y (i + 1))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
            ((History.historyFiltrationSucc action reward haction hreward) i)
            omega) =
        RewardKernel.selectedMeasure rewardKernel
          (context i (History.finiteRewardHistoryOfTrace (reward omega) i))
          (action omega (i + 1)))
      (ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i))) := by
  have h_kernel_partialtraj_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega ((j : Finset.Iic (i + 1)) -> Prod Action Rat)
            mOmega inferInstance
            (fun y : Omega =>
              History.finitePairHistoryOfTrace (action y) (reward y) (i + 1))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
            (fun n history =>
              context n (History.pairHistoryRewardProjection history))
            (fun n history =>
              state n (History.pairHistoryRewardProjection history))
            (fun n : Nat =>
              (hcontext n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            (fun n : Nat =>
              (hstate n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            i (i + 1)
            (History.finitePairHistoryOfTrace
              (action omega) (reward omega) i))
        (ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i))) :=
    actionRewardPartialTrajectoryKernel_map_eq_of_extend_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace
      (mu := mu)
      (action := action)
      (rewardKernel := rewardKernel)
      (policy := policy)
      (context := context)
      (state := state)
      (hcontext := hcontext)
      (hstate := hstate)
      (reward := reward)
      (haction := haction)
      (hreward := hreward)
      (i := i)
      h_kernel_extend_map_eq
  exact
    reward_condExpKernel_map_eq_selected_actual_action_of_actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace
      (mu := mu)
      (action := action)
      (rewardKernel := rewardKernel)
      (policy := policy)
      (context := context)
      (state := state)
      (hcontext := hcontext)
      (hstate := hstate)
      (reward := reward)
      (haction := haction)
      (hreward := hreward)
      (i := i)
      h_action_policy_eq
      h_kernel_partialtraj_map_eq

/--
Generated-action specialization of the extension-map reward-coordinate adapter.

The generated shifted policy trace supplies the successor action equality; the
remaining hypothesis is only the frozen-prefix extension-map `partialTraj`
law.
-/
theorem reward_condExpKernel_map_eq_selected_actual_action_of_generatedActionTraceSucc_actionRewardPartialTrajectoryKernel_extend_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace
    {Omega : Type u} {Context : Type v} {State : Type w} {Action : Type x}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (i : Nat)
    (h_action_generated :
      action =
        Policy.generatedActionTraceSucc policy
          (fun n omega =>
            state n (History.finiteRewardHistoryOfTrace (reward omega) n))
          defaultAction)
    (h_kernel_extend_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega ((j : Finset.Iic (i + 1)) -> Prod Action Rat)
            mOmega inferInstance
            (fun y : Omega =>
              History.extendPairHistorySucc
                (History.finitePairHistoryOfTrace
                  (action omega) (reward omega) i)
                (action y (i + 1), reward y (i + 1)))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
            (fun n history =>
              context n (History.pairHistoryRewardProjection history))
            (fun n history =>
              state n (History.pairHistoryRewardProjection history))
            (fun n : Nat =>
              (hcontext n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            (fun n : Nat =>
              (hstate n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            i (i + 1)
            (History.finitePairHistoryOfTrace
              (action omega) (reward omega) i))
        (ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.Eventually
      (fun omega : Omega =>
        @Measure.map Omega Rat mOmega inferInstance
          (fun y : Omega => reward y (i + 1))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
            ((History.historyFiltrationSucc action reward haction hreward) i)
            omega) =
        RewardKernel.selectedMeasure rewardKernel
          (context i (History.finiteRewardHistoryOfTrace (reward omega) i))
          (action omega (i + 1)))
      (ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i))) := by
  have h_action_policy_eq :
      Filter.Eventually
        (fun omega : Omega =>
          action omega (i + 1) =
            (policy i).action
              (state i
                (History.finiteRewardHistoryOfTrace (reward omega) i)))
        (ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i))) := by
    exact Filter.Eventually.of_forall (fun omega => by
      have h_point := congrFun (congrFun h_action_generated omega) (i + 1)
      simpa [Policy.generatedActionTraceSucc] using h_point)
  exact
    reward_condExpKernel_map_eq_selected_actual_action_of_actionRewardPartialTrajectoryKernel_extend_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace
      (mu := mu)
      (action := action)
      (rewardKernel := rewardKernel)
      (policy := policy)
      (context := context)
      (state := state)
      (hcontext := hcontext)
      (hstate := hstate)
      (reward := reward)
      (haction := haction)
      (hreward := hreward)
      (i := i)
      h_action_policy_eq
      h_kernel_extend_map_eq

/--
Generated-action and actual-action reward law source for the full finite
pair-trace `partialTraj` law.

This exposes the trajectory-law part of the generated-history route without
also consuming the centered-reward kernel law.  The remaining external input is
the actual-action reward-coordinate conditional map law.
-/
theorem actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc_reward_map_eq_actual_action
    {Omega : Type u} {Context : Type v} {State : Type w} {Action : Type x}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (i : Nat)
    (h_action_generated :
      action =
        Policy.generatedActionTraceSucc policy
          (fun n omega =>
            state n (History.finiteRewardHistoryOfTrace (reward omega) n))
          defaultAction)
    (h_reward_map_eq_actual_action :
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega Rat mOmega inferInstance
            (fun y : Omega => reward y (i + 1))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          RewardKernel.selectedMeasure rewardKernel
            (context i
              (History.finiteRewardHistoryOfTrace (reward omega) i))
            (action omega (i + 1)))
        (ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.Eventually
      (fun omega : Omega =>
        @Measure.map Omega ((j : Finset.Iic (i + 1)) -> Prod Action Rat)
          mOmega inferInstance
          (fun y : Omega =>
            History.finitePairHistoryOfTrace (action y) (reward y) (i + 1))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
            ((History.historyFiltrationSucc action reward haction hreward) i)
            omega) =
        RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
          (fun n history =>
            context n (History.pairHistoryRewardProjection history))
          (fun n history =>
            state n (History.pairHistoryRewardProjection history))
          (fun n : Nat =>
            (hcontext n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          (fun n : Nat =>
            (hstate n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          i (i + 1)
          (History.finitePairHistoryOfTrace
            (action omega) (reward omega) i))
      (ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i))) := by
  have h_kernel_extend_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega ((j : Finset.Iic (i + 1)) -> Prod Action Rat)
            mOmega inferInstance
            (fun y : Omega =>
              History.extendPairHistorySucc
                (History.finitePairHistoryOfTrace
                  (action omega) (reward omega) i)
                (action y (i + 1), reward y (i + 1)))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
            (fun n history =>
              context n (History.pairHistoryRewardProjection history))
            (fun n history =>
              state n (History.pairHistoryRewardProjection history))
            (fun n : Nat =>
              (hcontext n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            (fun n : Nat =>
              (hstate n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            i (i + 1)
            (History.finitePairHistoryOfTrace
              (action omega) (reward omega) i))
        (ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i))) :=
    actionRewardPartialTrajectoryKernel_extend_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc_reward_map_eq_actual_action
      (mu := mu)
      (action := action)
      (rewardKernel := rewardKernel)
      (policy := policy)
      (context := context)
      (state := state)
      (hcontext := hcontext)
      (hstate := hstate)
      (defaultAction := defaultAction)
      (reward := reward)
      (haction := haction)
      (hreward := hreward)
      (i := i)
      h_action_generated
      h_reward_map_eq_actual_action
  exact
    actionRewardPartialTrajectoryKernel_map_eq_of_extend_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace
      (mu := mu)
      (action := action)
      (rewardKernel := rewardKernel)
      (policy := policy)
      (context := context)
      (state := state)
      (hcontext := hcontext)
      (hstate := hstate)
      (reward := reward)
      (haction := haction)
      (hreward := hreward)
      (i := i)
      h_kernel_extend_map_eq

/--
Generated-history route from an extension-map `partialTraj` law assumption.

This is the next narrowing of the `partialTraj`/`condExpKernel` gap.  Instead
of requiring a law identity for the full `i + 1` trace restriction, it only
requires the conditional kernel pushed through the deterministic extension of
the frozen old pair prefix by the random next `(Action, Reward)` pair to agree
with the one-step action/reward `partialTraj` kernel.  The compiled
successor-decomposition bridge supplies the conversion back to the existing
full-trace consumer.
-/
theorem centeredReward_succ_condExp_eq_zero_of_actionRewardPartialTrajectoryKernel_extend_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace
    {Omega : Type u} {Context : Type v} {State : Type w} {Action : Type x}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (law :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (i : Nat)
    (h_integrable :
      Integrable
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))) mu)
    (h_kernel_extend_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega ((j : Finset.Iic (i + 1)) -> Prod Action Rat)
            mOmega inferInstance
            (fun y : Omega =>
              History.extendPairHistorySucc
                (History.finitePairHistoryOfTrace
                  (action omega) (reward omega) i)
                (action y (i + 1), reward y (i + 1)))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
            (fun n history =>
              context n (History.pairHistoryRewardProjection history))
            (fun n history =>
              state n (History.pairHistoryRewardProjection history))
            (fun n : Nat =>
              (hcontext n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            (fun n : Nat =>
              (hstate n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            i (i + 1)
            (History.finitePairHistoryOfTrace
              (action omega) (reward omega) i))
        (ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.EventuallyEq (ae mu)
      (@condExp Omega Real
        ((History.historyFiltrationSucc action reward haction hreward) i)
        mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))))
      (fun _omega : Omega => (0 : Real)) := by
  have h_kernel_partialtraj_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega ((j : Finset.Iic (i + 1)) -> Prod Action Rat)
            mOmega inferInstance
            (fun y : Omega =>
              History.finitePairHistoryOfTrace (action y) (reward y) (i + 1))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
            (fun n history =>
              context n (History.pairHistoryRewardProjection history))
            (fun n history =>
              state n (History.pairHistoryRewardProjection history))
            (fun n : Nat =>
              (hcontext n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            (fun n : Nat =>
              (hstate n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            i (i + 1)
            (History.finitePairHistoryOfTrace
              (action omega) (reward omega) i))
        (ae
          (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i))) := by
    exact
      actionRewardPartialTrajectoryKernel_map_eq_of_extend_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace
        (mu := mu)
        (action := action)
        (rewardKernel := rewardKernel)
        (policy := policy)
        (context := context)
        (state := state)
        (hcontext := hcontext)
        (hstate := hstate)
        (reward := reward)
        (haction := haction)
        (hreward := hreward)
        (i := i)
        h_kernel_extend_map_eq
  exact
    centeredReward_succ_condExp_eq_zero_of_actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace
      (mu := mu)
      (action := action)
      (rewardKernel := rewardKernel)
      (policy := policy)
      (context := context)
      (state := state)
      (hcontext := hcontext)
      (hstate := hstate)
      (mean := mean)
      (varianceProxy := varianceProxy)
      (law := law)
      (reward := reward)
      (haction := haction)
      (hreward := hreward)
      (i := i)
      h_integrable
      h_kernel_partialtraj_map_eq

/--
Generated-action and actual-action reward law source for succ-indexed
conditional mean-zero.

This is the current narrowest compiled consumer on the adaptive pair-law route:
it combines the shifted generated-action trace, an actual-action
reward-coordinate conditional map law, the extension-map `partialTraj` bridge,
and the centered-reward law transfer to produce ordinary conditional
mean-zero.  It still assumes the actual-action reward-coordinate law rather
than constructing it from an ambient trajectory measure.
-/
theorem centeredReward_succ_condExp_eq_zero_of_generatedActionTraceSucc_reward_map_eq_actual_action
    {Omega : Type u} {Context : Type v} {State : Type w} {Action : Type x}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (law :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (i : Nat)
    (h_action_generated :
      action =
        Policy.generatedActionTraceSucc policy
          (fun n omega =>
            state n (History.finiteRewardHistoryOfTrace (reward omega) n))
          defaultAction)
    (h_integrable :
      Integrable
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))) mu)
    (h_reward_map_eq_actual_action :
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega Rat mOmega inferInstance
            (fun y : Omega => reward y (i + 1))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          RewardKernel.selectedMeasure rewardKernel
            (context i
              (History.finiteRewardHistoryOfTrace (reward omega) i))
            (action omega (i + 1)))
        (ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.EventuallyEq (ae mu)
      (@condExp Omega Real
        ((History.historyFiltrationSucc action reward haction hreward) i)
        mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))))
      (fun _omega : Omega => (0 : Real)) := by
  have h_kernel_partialtraj_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega ((j : Finset.Iic (i + 1)) -> Prod Action Rat)
            mOmega inferInstance
            (fun y : Omega =>
              History.finitePairHistoryOfTrace (action y) (reward y) (i + 1))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
            (fun n history =>
              context n (History.pairHistoryRewardProjection history))
            (fun n history =>
              state n (History.pairHistoryRewardProjection history))
            (fun n : Nat =>
              (hcontext n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            (fun n : Nat =>
              (hstate n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            i (i + 1)
            (History.finitePairHistoryOfTrace
              (action omega) (reward omega) i))
        (ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i))) :=
    actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc_reward_map_eq_actual_action
      (mu := mu)
      (action := action)
      (rewardKernel := rewardKernel)
      (policy := policy)
      (context := context)
      (state := state)
      (hcontext := hcontext)
      (hstate := hstate)
      (defaultAction := defaultAction)
      (reward := reward)
      (haction := haction)
      (hreward := hreward)
      (i := i)
      h_action_generated
      h_reward_map_eq_actual_action
  exact
    centeredReward_succ_condExp_eq_zero_of_actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace
      (mu := mu)
      (action := action)
      (rewardKernel := rewardKernel)
      (policy := policy)
      (context := context)
      (state := state)
      (hcontext := hcontext)
      (hstate := hstate)
      (mean := mean)
      (varianceProxy := varianceProxy)
      (law := law)
      (reward := reward)
      (haction := haction)
      (hreward := hreward)
      (i := i)
      h_integrable
      h_kernel_partialtraj_map_eq

/--
Actual-action pair-product law source for the full finite-pair-trace
`partialTraj` law.

This exposes the trajectory-law layer that was previously only consumed inside
the centered-reward theorem: an actual-action pair-product conditional law is
first marginalized to the actual-action reward-coordinate law, then the
generated-action route turns it into the full `i + 1` finite pair-trace
`partialTraj` law.
-/
theorem actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc_pair_map_eq_actual_action
    {Omega : Type u} {Context : Type v} {State : Type w} {Action : Type x}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (i : Nat)
    (h_action_generated :
      action =
        Policy.generatedActionTraceSucc policy
          (fun n omega =>
            state n (History.finiteRewardHistoryOfTrace (reward omega) n))
          defaultAction)
    (h_pair_map_eq_actual_action :
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega (Prod Action Rat) mOmega inferInstance
            (fun y : Omega => (action omega (i + 1), reward y (i + 1)))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          Measure.map
            (Prod.mk (action omega (i + 1)))
            (RewardKernel.selectedMeasure rewardKernel
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              (action omega (i + 1))))
        (ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.Eventually
      (fun omega : Omega =>
        @Measure.map Omega ((j : Finset.Iic (i + 1)) -> Prod Action Rat)
          mOmega inferInstance
          (fun y : Omega =>
            History.finitePairHistoryOfTrace (action y) (reward y) (i + 1))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
            ((History.historyFiltrationSucc action reward haction hreward) i)
            omega) =
        RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
          (fun n history =>
            context n (History.pairHistoryRewardProjection history))
          (fun n history =>
            state n (History.pairHistoryRewardProjection history))
          (fun n : Nat =>
            (hcontext n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          (fun n : Nat =>
            (hstate n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          i (i + 1)
          (History.finitePairHistoryOfTrace
            (action omega) (reward omega) i))
      (ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i))) := by
  have h_reward_map_eq_actual_action :
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega Rat mOmega inferInstance
            (fun y : Omega => reward y (i + 1))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          RewardKernel.selectedMeasure rewardKernel
            (context i
              (History.finiteRewardHistoryOfTrace (reward omega) i))
            (action omega (i + 1)))
        (ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i))) := by
    exact
      reward_condExpKernel_map_eq_selected_actual_action_of_pair_map_eq
        (mu := mu)
        (F := History.historyFiltrationSucc action reward haction hreward)
        (rewardKernel := rewardKernel)
        (pairContext := fun n history =>
          context n (History.pairHistoryRewardProjection history))
        (action := action)
        (reward := reward)
        (i := i)
        (pairHistory := fun omega : Omega =>
          History.finitePairHistoryOfTrace (action omega) (reward omega) i)
        (h_reward_next := hreward (i + 1))
        (by
          simpa [History.pairHistoryRewardProjection_finitePairHistoryOfTrace]
            using h_pair_map_eq_actual_action)
  exact
    actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc_reward_map_eq_actual_action
      (mu := mu)
      (action := action)
      (rewardKernel := rewardKernel)
      (policy := policy)
      (context := context)
      (state := state)
      (hcontext := hcontext)
      (hstate := hstate)
      (defaultAction := defaultAction)
      (reward := reward)
      (haction := haction)
      (hreward := hreward)
      (i := i)
      h_action_generated
      h_reward_map_eq_actual_action

/--
Actual-action pair-product law source for generated-action conditional
mean-zero.

This packages one more upstream law shape: if the conditional kernel identifies
the pair `(actual next action, next reward)` with the selected reward law pushed
through `Prod.mk` at the actual next action, then `Prod.snd` marginalization
provides the actual-action reward-coordinate law required by
`centeredReward_succ_condExp_eq_zero_of_generatedActionTraceSucc_reward_map_eq_actual_action`.
-/
theorem centeredReward_succ_condExp_eq_zero_of_generatedActionTraceSucc_pair_map_eq_actual_action
    {Omega : Type u} {Context : Type v} {State : Type w} {Action : Type x}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (law :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (i : Nat)
    (h_action_generated :
      action =
        Policy.generatedActionTraceSucc policy
          (fun n omega =>
            state n (History.finiteRewardHistoryOfTrace (reward omega) n))
          defaultAction)
    (h_integrable :
      Integrable
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))) mu)
    (h_pair_map_eq_actual_action :
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega (Prod Action Rat) mOmega inferInstance
            (fun y : Omega => (action omega (i + 1), reward y (i + 1)))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          Measure.map
            (Prod.mk (action omega (i + 1)))
            (RewardKernel.selectedMeasure rewardKernel
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              (action omega (i + 1))))
        (ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.EventuallyEq (ae mu)
      (@condExp Omega Real
        ((History.historyFiltrationSucc action reward haction hreward) i)
        mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))))
      (fun _omega : Omega => (0 : Real)) := by
  have h_kernel_partialtraj_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega ((j : Finset.Iic (i + 1)) -> Prod Action Rat)
            mOmega inferInstance
            (fun y : Omega =>
              History.finitePairHistoryOfTrace (action y) (reward y) (i + 1))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
            (fun n history =>
              context n (History.pairHistoryRewardProjection history))
            (fun n history =>
              state n (History.pairHistoryRewardProjection history))
            (fun n : Nat =>
              (hcontext n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            (fun n : Nat =>
              (hstate n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            i (i + 1)
            (History.finitePairHistoryOfTrace
              (action omega) (reward omega) i))
        (ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i))) :=
    actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc_pair_map_eq_actual_action
      (mu := mu)
      (action := action)
      (rewardKernel := rewardKernel)
      (policy := policy)
      (context := context)
      (state := state)
      (hcontext := hcontext)
      (hstate := hstate)
      (defaultAction := defaultAction)
      (reward := reward)
      (haction := haction)
      (hreward := hreward)
      (i := i)
      h_action_generated
      h_pair_map_eq_actual_action
  exact
    centeredReward_succ_condExp_eq_zero_of_actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace
      (mu := mu)
      (action := action)
      (rewardKernel := rewardKernel)
      (policy := policy)
      (context := context)
      (state := state)
      (hcontext := hcontext)
      (hstate := hstate)
      (mean := mean)
      (varianceProxy := varianceProxy)
      (law := law)
      (reward := reward)
      (haction := haction)
      (hreward := hreward)
      (i := i)
      h_integrable
      h_kernel_partialtraj_map_eq

/--
Fully-random next-pair product law source for the full finite-pair-trace
`partialTraj` law.

The hypothesis may state the conditional law of the sampled pair
`(action y (i+1), reward y (i+1))`.  The shifted generated-action trace freezes
that action coordinate to the actual/policy-selected action under the
conditional kernel, after which the actual-action pair-product adapter produces
the full trace law.
-/
theorem actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc_random_pair_map_eq_actual_action
    {Omega : Type u} {Context : Type v} {State : Type w} {Action : Type x}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (i : Nat)
    (h_action_generated :
      action =
        Policy.generatedActionTraceSucc policy
          (fun n omega =>
            state n (History.finiteRewardHistoryOfTrace (reward omega) n))
          defaultAction)
    (h_random_pair_map_eq_actual_action :
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega (Prod Action Rat) mOmega inferInstance
            (fun y : Omega => (action y (i + 1), reward y (i + 1)))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          Measure.map
            (Prod.mk (action omega (i + 1)))
            (RewardKernel.selectedMeasure rewardKernel
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              (action omega (i + 1))))
        (ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.Eventually
      (fun omega : Omega =>
        @Measure.map Omega ((j : Finset.Iic (i + 1)) -> Prod Action Rat)
          mOmega inferInstance
          (fun y : Omega =>
            History.finitePairHistoryOfTrace (action y) (reward y) (i + 1))
          (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
            ((History.historyFiltrationSucc action reward haction hreward) i)
            omega) =
        RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
          (fun n history =>
            context n (History.pairHistoryRewardProjection history))
          (fun n history =>
            state n (History.pairHistoryRewardProjection history))
          (fun n : Nat =>
            (hcontext n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          (fun n : Nat =>
            (hstate n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          i (i + 1)
          (History.finitePairHistoryOfTrace
            (action omega) (reward omega) i))
      (ae
        (mu.trim
          ((History.historyFiltrationSucc action reward haction hreward).le
            i))) := by
  have h_action_generated_pair :
      action =
        Policy.generatedActionTraceSucc policy
          (fun n omega =>
            state n
              (History.pairHistoryRewardProjection
                (History.finitePairHistoryOfTrace
                  (action omega) (reward omega) n)))
          defaultAction := by
    simpa [History.pairHistoryRewardProjection_finitePairHistoryOfTrace]
      using h_action_generated
  have h_pair_map_eq_actual_action :
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega (Prod Action Rat) mOmega inferInstance
            (fun y : Omega => (action omega (i + 1), reward y (i + 1)))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          Measure.map
            (Prod.mk (action omega (i + 1)))
            (RewardKernel.selectedMeasure rewardKernel
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              (action omega (i + 1))))
        (ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i))) := by
    have h_pair_map_eq_projected :
        Filter.Eventually
          (fun omega : Omega =>
            @Measure.map Omega (Prod Action Rat) mOmega inferInstance
              (fun y : Omega => (action omega (i + 1), reward y (i + 1)))
              (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
                ((History.historyFiltrationSucc action reward haction hreward) i)
                omega) =
            Measure.map
              (Prod.mk (action omega (i + 1)))
              (RewardKernel.selectedMeasure rewardKernel
                ((fun n history =>
                    context n (History.pairHistoryRewardProjection history)) i
                  (History.finitePairHistoryOfTrace
                    (action omega) (reward omega) i))
                (action omega (i + 1))))
          (ae
            (mu.trim
              ((History.historyFiltrationSucc action reward haction hreward).le
                i))) := by
      exact
        pair_condExpKernel_map_eq_frozen_actual_action_of_generatedActionTraceSucc_random_pair_map_eq
          (mu := mu)
          (rewardKernel := rewardKernel)
          (policy := policy)
          (pairContext := fun n history =>
            context n (History.pairHistoryRewardProjection history))
          (pairState := fun n history =>
            state n (History.pairHistoryRewardProjection history))
          (hpairState := fun n : Nat =>
            (hstate n).comp
              (History.measurable_pairHistoryRewardProjection
                (Action := Action) (Reward := Rat) n))
          (defaultAction := defaultAction)
          (action := action)
          (reward := reward)
          (haction := haction)
          (hreward := hreward)
          (i := i)
          h_action_generated_pair
          (by
            simpa [History.pairHistoryRewardProjection_finitePairHistoryOfTrace]
              using h_random_pair_map_eq_actual_action)
    simpa [History.pairHistoryRewardProjection_finitePairHistoryOfTrace]
      using h_pair_map_eq_projected
  exact
    actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc_pair_map_eq_actual_action
      (mu := mu)
      (action := action)
      (rewardKernel := rewardKernel)
      (policy := policy)
      (context := context)
      (state := state)
      (hcontext := hcontext)
      (hstate := hstate)
      (defaultAction := defaultAction)
      (reward := reward)
      (haction := haction)
      (hreward := hreward)
      (i := i)
      h_action_generated
      h_pair_map_eq_actual_action

/--
Random next-pair product law source for generated-action conditional
mean-zero.

This is a slightly more trajectory-facing consumer than
`..._pair_map_eq_actual_action`: the law hypothesis may state the conditional
pushforward of the fully random next pair `(action y (i+1), reward y (i+1))`.
The generated-action trace freezes the action coordinate, after which the
existing actual-action pair-product consumer handles the centered-reward
conditional expectation.
-/
theorem centeredReward_succ_condExp_eq_zero_of_generatedActionTraceSucc_random_pair_map_eq_actual_action
    {Omega : Type u} {Context : Type v} {State : Type w} {Action : Type x}
    [mOmega : MeasurableSpace Omega] [StandardBorelSpace Omega]
    [MeasurableSpace Context] [MeasurableSpace State]
    [MeasurableSpace Action] [MeasurableSingletonClass Action]
    [Countable Action]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (action : Omega -> ActionTrace Action)
    (rewardKernel : RewardKernel.MarkovRewardKernel (Prod Context Action) Rat)
    (policy : Nat -> Policy.MeasurablePolicy State Action)
    (context : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> Context)
    (state : (n : Nat) -> ((j : Finset.Iic n) -> Rat) -> State)
    (hcontext : forall n : Nat, Measurable (context n))
    (hstate : forall n : Nat, Measurable (state n))
    (mean : Context -> Action -> Rat)
    (varianceProxy : Context -> Action -> NNReal)
    (law :
      RewardKernel.CenteredRewardKernelLaw rewardKernel mean varianceProxy)
    (defaultAction : Action)
    (reward : Omega -> RewardTrace Rat)
    (haction : forall t : Nat,
      Measurable (fun omega : Omega => action omega t))
    (hreward : forall t : Nat,
      Measurable (fun omega : Omega => reward omega t))
    (i : Nat)
    (h_action_generated :
      action =
        Policy.generatedActionTraceSucc policy
          (fun n omega =>
            state n (History.finiteRewardHistoryOfTrace (reward omega) n))
          defaultAction)
    (h_integrable :
      Integrable
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))) mu)
    (h_random_pair_map_eq_actual_action :
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega (Prod Action Rat) mOmega inferInstance
            (fun y : Omega => (action y (i + 1), reward y (i + 1)))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          Measure.map
            (Prod.mk (action omega (i + 1)))
            (RewardKernel.selectedMeasure rewardKernel
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              (action omega (i + 1))))
        (ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i)))) :
    Filter.EventuallyEq (ae mu)
      (@condExp Omega Real
        ((History.historyFiltrationSucc action reward haction hreward) i)
        mOmega _ _ _ mu
        (fun omega : Omega =>
          (((reward omega (i + 1) -
            mean
              (context i
                (History.finiteRewardHistoryOfTrace (reward omega) i))
              ((policy i).action
                (state i
                  (History.finiteRewardHistoryOfTrace (reward omega) i))) :
                Rat) : Real))))
      (fun _omega : Omega => (0 : Real)) := by
  have h_kernel_partialtraj_map_eq :
      Filter.Eventually
        (fun omega : Omega =>
          @Measure.map Omega ((j : Finset.Iic (i + 1)) -> Prod Action Rat)
            mOmega inferInstance
            (fun y : Omega =>
              History.finitePairHistoryOfTrace (action y) (reward y) (i + 1))
            (@ProbabilityTheory.condExpKernel Omega mOmega _ mu _
              ((History.historyFiltrationSucc action reward haction hreward) i)
              omega) =
          RewardKernel.actionRewardPartialTrajectoryKernel rewardKernel policy
            (fun n history =>
              context n (History.pairHistoryRewardProjection history))
            (fun n history =>
              state n (History.pairHistoryRewardProjection history))
            (fun n : Nat =>
              (hcontext n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            (fun n : Nat =>
              (hstate n).comp
                (History.measurable_pairHistoryRewardProjection
                  (Action := Action) (Reward := Rat) n))
            i (i + 1)
            (History.finitePairHistoryOfTrace
              (action omega) (reward omega) i))
        (ae
          (mu.trim
            ((History.historyFiltrationSucc action reward haction hreward).le
              i))) :=
    actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace_of_generatedActionTraceSucc_random_pair_map_eq_actual_action
      (mu := mu)
      (action := action)
      (rewardKernel := rewardKernel)
      (policy := policy)
      (context := context)
      (state := state)
      (hcontext := hcontext)
      (hstate := hstate)
      (defaultAction := defaultAction)
      (reward := reward)
      (haction := haction)
      (hreward := hreward)
      (i := i)
      h_action_generated
      h_random_pair_map_eq_actual_action
  exact
    centeredReward_succ_condExp_eq_zero_of_actionRewardPartialTrajectoryKernel_map_eq_historyFiltrationSucc_finitePairHistoryOfTrace
      (mu := mu)
      (action := action)
      (rewardKernel := rewardKernel)
      (policy := policy)
      (context := context)
      (state := state)
      (hcontext := hcontext)
      (hstate := hstate)
      (mean := mean)
      (varianceProxy := varianceProxy)
      (law := law)
      (reward := reward)
      (haction := haction)
      (hreward := hreward)
      (i := i)
      h_integrable
      h_kernel_partialtraj_map_eq

end ConditionalExpectationReward
end BanditRLProof
