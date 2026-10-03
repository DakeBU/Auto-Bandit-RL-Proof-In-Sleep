# Noisy unknown-player-count learner canary

This scratch canary instantiates the existing frozen static Musical Chairs
contract: n=2, k=3, independent Bernoulli arm means (3/4,1/2,1/4), epsilon=1/8.
It fixes delta=1/4 and uses exactly S=explorationLength(3,1/8,1/4), not a smaller
test duration. It retains the previously disclosed source-budget repair. The
source is Rosenski--Shamir--Szlak, ICML 2016, static Algorithms 1/2 and Theorem 1;
the source hashes and canary requirements are in MULTI-AGENT-CONTRACT.md.

## Reward laws and actual learner endpoint

Each law is the real measure (1-p_a) dirac(0) + p_a dirac(1). Probability,
[0,1] support and the integral of any real function are proved. Consequently
armMean(law) is exactly (3/4,1/2,1/4). Both {0} and {1} have strictly positive
mass for every arm: this is a genuinely noisy example, not means supplied as
deterministic observations. The fixed ordered list is [0,1,2], the top set is
{0,1}, and the numeric second-to-third boundary gap is exactly 1/4.

Let G be the actual explorationGoodEvent, computed from each player's own
exploration feedback. The source producer gives P(G)>=3/4 at the prescribed
duration. For every z in G and each player, the actual local population estimate
is 2 and its local candidate set is {0,1}. Those correct values are derived on
G; they are not supplied to the algorithm or assumed for all histories.

The actual complete visible-law endpoint specializes, for every natural H, to

    E_visible[R_H] <= min(2 H, 2 S + 32 + H/2).

This instantiates the prior primitive-law theorem with the proved support,
mean and gap conditions. It includes H=0 and H<S and retains the failure
residual H/2. It is an unconditional expected regret bound, not a conditional
realized bound. No simulation or numerical approximation to S is used.

## A positive-probability transient under the learned law

Consider the continuation private-draw path d of length two:
both players draw arm 0 first; then player 0 draws arm 0 and player 1 draws
arm 1. On the first round both collide and remain unfixed; on the second they
separate and fix. The actual pathCoordinationRegret is exactly 5/4.

On G, the learned kernel is the independent uniform product over {0,1} for
both players. Each allowed joint draw has mass 1/4, so this two-round path has
mass 1/16. The previously proved same-law rectangle identity yields exactly

    P_joint(G × {d}) = P_exploration(G) / 16 >= 3/64.

This statement integrates over actual noisy exploration histories and actual
unknown-N estimation. It does not replace the learned kernel outside G with
externally supplied correct candidates. On the event, the exact 5/4 charge
uses armMean(law) and trueTopArms(law), not a separate reference score.

The complete law at H=S+2 adds the fresh independent reward array. Its first
marginal is the learned exploration/continuation law; the preimage event has
the same probability, hence at least 3/64. The finite-index cast is explicit.
All future rewards remain random. The 5/4 calculation is pseudo-regret on the
transient draw path, not a claim that every future reward realization has the
same deficit.

## Observation and ranking diagnostics

For either player and any arm, the actual uniform exploration-draw law gives
effective observation probability 2/9. Either player's collision probability
is 1/3. These are the same one-round PMFs used by the iid exploration law.

The actual feedback definitions distinguish collided=true/reward=0 from
collided=false/reward=0. The named zero-bit diagnostic reuses the preceding
small trace fixtures; the new arm-law theorem proves genuine zero rewards
have positive mass. No probability for either complete diagnostic trace is
claimed. Swapping the two top scores changes their internal ranking while
preserving the top set, and on G each player's actual learned set equals this
same set. This does not assume or prove identical empirical score orderings
between players.

## Evidence and limits

Focused compilation covers the entire actual-law scratch prefix and this
canary. All new declarations and the probability instance are separately
axiom-audited; independent blind and source review are recorded in the receipt.
These are symbolic probability and performance proofs. They are not empirical
Monte Carlo results, a numerical execution trace of the large exploration
duration, or a controlled measurement of formalization efficiency.

The canary supplies a real consumer of the whole learner endpoint and a
positive-probability nonzero coordination witness. Public-root canary acceptance
still requires extracting the scratch chain into shared modules and running
the combined root, Tests, harness, registry and site gates. Recent-source
comparison and ICLR evidence remain mandatory. Topic completion remains false;
the overall Goal remains active with 0/10 topics complete.

The following is the exact new layer; its unchanged preceding context is
MusicalChairsRealizedPrototype.lean SHA256
ac6f6a16052b8ca8ef1e4f5ddcaf5c9e75c95cdb2b696b7749b2d0ad4f1f4462.

<details>
<summary>Exact new Lean declarations and proofs</summary>

```lean
namespace BanditRLProof.MusicalChairs.NoisyLearnerCanary
open MeasureTheory ProbabilityTheory

noncomputable def successMass (a : Fin 3) : ℝ≥0∞ :=
  ENNReal.ofReal (MarginalCanary.means a)

noncomputable def law (a : Fin 3) : Measure ℝ :=
  ENNReal.ofReal (1-MarginalCanary.means a) • Measure.dirac 0 + successMass a • Measure.dirac 1

instance law_probability (a : Fin 3) : IsProbabilityMeasure (law a) := by
  constructor
  fin_cases a <;> norm_num [law,successMass,MarginalCanary.means, ← ENNReal.ofReal_add]

theorem law_bounded (a : Fin 3) : ∀ᵐ y ∂law a, y ∈ Set.Icc (0 : ℝ) 1 := by
  unfold law
  apply ae_add_measure_iff.mpr
  constructor <;> apply Measure.ae_smul_measure <;> simp


theorem law_integral (a : Fin 3) (g : ℝ → ℝ) :
    (∫ y, g y ∂law a) = (1-(successMass a).toReal)*g 0 + (successMass a).toReal*g 1 := by
  fin_cases a <;> rw [law,integral_add_measure]
  all_goals try { exact (integrable_dirac (by finiteness)).smul_measure (by simp [successMass]) }
  all_goals norm_num [successMass, MarginalCanary.means, integral_smul_measure]

theorem actual_means : armMean law = MarginalCanary.means := by
  funext a
  rw [armMean,law_integral]
  fin_cases a <;> norm_num [successMass,MarginalCanary.means]

theorem success_and_failure_positive (a : Fin 3) : 0 < law a {1} ∧ 0 < law a {0} := by
  fin_cases a <;> norm_num [law,successMass,MarginalCanary.means,Measure.add_apply,Measure.smul_apply]

theorem top_set : trueTopArms law 2 = ({0,1} : Finset (Fin 3)) := by
  rw [trueTopArms,actual_means]
  apply topArms_eq_of_strict_separation _ 2 _ (by decide) (by decide)
  intro a ha b hb
  fin_cases a <;> fin_cases b <;> norm_num [MarginalCanary.means] at *

theorem ranked_list : rankedArms (armMean law) = [0,1,2] := by
  rw [actual_means]
  have hu : ([0,1,2] : List (Fin 3)).toFinset = Finset.univ := by decide
  unfold rankedArms
  rw [← hu]
  apply (List.toFinset_sort (r := scoreOrder MarginalCanary.means) (by decide)).2
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  norm_num [List.pairwise_cons, scoreOrder, MarginalCanary.means,h20,h21,h20.symm,h21.symm]

theorem numeric_gap : boundaryGap (armMean law) 2 (by decide) (by decide) = 1/4 := by
  have hs : rankedArms MarginalCanary.means = [0,1,2] := by
    simpa only [actual_means] using ranked_list
  rw [actual_means]
  norm_num [boundaryGap,rankedArm,hs,MarginalCanary.means, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide]

noncomputable def duration : ℕ := explorationLength 3 (1/8) (1/4)
noncomputable def good : Set ((Fin duration → Fin 2 → Fin 3) × (Fin duration → Fin 3 → ℝ)) :=
  explorationGoodEvent (n := 2) (trueTopArms law 2)

theorem measurable_good : MeasurableSet good := by
  apply measurableSet_explorationGoodEvent
  rw [top_set]
  decide

theorem learned_good_probability : (3/4 : ℝ≥0∞) ≤ explorationRewardLaw (by decide) law good := by
  have h := explorationGoodEvent_orderStatistic_probability (n := 2) (by decide) (by decide)
    law law_bounded (1/8) (1/4) (by norm_num) (by rw [numeric_gap]; norm_num) (by norm_num) (by norm_num)
  have he : (1 : ℝ≥0∞)-ENNReal.ofReal (1/4 : ℝ) = 3/4 := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 (by norm_num)]
    norm_num [ENNReal.ofReal_div_of_pos]
  rw [he] at h
  exact h

theorem actual_visible_regret_bound (H : ℕ) :
    (∫ f, visibleRegret (n := 2) (H := H) (armMean law) f
      ∂visibleLearnerLaw (S := duration) (by decide) law) ≤
      min (2*H : ℝ) (2*duration + 32 + (1/2 : ℝ)*H) := by
  have h := source_expected_visibleRegret_le (H := H) (n := 2) (by decide) (by decide)
    law law_bounded (1/8) (1/4) (by norm_num) (by rw [numeric_gap]; norm_num) (by norm_num) (by norm_num)
  have hr : (2 : ℝ)*explorationLength 3 (1/8) (1/4) + 8*(2 : ℝ)^2 + (1/4 : ℝ)*(2*H) =
      2*duration + 32 + (1/2 : ℝ)*H := by
    dsimp [duration]
    ring
  simpa only [Nat.cast_ofNat,hr] using h

theorem transient_iid_mass :
    (FinitePMF.iid (jointDraw (fun _ : Fin 2 => ({0,1} : Finset (Fin 3)))
      (fun _ => by simp)) 2).toMeasure {MarginalCanary.transientDraws} = (1/16 : ℝ≥0∞) := by
  rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _), FinitePMF.iid_apply]
  have h (t : Fin 2) : jointDraw (fun _ : Fin 2 => ({0,1} : Finset (Fin 3)))
      (fun _ => by simp) (MarginalCanary.transientDraws t) = (1/4 : ℝ≥0∞) := by
    apply MarginalCanary.allowed_draw_mass
    intro i
    fin_cases t <;> fin_cases i <;> norm_num [MarginalCanary.transientDraws]
  simp_rw [h]
  norm_num [Fin.prod_univ_two, ← ENNReal.inv_pow]

theorem actual_good_transient_factorization :
    explorationContinuationLaw (by decide) law 2 (good ×ˢ {MarginalCanary.transientDraws}) =
      explorationRewardLaw (by decide) law good * (1/16 : ℝ≥0∞) := by
  have hg : good ⊆ explorationGoodEvent (n := 2) ({0,1} : Finset (Fin 3)) := by
    unfold good
    rw [top_set]
  rw [explorationContinuationLaw_rectangle_on_good (by decide) law {0,1} (by simp)
    good measurable_good hg, transient_iid_mass]

theorem actual_good_transient_lower : (3/64 : ℝ≥0∞) ≤
    explorationContinuationLaw (by decide) law 2 (good ×ˢ {MarginalCanary.transientDraws}) := by
  rw [actual_good_transient_factorization]
  calc
    _ = (3/4 : ℝ≥0∞)*(1/16) := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      norm_num
    _ ≤ _ := mul_le_mul' learned_good_probability le_rfl

theorem actual_transient_charge {z : ((Fin duration → Fin 2 → Fin 3) ×
    (Fin duration → Fin 3 → ℝ)) × (Fin 2 → Fin 2 → Fin 3)}
    (hz : z ∈ good ×ˢ {MarginalCanary.transientDraws}) :
    pathCoordinationRegret (by decide) (trueTopArms law 2) (armMean law) z.2 = 5/4 := by
  rw [show z.2 = MarginalCanary.transientDraws from hz.2,top_set,actual_means]
  exact MarginalCanary.actual_transient_regret

theorem exact_effective_observation (i : Fin 2) (a : Fin 3) :
    (explorationDraw 2 3 (by decide)).toOuterMeasure (observes i a) = (2/9 : ℝ≥0∞) := by
  rw [exploration_observes_probability]
  norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num

theorem exact_collision (i : Fin 2) :
    (explorationDraw 2 3 (by decide)).toOuterMeasure {x | ¬ CollisionFree x i} = (1/3 : ℝ≥0∞) := by
  rw [exploration_collision_probability]
  norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_sub_of_le (by norm_num [ENNReal.div_le_iff]) (by simp)]
  norm_num

theorem actual_local_recovery {z : (Fin duration → Fin 2 → Fin 3) × (Fin duration → Fin 3 → ℝ)}
    (hz : z ∈ good) (i : Fin 2) :
    localPopulationEstimate (explorationFeedback z.1 z.2 i) = 2 ∧
      localCandidateSet (explorationFeedback z.1 z.2 i) = ({0,1} : Finset (Fin 3)) := by
  have h := hz i
  rw [top_set] at h
  exact h

theorem within_top_order_invariant :
    topArms (armMean law) 2 = topArms RankingCanary.scrambledScores 2 := by
  change trueTopArms law 2 = _
  rw [top_set,RankingCanary.scrambled_candidates]

theorem zero_reward_bit_distinction :
    (explorationFeedback (fun _ : Fin 1 => fun _ : Fin 2 => (0 : Fin 3))
      (fun _ _ => (1 : ℝ)) 0 0).collided = true ∧
    (explorationFeedback (fun _ : Fin 1 => fun i : Fin 2 => (i.castLE (by decide) : Fin 3))
      (fun _ _ => (0 : ℝ)) 0 0).collided = false :=
  ⟨RealizedCanary.collision_zero_sensed.1,RealizedCanary.genuine_zero_not_collision.1⟩

theorem zero_reward_has_positive_mass (a : Fin 3) : 0 < law a {0} :=
  (success_and_failure_positive a).2

theorem actual_good_transient_lower_cast (L : ℕ) (hL : L = 2) : (3/64 : ℝ≥0∞) ≤
    explorationContinuationLaw (by decide) law L
      (good ×ˢ {fun t : Fin L => MarginalCanary.transientDraws (Fin.cast hL t)}) := by
  subst L
  exact actual_good_transient_lower

noncomputable def completeTransientEvent : Set (FullSample 2 3 duration (duration+2)) :=
  Prod.fst ⁻¹' (good ×ˢ {fun t : Fin (duration+2-duration) =>
    MarginalCanary.transientDraws (Fin.cast (Nat.add_sub_cancel_left duration 2) t)})

theorem complete_transient_event_lower : (3/64 : ℝ≥0∞) ≤
    completeLearnerLaw (by decide) law completeTransientEvent := by
  unfold completeTransientEvent
  rw [(completeLearnerLaw_first_preserving (n := 2) (S := duration) (H := duration+2)
    (by decide) law).measure_preimage (measurable_good.prod (MeasurableSet.singleton _)).nullMeasurableSet]
  exact actual_good_transient_lower_cast _ _

end BanditRLProof.MusicalChairs.NoisyLearnerCanary
```

</details>
