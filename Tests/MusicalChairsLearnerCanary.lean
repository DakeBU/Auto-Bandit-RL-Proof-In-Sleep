import BanditRLProof

open scoped Classical ENNReal
open MeasureTheory ProbabilityTheory
set_option autoImplicit false

namespace BanditRLProof.MusicalChairs.ExplorationCanary

theorem effective_probability :
    (explorationDraw 2 3 (by decide)).toOuterMeasure (observes (0 : Fin 2) (0 : Fin 3)) = 2/9 := by
  rw [exploration_observes_probability]
  norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num

theorem collision_probability :
    (explorationDraw 2 3 (by decide)).toOuterMeasure {draw | ¬ CollisionFree draw (0 : Fin 2)} = 1/3 := by
  rw [exploration_collision_probability]
  norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_sub_of_le (by norm_num [ENNReal.div_le_iff]) (by simp)]
  norm_num

theorem effective_pgf (T : ℕ) (z : ℝ≥0∞) :
    ∑ x, explorationLaw 2 3 T (by decide) x * z ^ observationCount (0 : Fin 2) (0 : Fin 3) x =
      ((2/9)*z+7/9)^T := by
  have h := observationCount_pgf (n := 2) (k := 3) (by decide) T (0 : Fin 2) (0 : Fin 3) z
  norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one] at h
  have hq : (1/3 : ℝ≥0∞) * (2/3) = 2/9 := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num
  have hc : (1 : ℝ≥0∞) - 2/9 = 7/9 := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    rw [ENNReal.toReal_sub_of_le (by norm_num [ENNReal.div_le_iff]) (by simp)]
    norm_num
  simpa only [hq, hc] using h

def mixedDraws : Fin 2 → Fin 2 → Fin 3 := fun t i =>
  if t = 0 then 0 else if i = 0 then 0 else 1

theorem mixed_counts : observationCount (0 : Fin 2) (0 : Fin 3) mixedDraws = 1 ∧
    collisionCount (0 : Fin 2) mixedDraws = 1 := by
  simp only [observationCount, collisionCount, FinitePMF.eventCount,
    Finset.card_eq_sum_ones, Finset.sum_filter, Fin.sum_univ_two]
  norm_num [mixedDraws, observes, CollisionFree, Fin.forall_fin_two]


theorem free_zero_reward :
    (explorationFeedback mixedDraws (fun _ _ => 0) (0 : Fin 2) (1 : Fin 2)).reward = 0 ∧
    (explorationFeedback mixedDraws (fun _ _ => 0) (0 : Fin 2) (1 : Fin 2)).collided = false := by
  norm_num [explorationFeedback, mixedDraws, CollisionFree, Fin.forall_fin_two]

theorem collision_zero_reward :
    (explorationFeedback mixedDraws (fun _ _ => 1) (0 : Fin 2) (0 : Fin 2)).reward = 0 ∧
    (explorationFeedback mixedDraws (fun _ _ => 1) (0 : Fin 2) (0 : Fin 2)).collided = true := by
  norm_num [explorationFeedback, mixedDraws, CollisionFree, Fin.forall_fin_two]

end BanditRLProof.MusicalChairs.ExplorationCanary

namespace BanditRLProof.MusicalChairs.RewardCanary

noncomputable def unitUniform : Measure ℝ := volume.restrict (Set.Icc 0 1)

instance unitUniform_probability : IsProbabilityMeasure unitUniform := by
  constructor
  norm_num [unitUniform, Measure.restrict_apply_univ]

theorem unitUniform_bounded : ∀ᵐ y ∂unitUniform, y ∈ Set.Icc (0 : ℝ) 1 := by
  exact ae_restrict_mem measurableSet_Icc

theorem continuous_reward_tail (eps : ℝ) (heps0 : 0 ≤ eps) (heps1 : eps ≤ 1) :
    explorationRewardLaw (n := 2) (T := 2) (by decide) (fun _ : Fin 3 => unitUniform)
      (meanBadEvent (fun _ : Fin 3 => unitUniform) (0 : Fin 2) (0 : Fin 3) eps) ≤
      ENNReal.ofReal (2 * Real.exp (-eps^2/24)) := by
  have h := meanBadEvent_exponential_bound (n := 2) (T := 2) (k := 3) (by decide) (by decide)
    (fun _ => unitUniform) (fun _ => unitUniform_bounded) (0 : Fin 2) (0 : Fin 3) eps heps0 heps1
  convert h using 1
  congr 3
  norm_num
  ring

theorem selected_single_value (r : Fin 2 → Fin 3 → ℝ) :
    selectedMean ({1} : Finset (Fin 2)) (0 : Fin 3) r = r 1 0 := by
  simp [selectedMean]

theorem selected_empty_zero (r : Fin 2 → Fin 3 → ℝ) :
    selectedMean (∅ : Finset (Fin 2)) (0 : Fin 3) r = 0 := by
  simp [selectedMean]

end BanditRLProof.MusicalChairs.RewardCanary

namespace BanditRLProof.MusicalChairs.CollisionCanary

theorem two_players_three_arms_mean : collisionProbReal 2 3 = 1/3 := by
  norm_num [collisionProbReal]

theorem mixed_local_rate (r : Fin 2 → Fin 3 → ℝ) :
    localCollisionRate ExplorationCanary.mixedDraws r (0 : Fin 2) = 1/2 := by
  rw [localCollisionRate_eq, ExplorationCanary.mixed_counts.2]
  norm_num

theorem informative_tail :
    (explorationLaw 2 3 9000 (by decide)).toMeasure
      (collisionBadEvent (k := 3) (T := 9000) (0 : Fin 2)) ≤ ENNReal.ofReal (1/10 : ℝ) := by
  have h := collisionBadEvent_bound (n := 2) (k := 3) (T := 9000) (by decide) (by decide) (0 : Fin 2)
  apply h.trans
  apply ENNReal.ofReal_le_ofReal
  norm_num
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos (20 : ℝ))]
  have he := Real.add_one_le_exp (20 : ℝ)
  linarith

end BanditRLProof.MusicalChairs.CollisionCanary

namespace BanditRLProof.MusicalChairs.PopulationCanary

theorem exact_mean_recovers_two : populationEstimate 3 30 10 = 2 := by
  apply populationEstimate_correct (n := 2) (by decide) (by decide) (by decide)
    (by decide) (by decide)
  norm_num [collisionProbReal]

theorem lower_margin_recovers_two : populationEstimate 3 30 9 = 2 := by
  apply populationEstimate_correct (n := 2) (by decide) (by decide) (by decide)
    (by decide) (by decide)
  norm_num [collisionProbReal]

theorem upper_margin_recovers_two : populationEstimate 3 30 11 = 2 := by
  apply populationEstimate_correct (n := 2) (by decide) (by decide) (by decide)
    (by decide) (by decide)
  norm_num [collisionProbReal]

theorem zero_collision_returns_one : populationEstimate 3 30 0 = 1 :=
  populationEstimate_zero_collision (by decide) (by decide)

theorem all_collision_returns_cap : populationEstimate 3 30 30 = 3 :=
  populationEstimate_all_collision 3 30

def draws : Fin 3 → Fin 2 → Fin 3 := fun t i =>
  if t = 0 then 0 else if i = 0 then 0 else 1

theorem actual_collision_count : collisionCount (0 : Fin 2) draws = 1 := by
  norm_num [collisionCount, FinitePMF.eventCount, draws, CollisionFree, Fin.forall_fin_two,
    Finset.filter_eq']

theorem actual_local_estimate (r : Fin 3 → Fin 3 → ℝ) :
    localPopulationEstimate (explorationFeedback draws r (0 : Fin 2)) = 2 := by
  rw [localPopulationEstimate_eq, actual_collision_count]
  apply populationEstimate_correct (n := 2) (by decide) (by decide) (by decide)
    (by decide) (by decide)
  norm_num [collisionProbReal]

end BanditRLProof.MusicalChairs.PopulationCanary

namespace BanditRLProof.MusicalChairs.RankingCanary

noncomputable def scrambledScores (a : Fin 3) : ℝ := if a = 0 then 1/2 else if a = 1 then 3/4 else 1/4

noncomputable def tiedScores (a : Fin 3) : ℝ := if a = 2 then 1/4 else 3/4

theorem scrambled_sort : rankedArms scrambledScores = [1,0,2] := by
  have hu : ([1,0,2] : List (Fin 3)).toFinset = Finset.univ := by decide
  unfold rankedArms
  rw [← hu]
  apply (List.toFinset_sort (r := scoreOrder scrambledScores) (by decide)).2
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  norm_num [List.pairwise_cons, scoreOrder, scrambledScores, h20,h21,h20.symm,h21.symm]

theorem tie_sort : rankedArms tiedScores = [0,1,2] := by
  have hu : ([0,1,2] : List (Fin 3)).toFinset = Finset.univ := by decide
  unfold rankedArms
  rw [← hu]
  apply (List.toFinset_sort (r := scoreOrder tiedScores) (by decide)).2
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  norm_num [List.pairwise_cons, scoreOrder, tiedScores, h20,h21,h20.symm,h21.symm]

theorem scrambled_candidates : topArms scrambledScores 2 = {0,1} := by
  simp [topArms, scrambled_sort, Finset.pair_comm]

theorem zero_request_empty : topArms scrambledScores 0 = ∅ := by
  simp [topArms]

theorem large_request_all : topArms scrambledScores 7 = Finset.univ := by
  rw [topArms, scrambled_sort]
  decide

noncomputable def allCollisionFeedback : Fin 2 → ExplorationFeedback 3 :=
  fun _ => ⟨0,true,0⟩

theorem all_collision_candidates : localCandidateSet allCollisionFeedback = Finset.univ := by
  have hpop : localPopulationEstimate allCollisionFeedback = 3 := by
    norm_num [localPopulationEstimate, localCollisionCount, allCollisionFeedback,
      populationEstimate]
  have hc := localCandidateSet_card allCollisionFeedback
  rw [hpop] at hc
  exact Finset.eq_univ_of_card _ (by simpa using hc)

end BanditRLProof.MusicalChairs.RankingCanary

namespace BanditRLProof.MusicalChairs.RankingCanary

def oneObservedScore (j a : Fin 3) : ℝ := if a = j then 1 else 0

theorem actual_player_zero_scores :
    localEmpiricalMean (explorationFeedback PopulationCanary.draws (fun _ _ => 1) (0 : Fin 2)) =
      oneObservedScore 0 := by
  have hu : (Finset.univ : Finset (Fin 3)) = {0,1,2} := by decide
  funext a
  fin_cases a <;>
    norm_num [localEmpiricalMean, localObservationCount_eq, localRewardSum_eq,
      observationCount, FinitePMF.eventCount, observes, PopulationCanary.draws,
      CollisionFree, Fin.forall_fin_two, hu, oneObservedScore]

theorem actual_player_one_scores :
    localEmpiricalMean (explorationFeedback PopulationCanary.draws (fun _ _ => 1) (1 : Fin 2)) =
      oneObservedScore 1 := by
  have hu : (Finset.univ : Finset (Fin 3)) = {0,1,2} := by decide
  funext a
  fin_cases a <;>
    norm_num [localEmpiricalMean, localObservationCount_eq, localRewardSum_eq,
      observationCount, FinitePMF.eventCount, observes, PopulationCanary.draws,
      CollisionFree, Fin.forall_fin_two, hu, oneObservedScore]

theorem actual_same_candidates :
    localCandidateSet (explorationFeedback PopulationCanary.draws (fun _ _ => 1) (0 : Fin 2)) = {0,1} ∧
    localCandidateSet (explorationFeedback PopulationCanary.draws (fun _ _ => 1) (1 : Fin 2)) = {0,1} := by
  have hc1 : collisionCount (1 : Fin 2) PopulationCanary.draws = 1 := by
    norm_num [collisionCount, FinitePMF.eventCount, PopulationCanary.draws, CollisionFree,
      Fin.forall_fin_two, Finset.filter_eq']
  have hp1 : localPopulationEstimate
      (explorationFeedback PopulationCanary.draws (fun _ _ => 1) (1 : Fin 2)) = 2 := by
    rw [localPopulationEstimate_eq, hc1]
    apply populationEstimate_correct (n := 2) (by decide) (by decide) (by decide)
      (by decide) (by decide)
    norm_num [collisionProbReal]
  constructor
  · rw [localCandidateSet, PopulationCanary.actual_local_estimate, actual_player_zero_scores]
    apply topArms_eq_of_order_separated _ 2 _ (by decide) (by decide)
    intro a ha b hb
    fin_cases a <;> fin_cases b <;> simp_all [oneObservedScore,scoreOrder]
  · rw [localCandidateSet, hp1, actual_player_one_scores]
    apply topArms_eq_of_order_separated _ 2 _ (by decide) (by decide)
    intro a ha b hb
    fin_cases a <;> fin_cases b <;> simp_all [oneObservedScore,scoreOrder]

end BanditRLProof.MusicalChairs.RankingCanary

namespace BanditRLProof.MusicalChairs.HandoffCanary

theorem scrambled_boundary_gap :
    boundaryGap RankingCanary.scrambledScores 2 (by decide) (by decide) = 1/4 := by
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  norm_num [boundaryGap,rankedArm,RankingCanary.scrambled_sort,RankingCanary.scrambledScores,h20,h21]

theorem within_top_tie_gap :
    boundaryGap RankingCanary.tiedScores 2 (by decide) (by decide) = 1/2 := by
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  norm_num [boundaryGap,rankedArm,RankingCanary.tie_sort,RankingCanary.tiedScores,h02,h12]

theorem constant_boundary_gap :
    boundaryGap (fun _ : Fin 3 => (1/2 : ℝ)) 2 (by decide) (by decide) = 0 := by
  simp [boundaryGap]

theorem learned_actual_config :
    learnedConfig (n := 2) (T := 3) (by decide)
      (PopulationCanary.draws, fun _ _ => (1 : ℝ)) =
      commonConfig ({0,1} : Finset (Fin 3)) (by simp) := by
  apply Subtype.ext
  funext i
  fin_cases i
  · exact RankingCanary.actual_same_candidates.1
  · exact RankingCanary.actual_same_candidates.2

theorem actual_future_product (L : ℕ) :
    learnedDrawPathKernel (n := 2) (T := 3) (by decide) L
      (PopulationCanary.draws, fun _ _ => (1 : ℝ)) =
      (FinitePMF.iid (jointDraw (fun _ : Fin 2 => ({0,1} : Finset (Fin 3))) (fun _ => by simp)) L).toMeasure := by
  rw [learnedDrawPathKernel_apply, learned_actual_config]
  rfl

def separatedDraws : Fin 2 → Fin 2 → Fin 3 := fun t i =>
  if t = 0 then (if i = 0 then 0 else 1) else 0

theorem actual_first_action : continuationAction (by decide) separatedDraws 0 = separatedDraws 0 := by
  funext i
  simp [continuationAction,trajectory,initial,action]

theorem actual_fixed_next_action : continuationAction (by decide) separatedDraws 1 = separatedDraws 0 := by
  funext i
  fin_cases i <;>
    norm_num [continuationAction,trajectory,extendedCoordinationDraws,initial,action,step,
      CollisionFree,separatedDraws,Fin.forall_fin_two]

end BanditRLProof.MusicalChairs.HandoffCanary

namespace BanditRLProof.MusicalChairs.MarginalCanary

noncomputable def means (a : Fin 3) : ℝ := if a = 0 then 3/4 else if a = 1 then 1/2 else 1/4

def transientDraws (t : Fin 2) (i : Fin 2) : Fin 3 :=
  if t = 0 then 0 else ⟨i.val, by omega⟩

theorem zero_horizon_regret (d : Fin 0 → Fin 2 → Fin 3) :
    pathCoordinationRegret (by decide) ({0,1} : Finset (Fin 3)) means d = 0 := by
  simp [pathCoordinationRegret]

theorem actual_transient_regret :
    pathCoordinationRegret (by decide) ({0,1} : Finset (Fin 3)) means transientDraws = 5/4 := by
  norm_num [pathCoordinationRegret, roundPseudoRegret, roundMeanReward,
    trajectory, extendedCoordinationDraws, transientDraws, step, initial, action,
    CollisionFree, means, Fin.sum_univ_two, Fin.forall_fin_succ]

theorem fixed_draws_not_actions_regret :
    pathCoordinationRegret (by decide) ({0,1} : Finset (Fin 3)) means
      HandoffCanary.separatedDraws = 0 := by
  norm_num [pathCoordinationRegret, roundPseudoRegret, roundMeanReward,
    trajectory, extendedCoordinationDraws, HandoffCanary.separatedDraws, step,
    initial, action, CollisionFree, means, Fin.sum_univ_two, Fin.forall_fin_succ]

theorem two_player_actual_path_bound (L : ℕ) :
    (∑ d, (FinitePMF.iid (jointDraw (fun _ : Fin 2 => ({0,1} : Finset (Fin 3)))
      (fun _ => by simp)) L d).toReal *
      pathCoordinationRegret (by decide) ({0,1} : Finset (Fin 3)) means d) ≤ 32 := by
  have h := iid_path_regret_le (n := 2) (L := L) (by decide)
    ({0,1} : Finset (Fin 3)) (by decide) (by decide) means
    (by intro a; fin_cases a <;> norm_num [means])
  norm_num at h ⊢
  exact h

end BanditRLProof.MusicalChairs.MarginalCanary

namespace BanditRLProof.MusicalChairs.MarginalCanary
open MeasureTheory ProbabilityTheory

theorem allowed_draw_mass (d : Fin 2 → Fin 3) (hd : ∀ i, d i ∈ ({0,1} : Finset (Fin 3))) :
    jointDraw (fun _ : Fin 2 => ({0,1} : Finset (Fin 3))) (fun _ => by simp) d = (1/4 : ℝ≥0∞) := by
  have he : {x : Fin 2 → Fin 3 | ∀ i, x i ∈ ({d i} : Finset (Fin 3))} = {d} := by
    ext x
    simp only [Set.mem_setOf_eq, Finset.mem_singleton, Set.mem_singleton_iff]
    exact funext_iff.symm
  have h := jointDraw_rectangle_product
    (fun _ : Fin 2 => ({0,1} : Finset (Fin 3))) (fun i => {d i}) (fun _ => by simp)
  rw [he, PMF.toOuterMeasure_apply_singleton] at h
  norm_num [Finset.inter_singleton_of_mem, hd, Fin.prod_univ_two, ← ENNReal.inv_pow] at h ⊢
  exact h

theorem actual_transient_path_mass :
    learnedDrawPathKernel (n := 2) (T := 3) (by decide) 2
      (PopulationCanary.draws, fun _ _ => (1 : ℝ)) {transientDraws} = (1/16 : ℝ≥0∞) := by
  rw [HandoffCanary.actual_future_product, PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _),
    FinitePMF.iid_apply]
  have h (t : Fin 2) : jointDraw (fun _ : Fin 2 => ({0,1} : Finset (Fin 3)))
      (fun _ => by simp) (transientDraws t) = (1/4 : ℝ≥0∞) := by
    apply allowed_draw_mass
    intro i
    fin_cases t <;> fin_cases i <;> norm_num [transientDraws]
  simp_rw [h]
  norm_num [Fin.prod_univ_two, ← ENNReal.inv_pow]

end BanditRLProof.MusicalChairs.MarginalCanary

namespace BanditRLProof.MusicalChairs.ComparatorCanary

noncomputable def means : Fin 3 → ℝ := RankingCanary.scrambledScores

theorem arbitrary_bad_arm_deficit :
    globalRoundRegret means (fun i : Fin 2 => if i = 0 then 1 else 2) = 1/4 := by
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  norm_num [globalRoundRegret, means, RankingCanary.scrambled_candidates,
    RankingCanary.scrambledScores, CollisionFree, Fin.sum_univ_two, Fin.forall_fin_succ,
    h20,h21,h21.symm]

theorem all_collide_deficit :
    globalRoundRegret means (fun _ : Fin 2 => (2 : Fin 3)) = 5/4 := by
  norm_num [globalRoundRegret, means, RankingCanary.scrambled_candidates,
    RankingCanary.scrambledScores, CollisionFree, Fin.sum_univ_two, Fin.forall_fin_succ]

theorem zero_player_deficit (a : Fin 0 → Fin 3) : globalRoundRegret means a = 0 := by
  simp [globalRoundRegret,topArms]

def collisionExploration : Fin 3 → Fin 2 → Fin 3 := fun _ _ => 0

def futureChangedExploration : Fin 3 → Fin 2 → Fin 3 := fun t _ => if t = 2 then 2 else 0

theorem horizon_zero :
    learnerRegret (H := 0) (by decide) means collisionExploration (fun t => Fin.elim0 t) = 0 := by
  simp [learnerRegret]

theorem short_horizon_cost :
    learnerRegret (H := 2) (by decide) means collisionExploration (fun t => Fin.elim0 t) = 5/2 := by
  norm_num [learnerRegret, learnerAction, collisionExploration, globalRoundRegret, means,
    RankingCanary.scrambled_candidates, RankingCanary.scrambledScores, CollisionFree,
    Fin.sum_univ_two, Fin.forall_fin_succ, Finset.sum_range_succ]

theorem future_exploration_unused :
    learnerRegret (H := 2) (by decide) means futureChangedExploration (fun t => Fin.elim0 t) =
    learnerRegret (H := 2) (by decide) means collisionExploration (fun t => Fin.elim0 t) := by
  have h0 : futureChangedExploration 0 = collisionExploration 0 := by
    funext i
    norm_num [futureChangedExploration,collisionExploration,
      show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 2 by decide]
  have h1 : futureChangedExploration 1 = collisionExploration 1 := by
    funext i
    norm_num [futureChangedExploration,collisionExploration,
      show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 2 by decide]
  norm_num [learnerRegret,learnerAction,Finset.sum_range_succ,h0,h1]

theorem two_phase_transient_cost :
    learnerRegret (H := 5) (by decide) means collisionExploration MarginalCanary.transientDraws = 5 := by
  have hp : pathCoordinationRegret (by decide) (topArms means 2) means
      MarginalCanary.transientDraws = 5/4 := by
    simp only [pathCoordinationRegret,Fin.sum_univ_two]
    norm_num [roundPseudoRegret,roundMeanReward,means,RankingCanary.scrambled_candidates,
      RankingCanary.scrambledScores,trajectory,extendedCoordinationDraws,
      MarginalCanary.transientDraws,step,initial,action,CollisionFree,
      Fin.sum_univ_two,Fin.forall_fin_succ]
  rw [learnerRegret_split,hp]
  norm_num [explorationPrefixRegret,globalRoundRegret,means,
    RankingCanary.scrambled_candidates,RankingCanary.scrambledScores,
    extendedCoordinationDraws,collisionExploration,CollisionFree,
    Fin.sum_univ_two,Fin.forall_fin_succ,Finset.sum_range_succ]

end BanditRLProof.MusicalChairs.ComparatorCanary

namespace BanditRLProof.MusicalChairs.RealizedCanary

noncomputable def oneFeedback : Fin 1 → Fin 1 → ExplorationFeedback 1 :=
  fun _ _ => ⟨0,false,1⟩

theorem realized_deficit_negative : visibleRegret (fun _ : Fin 1 => (1/4 : ℝ)) oneFeedback = -3/4 := by
  norm_num [visibleRegret, oneFeedback, Fin.sum_univ_one, Finset.sum_const, topArms_card]

theorem collision_zero_sensed :
    (explorationFeedback (fun _ : Fin 1 => fun _ : Fin 2 => (0 : Fin 3))
      (fun _ _ => (1 : ℝ)) 0 0).collided = true ∧
    (explorationFeedback (fun _ : Fin 1 => fun _ : Fin 2 => (0 : Fin 3))
      (fun _ _ => (1 : ℝ)) 0 0).reward = 0 := by
  norm_num [explorationFeedback, CollisionFree, Fin.forall_fin_succ]

theorem genuine_zero_not_collision :
    (explorationFeedback (fun _ : Fin 1 => fun i : Fin 2 => (i.castLE (by decide) : Fin 3))
      (fun _ _ => (0 : ℝ)) 0 0).collided = false ∧
    (explorationFeedback (fun _ : Fin 1 => fun i : Fin 2 => (i.castLE (by decide) : Fin 3))
      (fun _ _ => (0 : ℝ)) 0 0).reward = 0 := by
  norm_num [explorationFeedback, CollisionFree, Fin.forall_fin_succ]

end BanditRLProof.MusicalChairs.RealizedCanary

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
