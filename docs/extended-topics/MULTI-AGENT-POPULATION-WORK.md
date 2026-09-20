# Actual local population estimator work

Source: Rosenski--Shamir--Szlak ICML2016 static Algorithm1 and supplement A.1
Lemma3. Frozen contract and reviewed route retain gamma=2/5 and collision
accuracy1/(10k); no informal Taylor argument or supplied correct-N premise.
Target: actual local collision count -> total inverse-log/round/min estimate ->
Nhat=n on the already constructed statistics event -> same-law probability.
Owner: runs/extended-topics-20260920/MusicalChairsPopulationPrototype.lean.

Reuse/search: existing quarter_le_avoidance and exact collision law; prior
joint statistics probability and explorationLength. Upstream global
rpow_one_add_le_one_add_mul_self, Real.rpow_neg/log_rpow/log_pow/log_le_log,
round_eq_iff (global namespace); natural subtraction casts and finite filter-card count bound.
Prior private API trial compiled the two real-power margins. State k>1,
1<=n<=k and positive duration wherever inverse logs/count fractions require it.
The source1<=n<k entails these; k=1 is not a valid inverse-log domain.

Implementation: round half-integers towards positive infinity as Mathlib Int.round;
Int.toNat truncates negative values to0, then min k caps. All-collisions count=T
uses k. On valid non-all-collision counts prove real inverse>=1, ensuring
agreement of the natural output with the source. Actual correctness retains
zero collisions, n=1, ties safely away from half-integers, and exact denominator.

Semantic plan: source-blind reconstruction, independent source comparison,
standard-axiom audit and exact folded reader. Scratch-only until shared extraction
and full public gates. Population correctness is a theorem edge towards the
source good event, not ranking, complete learner/regret or topic completion.

## Compiled actual population endpoint

Both real-power margins, q>=1/4, positive survival sandwich, reversed-log
inequalities and the closed n+-2/5 interval now compile. round_eq_iff then
identifies the actual rounded integer. The natural-count complement uses its
required C<=T,T>0 domains. Actual local collision counts satisfy C<=T, and the
same local-only estimator agrees with the integer rounded/capped source formula
in every valid regular branch. On collision accuracy, C=T is impossible and
populationEstimate_correct proves the total estimator equals n.

populationRecovered_probability consumes actual collision-law concentration.
The measurable explorationEstimatesCorrect joint event explicitly combines
actual local Nhat=n with mean accuracy. Its probability>=1-delta at the exact
ceiling/max explorationLength follows by inclusion of the earlier constructed
statistics event. No correct-N premise was introduced; sorting remains open.

Focused compilation exited0. Separate axiom build exited0 for all38 new
named declarations (32 theorems, six definitions, no new probability instance),
with only propext, Classical.choice and Quot.sound. Seven canaries include both
closed collision-error boundaries, zero/full counts, and the actual local
readout on a three-round, two-player transcript for every reward array.
Independent blind/source evidence is recorded separately in the population
receipt. No new public root/Tests/harness/site gates are claimed.

Compiler repairs: global round_eq_iff (not Int namespace), explicit sign lemmas
for log/division, preserving Nat subtraction casts, and Finset.filter_eq' for
the concrete count. The analytic route and all constants stayed unchanged.

Next ranking route: actual Finset.univ.sort with score-descending/index-ascending
tie order, take Nhat, toFinset; upstream pairwise_sort/sort_nodup/length_sort,
List.pairwise_append and take_append_drop connect strict cross-gap separation
to the selected first-n set. Private ranking-api.lean contains exploratory
#check output; its unknown-name checks are not validation evidence.

Independent source review accepted with explicit delta, matching the completed
blind reconstruction;32 new proofs/seven canaries and the exact fold inspected.
The receipt binds hashes and preserves scratch-only status. The next-step
private ranking-prototype.lean now compiles score-descending/index-ascending
total-order instances, actual sorted/take list definitions and exact selected
cardinality=min(n,k). This private trial is not included in this checkpoint's
semantic acceptance or declaration totals and does not prove common candidates.
