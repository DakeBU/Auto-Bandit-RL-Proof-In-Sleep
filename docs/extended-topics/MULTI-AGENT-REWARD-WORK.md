# Arbitrary bounded reward-array and selected-mean proof work

Source: Rosenski--Shamir--Szlak ICML2016 static Algorithm1, supplement A.1
Lemma2, and the explicitly reviewed random-count proof route. Target: construct
nested product reward laws for arbitrary arm probability measures supported in
[0,1], identify actual coordinate marginals/means, derive temporal independence
and sharp fixed-schedule mean concentration for the actual local reward/count
readout. Then couple the finite exploration schedule and reward law and mix by
the already constructed count Laplace transform. No finite-support restriction
on rewards; no independent-selected-reward or concentration premise supplied.

Reuse: previous exact exploration action/count/readout prototype; Mathlib
Measure.pi, measurePreserving_eval, iIndepFun_pi, integral_map,
hasSubgaussianMGF_of_mem_Icc and sum_of_iIndepFun/measure_ge_le. Mean is the
integral under each supplied arm measure. Finite observed-time filters are
functions of a fixed action transcript, not reward-dependent stopping rules.
Each selected centered reward has proxy1/4; countD and thresholdD*eps/2 give
2exp(-D*eps^2/2). D=0 retained with a separate trivial bound. Product-law
construction, measurability, integrability and finite mixture identities must
be proved. Source changes/target weakening are not authorized by compiler
errors. Scratch owner MusicalChairsRewardPrototype.lean; preceding action
prototype is copied as immutable context until canonical shared extraction.

## Accepted scratch checkpoint

Actual reward-coordinate marginals/means, temporal independence, sub-Gaussian
selected sums, zero-count branch, measurable actual local means, finite joint
mixture, exact count transform, exponential scalar bound and finite player/arm
union now compile. Terminal allMeanAccurate_probability preserves the first
source exploration budget16k/eps^2 log(4k^2/delta) and yields simultaneous
STRICT eps/2 accuracy with failure at mostdelta/2.

Focused Lean compilation exited0. The separate axiom audit exited0 and covered
46 new named declarations:43 scanned definitions/theorems (33 theorems) plus
three explicit probability instances. Only propext, Classical.choice and
Quot.sound occur. Previous exploration context is unchanged and the reader's
folded code exactly matches the scratch file. Independent blind reconstruction
and source review accepted the explicit component boundary. Receipt:
runs/extended-topics-20260920/multi-agent-reward-review.json.

Compiler repairs only supplied explicit pi index/function types, NNReal proxy
notation, measure-preserving map/integral rewrites and scalar normalization;
no source hypotheses or constants were weakened. The continuous uniform-law
canary verifies a genuinely non-discrete interface; its T=2 numerical bound
exceeds1 and is not evidence of useful finite-sample accuracy by itself.

Next: actual collision-count concentration with all-player delta/2 allocation,
then inverse-log rounding/population recovery, ranking, ceiling/max budget
instantiation and full good event. Fresh continuation/complete learner/regret,
shared extraction/public gates, recent-source audit and ICLR evidence remain.
No new combined root/Tests/harness/site gate is claimed for this scratch.
