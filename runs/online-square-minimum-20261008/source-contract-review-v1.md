# Square-minimum source/type contract review

Verdict: **accepted-with-explicit-delta**, for stabilization only. No blocking mathematical or metadata repair found.

Actor: /root/source_reviewer. Reused automated source reviewer with prior staged history; distinct from formalizer and neutral decoder. GPT-6 Astra / medium are requested settings, not runtime-attested. This is neither blind nor human/external review.

I independently rehashed all 132 fixed raw inputs before and after review, read the source and complete relevant Mean/FTL/Regret/Foundations bodies, and viewed all four bound source images at original detail (PDF14–17 / printed2–5). The PDF SHA is cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17. Historical references are bounded dependencies, not recursive reacceptance of their whole packages.

The source pathwise square minimum, actual empirical-mean minimizer, printed Theorem1.3 and the quarter-plus-harmonic intermediate bound are distinct anchors. The six new propositions are derived producers/representations/adapters, not six printed theorems. Source printed1–2 minimum of expected fixed loss and the causal IID variance benchmark remain REQUIRED next.

## Target seven-slot comparisons

### M001 BanditRL.OnlineLearning.guessing_prefix_minimum

Verdict: accepted-with-explicit-delta (source/type only).

- **objects**: Real interval squared-loss prefix and actual empiricalMean.
- **hypotheses**: Only y_t in [0,1] for t<T; no supplied argmin.
- **quantifiers**: Every real stream and natural T; every feasible fixed u.
- **normalization_and_indexing**: Same finite range T; zero-based source translation.
- **information_structure**: Hindsight comparator producer, not a learner.
- **conclusion**: Actual mean feasibility AND cumulative-loss minimality.
- **source_delta_and_dependency**: Positive T follows existing decomposition/feasibility; T0 is empty extension, not uniqueness.

### M002 BanditRL.OnlineLearning.squaredLoss_minimum_eq

Verdict: accepted-with-explicit-delta (source/type only).

- **objects**: Real sInf of the image of interval comparator losses.
- **hypotheses**: Same finite-prefix interval hypothesis; no assumed minimum.
- **quantifiers**: Every y,T under hy; image ranges over all feasible real u.
- **normalization_and_indexing**: Unnormalized cumulative square loss.
- **information_structure**: Pure pathwise benchmark, no probability or expectation.
- **conclusion**: sInf equals loss at the actual empirical mean.
- **source_delta_and_dependency**: Image contains mean loss and is bounded below by it via M001; IsLeast.csInf_eq is applicable. The image is not asserted finite.

### M003 BanditRL.OnlineLearning.squaredBestRegret_eq_comparatorRegret

Verdict: accepted-with-explicit-delta (source/type only).

- **objects**: squaredBestRegret and shared comparatorRegret at actual mean.
- **hypotheses**: hy only; prediction is arbitrary real-valued.
- **quantifiers**: All y,prediction,T satisfying the prefix condition.
- **normalization_and_indexing**: Same cumulative sums and horizon on both sides.
- **information_structure**: No prediction feasibility or causality follows.
- **conclusion**: Exact signed regret identity.
- **source_delta_and_dependency**: Definition unfolding plus M002; no expectation/minimum interchange or assumed regret bound.

### M004 BanditRL.OnlineLearning.comparatorRegret_le_squaredBestRegret

Verdict: accepted-with-explicit-delta (source/type only).

- **objects**: Regret against a feasible fixed comparator versus minimum benchmark.
- **hypotheses**: hy and u in [0,1]; prediction arbitrary.
- **quantifiers**: Every such y,prediction,T,u.
- **normalization_and_indexing**: Same cumulative prefix, no averaging.
- **information_structure**: Representation order only, not algorithmic performance.
- **conclusion**: Comparator regret is at most best-fixed regret.
- **source_delta_and_dependency**: Subtracting the smaller minimum reverses the loss comparison correctly; negative regret remains possible.

### M005 BanditRL.OnlineLearning.meanPredict_bestRegret_bound

Verdict: accepted-with-explicit-delta (source/type only).

- **objects**: Actual first-half strict-past meanPredict and produced minimum.
- **hypotheses**: T>0 and all prefix targets in [0,1].
- **quantifiers**: Every qualifying stream/prefix; no IID assumption.
- **normalization_and_indexing**: 4+4 log T with T coerced to real; source rounds 1..T.
- **information_structure**: Existing meanPredict_prefix and definition fix current output from strict past.
- **conclusion**: Upper bound on signed pathwise best-fixed regret.
- **source_delta_and_dependency**: M003 transports existing theorem_1_3 for this same predictor; no new arbitrary-initial or optimality claim.

### M006 BanditRL.OnlineLearning.meanPredict_bestRegret_refined

Verdict: accepted-with-explicit-delta (source/type only).

- **objects**: Same actual predictor and attained minimum.
- **hypotheses**: T>0 and same prefix interval condition.
- **quantifiers**: Every qualifying stream and positive horizon.
- **normalization_and_indexing**: 1/4 + sum over range(T-1) of 4/(real t+2), source rounds 2..T.
- **information_structure**: Initial 1/2 is essential to sharp first-round term; no future data.
- **conclusion**: Exact refined upper bound, not optimized or asymptotic equality.
- **source_delta_and_dependency**: M003 transports existing meanPredict_regret_refined; T1 has empty tail, T0 excluded.

## Complete owned definition

- **objects**: Real-valued finite cumulative loss minus real sInf over interval loss image.
- **hypotheses**: Standalone definition has no hypotheses.
- **quantifiers**: All real target/prediction streams and natural horizons.
- **normalization_and_indexing**: Finite unnormalized prefix; no division by horizon.
- **information_structure**: Arbitrary supplied prediction trace, not a causal strategy definition.
- **conclusion**: Complete difference-of-sums/infimum expression preserves signed values.
- **source_delta_and_dependency**: Actual interval image is nonempty and square losses nonnegative; target M001/M002 must produce attained minimum under hy. No probability/minimum exchange.

## Evidence and attempted contradiction checks

The actual reused empiricalMean_decomposition produces the global minimizing inequality from a nonnegative n*(u-mean)^2; empiricalMean_mem separately proves interval membership. No desired minimizer is supplied as a hypothesis in M001. At T0 the interval is still nonempty, all losses are zero, and the default mean is zero; there is no unique-minimizer claim. At positive T the existing unique result is separately reusable.

The actual FTL proof consumes the produced empirical-mean minimizers through Lemma1.2; the refined proof explicitly splits the initial term and subsequent indices. Arbitrary predictions in M003/M004 are an explicit representation generalization. Their signed regret can be negative: this cannot imply nonnegative expected excess loss, ordinary convergence, minimax optimality, or causal behavior of arbitrary supplied traces. The prospective alternating-stream and nonbinary canaries are meaningful plans, not compiled tests.

The successful logs establish six public/neutral closed Prop types and six Prop/four whole-definition equalities, plus pinned API availability. They do not prove these six prospective theorem bodies. IsLeast.csInf_eq uses actual leastness; csInf_le and le_csInf retain their boundedness/nonemptiness requirements. The initial DAG pending flag is historical draft readiness, with actual later compilation evidence kept separate.

Preparation failures (missing blueprint file after native task creation and nested decoder report-object handling) are preserved and repaired administratively without statement/source changes. Decoder reconstructed six propositions and four neutral definitions; its source/proof verdict remains not_assessed.

## Original future reader obligations

- **R1 — future-required:** Keep source printed2 square minimum, printed3 actual empirical-mean minimizer, printed4 theorem1.3 and printed5 refined bound distinct; six derived producers/representation/adapters are not six printed theorems.
- **R2 — future-required:** The real sInf benchmark must be proved nonempty and attained by the actual feasible empirical mean; no assumed minimizer or totalized-inf shortcut. Positive-horizon uniqueness is separate; T0 is only the explicitly disclosed empty-prefix extension.
- **R3 — future-required:** Retain interval targets for the same finite prefix, source rounds1..T versus Lean0..T-1, and refined source2..T versus range(T-1) with real denominator t+2; performance endpoints require T>0.
- **R4 — future-required:** Generic identities/order consume an arbitrary supplied real prediction trace and do not assert its feasibility or causality. Performance endpoints use the actual meanPredict first1/2 and later strict-past empirical mean, not an arbitrary future-aware algorithm or arbitrary initialization.
- **R5 — future-required:** Keep signed pathwise best-fixed and comparator regret; their values may be negative. No nonnegative regret, absolute-value/rate/ordinary-limit claim follows from the minimum representation.
- **R6 — future-required:** Do not interchange expectation and a hindsight minimum. Printed1-2 minimum of expected fixed loss and causal cumulative IID variance benchmark remain required next, distinct from this produced pathwise minimum.
- **R7 — future-required:** Reuse the actual shared empiricalMean/comparatorRegret/meanPredict and existing theorem1.3/refined proofs in the same library and registry. Draft closed-Prop/whole-definition equality compilation is separate from actual theorem-body proof; disclose every actual source delta.
- **R8 — future-required:** Keep source/compiled-body/canary/kernel/combined/root/Tests/harness/reader/site/native/PR gates separately evidenced. Only bounded square-minimum hinge may close;16C1sourceitems/proof-totalnull, five main-relative modules, full C1, incompleteC2,3-16/necessaryappendices and active totalGoal remain required. OPENunmergedPR192stack is not main/live completion.

No R requirement is discharged by this contract review. New proof bodies, canaries, kernel/dependency checks, combined root/Tests/harness, reader/site/pixels, native acceptance and PR remain separate. Sixteen Chapter1 source items are not a proof count; proof-total remains null. Five other main-relative audits, full Chapter1, incomplete Chapter2, unenumerated Chapters3–16 and necessary appendices remain required; Goal remains active. OPEN unmerged PR192 is a stack reference, not main/live completion.

## Independently measured raw bindings

| Path | SHA-256 |
|---|---|
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/00_context.md | c8e656ad99f432997cbd659959bf0c2f48f869eef1708fe70c6df59475cb7ad0 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/10_director.md | a96038c1f903eeb0418b6d2a75fecc8234593049bf35c4bb346178ee0c28bdb0 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/20_architect.md | e6c214adbc83a0eb645d26f753af79a24647f6f542f1d1d17b1db823b4994150 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/actual-blueprint-refresh-v2-exit.json | 8ccff2141eed7c7b481e93ac29f0735bec6ce03a89ae51ec8aa958cdedb06306 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/actual-blueprint-refresh-v2.log | 7f09c01374a8726202b0dd545e41123cd1fd829094ff9b56c0894d50872cdabd |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/actual-draft-neutral-identities-v1-exit.json | 72ae69cf68172a253441d82bcdbbbd90bb4de3d46dd3b130102f25c04fe397be |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/actual-draft-neutral-identities-v1.log | 2e40a403dbdd3a1c831c19cf50cc81c541977f342508fcd4121e84fe6288a0bc |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/actual-draft-types-and-API-v1-exit.json | 2efa49f1816734552c360e657072799cb9448b6c0796853498082ba361ecf321 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/actual-draft-types-and-API-v1.log | 68eae7abf23b24ddc3e1859879174491326be3c36e975d13a98b7904ac291644 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/actual-neutral-types-v1-exit.json | 0d8a8d6d9498b6bc0a05c6eb46acbd80b342206be43b02da159b876ff3e92afa |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/actual-neutral-types-v1.log | 904dfaf050ebdecc8f4059f6a183fcadd28804d81eed369f099dd33cb7072629 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/actual-reference-index-v1-exit.json | 74ac75045e4625f04a4effee02dcfec0948f14c8632e77ac696fec9303a12e62 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/actual-reference-index-v1.log | d92bf5e27da356cfe1c9e173388aae6b24ccf1a93a9d9638753ada539b796d41 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/blind-receipt-v1.json | 2f7b4baf062f5a94be357ea02a36ee6214d50e7eaa4fcda400a1ae4942a5d076 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/blind-reconstruction-v1.md | 71539dc2bc8a5717750b38de440387ef61fd6d2450bc20f687b2af3ab99f1d88 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/bootstrap-draft-v1.py | 00635216db447f876411f5f956169a2a6234cd16722308a4f867b72557c34c2d |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/canary-plan-v1.json | aa56fae37b8607426e57d877a82d884a102acc5be7f515019b1bc43d907a6031 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/common_v1.py | 4f57cab1ca46603becfa68a59fcc5e2b20353f5bb6b0b42db69de88460cea8c9 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/contract-preparation-repair-v2.json | 2b5e5afa439e5ad663c70cc7e7460744ad7ce902a2a7b64914f9f35e65dce906 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/declarations-csInf-v1-exit.json | 1f2b9054807b32b230ff9eb82c7ef4a073eb3a8959bf5c3e610d2711ef7fb5db |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/declarations-csInf-v1.log | e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/declarations-empiricalMean_minimizes-v1-exit.json | a653ef6fd1afe5c2afbd2c6c74fe9fdcb7e25addb56e6a42f80fa55ab5f9a3af |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/declarations-empiricalMean_minimizes-v1.log | d825bf3395c6e987a7311bc81778c4dfef3fba2e954920adc80905b34ed23286 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/declarations-squaredBestRegret-v1-exit.json | a1a5fad4da791145edd8323a1efd06f5d48a96405d5ae4cfb9ed66229ee57c50 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/declarations-squaredBestRegret-v1.log | e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/draft-baseline-v1.json | 1785baf438a9b6a537acaf132031d1cb2aad790ce4c52b143846a347c1a9173a |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/draft-lifecycle-v1-exit.json | d1ddc91a14ddbd21aea09ea86085ba35e9b68d4f7b910510d4b15d92d4659119 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/draft-lifecycle-v1.log | efa21bb6bfc92dea5d2d86e6379416afe73abb30995e5b0bb941c31a74e946a6 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/draft-neutral-identities-v1.lean | 33ce2ad0620073ee42cf610d6aa61fe26d3233833d6408142ef97f25b52a9e6a |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/draft-type-verification-v1.json | 6489ded463849eb98e95c269b1c531e154c47925605312efde9e24198b7dcef2 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/draft-types-v1.lean | ebc9bc47e6484d1ca79d20686230d6b59fe5a274e4eb204e111fedc7a9c501fe |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/mathlib-cards-v1-exit.json | 90b922c872951fd3ed458724fd40dcd61a0c3aa06f0651c1936c17169d4f0f6a |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/mathlib-cards-v1.log | 884fab88619a3d1adcafe89eecddd2d98f4be5c6fa61262862134dde9e51d225 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/memory-csInf-v1-exit.json | 587158d128241a7a672205d5ea365e97df3f4056f72d6ce2f3da363cf819050e |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/memory-csInf-v1.log | 11999fd2b01349cb48f47e2291dcbda3daeae233e4d63611c1bad6c59a86faae |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/memory-empiricalMean_minimizes-v1-exit.json | 9ead39e3977a790f12e40221d1305383a74750a159d75510bdedd51696222dbb |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/memory-empiricalMean_minimizes-v1.log | 79a53551b8747b56f7e8880612eed550afd6de9cf66d27386c99098e54018875 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/memory-squaredBestRegret-v1-exit.json | fb6b005d078d457595090d7db64efbd24fdb794bc99e9e554e3b3d9f15318d3e |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/memory-squaredBestRegret-v1.log | 11999fd2b01349cb48f47e2291dcbda3daeae233e4d63611c1bad6c59a86faae |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/memory_digest.md | 6cb2f6d7a20f6dd2ed45318bce0c10db033b60412d601f54ff973441b23ca698 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/native-reference-index/bandit_paper_cards.json | 91c1dc2ce7f91fc6a148f02a0cebb367a64f6353204a0781d75c762337d83995 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/native-reference-index/bandit_scenario_cards.json | fa4ea6e7d7cdd5d92f9cef56c260a6657d548f6d0e7a546a3afdea2348bb0db1 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/native-reference-index/bandit_textbook_cards.json | 7b4f40eb580a29d0d559fe50dd1a2872cf7a61675e047fb3facaeb4c2b9abf09 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/native-reference-index/lml_bandit_cards.json | fa149c38753544dc8a45fc3f12e4b3116de2661798285d0eea6f5960c7bd1959 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/native-reference-index/local_leaf_cards.json | 8ac1e50469b7dceb3007d9b7665e8dd7a8a510ed00a72d8c5c36918b237efb4b |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/native-reference-index/local_lean_declarations.json | 0e300c061cbf1ab1d4d464dfd0f303a17b8054bbc85ffd21361b54973a3e7dab |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/native-reference-index/mathlib_bandit_cards.json | 824faf3db7ceeea04f8dfc39a72f308d5bef6bafe67751f6c1ac66da13fa39ae |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/native-reference-index/proof_weapon_cards.json | 7bba956158c7cffa65de22cda2b51d8c1d3b5d4fc515858c7854b5dccddabe90 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/native-reference-index-v1.py | 621cf42667fbddd44e2296f69932e172255afb17a221fee4048d31ae322ab388 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/neutral-inputs-v1.json | 8779336eaa3af15143b1afbf2699a1947ac619c6bd16ee777370c2b45bddbdea |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/neutral-packet-v1.md | cf2abf3cdcd5a2fd2d708316343a67a8fbfa2d3aaa64b9be9894fdd23b5ad372 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/new-task-v1-exit.json | 1933929d3acff540fe1e298e4bfae3ce411f1c95dc3a8cee4bb46c3e8351f582 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/new-task-v1.log | 59d34971d6b6e1d60bc41cdff5f974c082fad69a51d32433166298e5e171d6f2 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/paper-cards-v1-exit.json | 92b62197bf55b3cd506b18a772391472df90dae0e8a4bba2dc73cd2b1b1543ce |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/paper-cards-v1.log | 9acd333996a893a7b5ccad3e674ece26ef05c8b737e7816b33043b121583a619 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/prepare-contract-v1.py | 42335d0aff998171db2e7745c11cc60fa164ced18494d88979c1e0650df72e14 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/prepare-source-review-v1.py | b52b9270dfc6caaa8f367664389665d86cabf01d1985b5852570d31a314435ab |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/prepare-source-review-v2.py | 045cc20d68741f34a7901396cf62518e52b22701d5c8aed3a135f6fdabf206e2 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/prepare-type-identity-v1.py | 1b088ca2f422e3a400eb454e87414f47c9f14006f5ae3f0785b80528be9dd012 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/proof-obligations-draft-v1.json | 8906a1c538845ddd018f8d5718b55dfc92414d1ab554d924d2e2559ee2223a63 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/record-source-audit-v1.py | c7c35b9784f9642f0c4d9c8462e3faddb11945aed5910c57b2b27696dac0575a |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/resume-contract-preparation-v2.py | 298a09a3cd7989f71c9f817fef00317a14577175d1baf7797797a8ae8383b80e |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/retrieval-actual-APIs-v1.json | da2b6f8c9d3e901b3909fa9860b5fab2d44179e61486b206fa4e899c27d2978d |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/retrieval_index.md | 45669f19a7d40647b02fc6c2b6cca5fcffd94794a8d077897cd654ec167a6c79 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/snapshots/BanditRLProof--OnlineLearningAsymptotic.lean.raw | 60580602f27c35cb4782d78bd590e73e780023f62e5ae71a06c5a44d09d7ab72 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/snapshots/BanditRLProof--OnlineLearningFoundations.lean.raw | e23ebdca2f7ce21a16173c93390fd24d16ba36e403c9d084233f7480e75408b8 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/snapshots/BanditRLProof--OnlineLearningFTL.lean.raw | 8c3574c657f08e0c5291f0689105f9459e92187502f092f4d36d848e52ab4219 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/snapshots/BanditRLProof--OnlineLearningHistory.lean.raw | 3412177ab7dd0ac0e350d8fde7f91e61640d55743d1f17d15c62a65dd4492fc7 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/snapshots/BanditRLProof--OnlineLearningIID.lean.raw | 92af24e6a2c2b1054503492b2bad97cd17ccea2217439f6d2f8a7bedb0de3d5e |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/snapshots/BanditRLProof--OnlineLearningInformation.lean.raw | 72bef017a43c293d0d3c449707e4a0e058f4655c2483b54c3120d7b41c98135a |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/snapshots/BanditRLProof--OnlineLearningMean.lean.raw | 811dcf3741e3d6dee19b2c4a9f43f4b266808b89843a1719e00f239a4687258b |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/snapshots/BanditRLProof--OnlineLearningRegret.lean.raw | 0bac6b6e454c5d7bd2244fc115bc8df8cbd9b5505302aa81d03baaeeeec204dc |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/snapshots/BanditRLProof--OnlineLearningStochastic.lean.raw | 0242481022883958afef677654fadd3f6e37b381f3fe463e3605f3eb0542f2bd |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/snapshots/BanditRLProof--OnlineNoRegretSemantics.lean.raw | db7482a02bf4643ba3d4b15b29dd5a59418ea111763afeed45c51879b996e5a7 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/snapshots/BanditRLProof.lean.raw | 16c1fa305a980353d040eda958d087bbafa48c7a2957662e2c9e0228acd36d95 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/snapshots/docs--contracts--online-book-v1--source-inventory.json.raw | a2a504cf40d73f9c5e36f00fc1ef3b949ccaf5a558ab603c1c2a86007f30efa7 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/snapshots/lake-manifest.json.raw | 87c3e616f86244550ef39e7415186b11c1d4cf4bef20173196a619d9d4d48f48 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/snapshots/lakefile.lean.raw | 0164f3b5b5bdcbb237ab15ae8b44da83e183f4b97d5f3832aa4a57f27dc69d45 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/snapshots/lean-toolchain.raw | b15a57f8ea4c890197465ce1156667ae13d9ed4ab8a9f263a920bf010d967d82 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/snapshots/MANIFEST.md.raw | ea06fc5749dacec55781ad64f8f67650b6ddb2d9e73e01e7ab9ac1283f480866 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/snapshots/research-wiki--papers--sgb-theorem2-interface-frontier-trace.json.raw | 6cc5d9f545aded644d0ee7e3006e714f5e226869a78ae3c1904de542b5e8ca39 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/snapshots/runs--lifecycle_memory.jsonl.raw | 94be3ceb994768191ceb6a7545935c8d16c044511dfe8c4482e2fde493eaa5f8 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/snapshots/runs--lifecycle_sessions.jsonl.raw | 78280f01886a7b95528cc6d4a342cf0b050d49e007ec988531896438fb0474f5 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/snapshots/runs--trials.jsonl.raw | ec2ad2999d1895a8a604b231bba6117535d5cd14fc29a2b20469f2cddd46510a |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/snapshots/Tests.lean.raw | 43bed7e65a4c43a88f5ae352c556f2bdb94fef7f1cc7a5e38d21384c967e784c |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/snapshots/website--content--chapters.json.raw | f0a19e8c26111abc8059b5ab4fdf8555c6128faf81f465c5ba1d7bb683f1ce50 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/snapshots/website--content--highlights.json.raw | e8f77a2d46866622d3fa5c309ae6b47e46e736eed91dc82ce4373a47fe92c5a2 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/snapshots/website--content--readings.json.raw | 0f3bccc8634d20a09a13e4ceaca988c77d2206d72e6bc0cfb1fc9e0363bc80d8 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/source-contract-packet-v1.md | ea13413e786f8dcda3f46f23fa0d5f24aca25ea44d7f31fd5ad31f33f9ef15b4 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/source-pdf14-v1.png | 7ab02401ce04b4dd7b4fe65fede63ea9a7aed1e3ef8db085660bca99ae580f79 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/source-pdf14-v1.txt | 3f9d01aee6e81504b7ca2ef0d9657bc1ee30f36eb54a957b8018c4d0c3e2ac66 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/source-pdf15-v1.png | 42bb911c94638c3e96bed6b043eb9f2de8d9dc6c226dd36e5c43d42896d02259 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/source-pdf15-v1.txt | 037b6d907a868c339b881162333f6e56352cbebf285902eb6ed628ff4f8bd947 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/source-pdf16-v1.png | 1cdaa7b80dc113b8083930eb1dcf245688aa921bfe112021d070610f8cab3eb8 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/source-pdf16-v1.txt | b8fe01f6c31bf15cfb67ea948a832f97e2c77f9e1f569a36fd9fa72e831796ee |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/source-pdf17-v1.png | 8515e968b52d0d84928817aa489e890b5fa9a02207aa95dd3da28c9252eacff2 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/source-pdf17-v1.txt | 164b4ca2261475aeadaf633ce67afbf8a221f612b8f4db801c36ea75081263e8 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/source-pixel-review-v1.json | 5eee2df0fc2d3327c9c19ea368cf675b1e43fbc85b1586fce3a57cb2322fd067 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/source-preparation-repair-v2.json | 7ad3fd4614d54dd0c1d374326fa6e0c5d16dc3f569edb59a23283ff065936957 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/stacked-base-PR192-v1.json | c72bc5c9023f1ab9a3bb2914600fdd3ac13feba52cbca199cffac29f989fb97e |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/weapon-cards-v1-exit.json | 7fca58e30e0c7949e4f9173671ea615d757ff62e37998ae253653fe022b0fcdf |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/weapon-cards-v1.log | a6e4b78de1a30fcf5a0ee66b868eb3ac1bfa68d2250c713f61e690ae064f7ef6 |
| E:/ABRL/worktrees/research-online-book/docs/contracts/online-square-minimum-v1/chapter-one-source-ledger-draft-v1.json | e31045dcde829375ea0601914aa00db30c9f46e80bbcfbe0a3228976564b6f6d |
| E:/ABRL/worktrees/research-online-book/docs/contracts/online-square-minimum-v1/contract-v1.md | e5fd2a55bbdb88b11558bfa1d386650677f551b9337dfc814bc9129ce740a1b9 |
| E:/ABRL/worktrees/research-online-book/docs/contracts/online-square-minimum-v1/initial-DAG-v1.json | 11bca5ef5e43721f1af2ecc6d9cdcdfa9d7cfce2b899307e6a61ed1b819ff063 |
| E:/ABRL/worktrees/research-online-book/docs/contracts/online-square-minimum-v1/neutral-context-v1.lean | f51eff332bb91d454e6974e2b7ed1f20122a7a6102db6be760a4c01d561fb97c |
| E:/ABRL/worktrees/research-online-book/docs/contracts/online-square-minimum-v1/public-context-v1.lean | fdc68d202b7789a35f48e01f861dacfcda98fcf27e2076e38ca5e72b18d6dd69 |
| E:/ABRL/worktrees/research-online-book/docs/contracts/online-square-minimum-v1/reader-requirements-v1.json | a314a6f080fe2ea29b15ed8beea4b73029d193fbf73e6cef2a15a7398aef61d2 |
| E:/ABRL/worktrees/research-online-book/docs/contracts/online-square-minimum-v1/source-card-v1.json | ddde6020861e00a1812d9b07dec0a5b5427d096576b21436d89ab97bdc9a075f |
| E:/ABRL/worktrees/research-online-book/docs/contracts/online-square-minimum-v1/source-fingerprint-v1.json | bbb76f461c1e6e1b1ebe2de9c6cb78d5c421e0bea6512fb28c90104dd8532c7d |
| E:/ABRL/worktrees/research-online-book/docs/contracts/online-square-minimum-v1/targets-v1.json | 6f845210c292f01803e3842002ebcc3795359e7878f3094d5452c582eb62cc01 |
| E:/ABRL/worktrees/research-online-book/BanditRLProof/OnlineLearningMean.lean | 811dcf3741e3d6dee19b2c4a9f43f4b266808b89843a1719e00f239a4687258b |
| E:/ABRL/worktrees/research-online-book/BanditRLProof/OnlineLearningFTL.lean | 8c3574c657f08e0c5291f0689105f9459e92187502f092f4d36d848e52ab4219 |
| E:/ABRL/worktrees/research-online-book/BanditRLProof/OnlineLearningFoundations.lean | e23ebdca2f7ce21a16173c93390fd24d16ba36e403c9d084233f7480e75408b8 |
| E:/ABRL/worktrees/research-online-book/BanditRLProof/OnlineLearningRegret.lean | 0bac6b6e454c5d7bd2244fc115bc8df8cbd9b5505302aa81d03baaeeeec204dc |
| E:/ABRL/worktrees/research-online-book/BanditRLProof/OnlineLearningAsymptotic.lean | 60580602f27c35cb4782d78bd590e73e780023f62e5ae71a06c5a44d09d7ab72 |
| E:/ABRL/worktrees/research-online-book/BanditRLProof/OnlineNoRegretSemantics.lean | db7482a02bf4643ba3d4b15b29dd5a59418ea111763afeed45c51879b996e5a7 |
| E:/ABRL/worktrees/research-online-book/BanditRLProof/OnlineLearningHistory.lean | 3412177ab7dd0ac0e350d8fde7f91e61640d55743d1f17d15c62a65dd4492fc7 |
| E:/ABRL/worktrees/research-online-book/BanditRLProof/OnlineLearningIID.lean | 92af24e6a2c2b1054503492b2bad97cd17ccea2217439f6d2f8a7bedb0de3d5e |
| E:/ABRL/worktrees/research-online-book/BanditRLProof/OnlineLearningInformation.lean | 72bef017a43c293d0d3c449707e4a0e058f4655c2483b54c3120d7b41c98135a |
| E:/ABRL/worktrees/research-online-book/BanditRLProof/OnlineLearningStochastic.lean | 0242481022883958afef677654fadd3f6e37b381f3fe463e3605f3eb0542f2bd |
| E:/ABRL/worktrees/research-online-book/lean-toolchain | b15a57f8ea4c890197465ce1156667ae13d9ed4ab8a9f263a920bf010d967d82 |
| E:/ABRL/worktrees/research-online-book/lakefile.lean | 0164f3b5b5bdcbb237ab15ae8b44da83e183f4b97d5f3832aa4a57f27dc69d45 |
| E:/ABRL/worktrees/research-online-book/lake-manifest.json | 87c3e616f86244550ef39e7415186b11c1d4cf4bef20173196a619d9d4d48f48 |
| E:/ABRL/worktrees/research-online-book/docs/contracts/online-book-v1/source-inventory.json | a2a504cf40d73f9c5e36f00fc1ef3b949ccaf5a558ab603c1c2a86007f30efa7 |
| E:/ABRL/worktrees/research-online-book/research-wiki/papers/sgb-theorem2-interface-frontier-trace.json | 6cc5d9f545aded644d0ee7e3006e714f5e226869a78ae3c1904de542b5e8ca39 |
| E:/ABRL/worktrees/research-online-book/tasks/ONLINE-SQUARE-MINIMUM-20261008.md | 47df5a2a1660eb9ac5376d3aaa1a1a1f1a28e527cc36f4d0854d125474050407 |
| E:/ABRL/worktrees/research-online-book/conversion-windows/ONLINE-SQUARE-MINIMUM-20261008.md | a147fe734e4c4f46667a0c7c2f3e04c675d6b1a1cdfe4a1969248b1844115f35 |
| E:/ABRL/worktrees/research-online-book/proof-obligations/ONLINE-SQUARE-MINIMUM-20261008.md | 2f8cc9142231c5736aaa617ddf7bb3a6cf85dea9b24fe84fef1da32f93b3de8f |
| E:/ABRL/worktrees/research-online-book/proof-blueprints/ONLINE-SQUARE-MINIMUM-20261008.md | f1b30a3e972dac14ec1f01af0c345114fde05e99f930ad99f6946a72be3149a4 |
| E:/ABRL/worktrees/research-online-book/research-wiki/retrieval-index/ONLINE-SQUARE-MINIMUM-20261008.md | 9d4cf1d3a3f0bea19aad1b3711642079a50535abc94517ef0530852b786f2dc6 |
| E:/ABRL/worktrees/research-online-ogd/tmp/pdfs/orabona-v10.pdf | cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/source-contract-inputs-v1.json | 93a048420015392099387c83652b8e4123df48afa50529839ee88911a7b630d4 |
