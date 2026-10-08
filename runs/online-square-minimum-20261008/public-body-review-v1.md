# Square-minimum actual BODY review

Verdict: **accepted-with-explicit-delta**, limited to the actual candidate bodies and canaries. No blocking mathematical or metadata repair found.

Actor /root/source_reviewer is a reused distinct automated source reviewer with prior CONTRACT and staged history. GPT-6 Astra / medium are requested, not runtime-attested; this is not blind, human or external review.

All 362 current fixed inputs were independently raw-SHA verified before and after. All 132 original CONTRACT rows resolve exactly: only the five explicitly task-owned metadata paths use immutable original snapshots. No Lean/source/type/other-task exception is used. The original report and receipt remain unchanged. The pinned v10 PDF SHA is cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17; I actually viewed all four original-detail PDF14–17 PNGs again. The same Mean/FTL/Foundations/Regret producer bodies were read in this staged review and remain byte-identical to those bindings.

## Actual six producers and seven semantic slots

### M001 BanditRL.OnlineLearning.guessing_prefix_minimum

Verdict: accepted-with-explicit-delta.

Actual by_cases T=0 proves empty sums and mean0 by simp; otherwise Nat.pos_of_ne_zero feeds empiricalMean_mem and empiricalMean_minimizes. Neither feasibility nor optimality is assumed.

- **objects**: Real interval squared-loss prefix and actual empiricalMean.
- **hypotheses**: Only y_t in [0,1] for t<T; no supplied argmin.
- **quantifiers**: Every real stream and natural T; every feasible fixed u.
- **normalization_and_indexing**: Same finite range T; zero-based source translation.
- **information_structure**: Hindsight comparator producer, not a learner.
- **conclusion**: Actual mean feasibility AND cumulative-loss minimality.
- **source_delta_and_dependency**: Positive T follows existing decomposition/feasibility; T0 is empty extension, not uniqueness.

### M002 BanditRL.OnlineLearning.squaredLoss_minimum_eq

Verdict: accepted-with-explicit-delta.

Actual IsLeast constructor supplies image witness empiricalMean with hm.1 and rfl, then destructs every image membership and applies hm.2; hleast.csInf_eq derives the real infimum identity. No empty-set/default-sInf escape.

- **objects**: Real sInf of the image of interval comparator losses.
- **hypotheses**: Same finite-prefix interval hypothesis; no assumed minimum.
- **quantifiers**: Every y,T under hy; image ranges over all feasible real u.
- **normalization_and_indexing**: Unnormalized cumulative square loss.
- **information_structure**: Pure pathwise benchmark, no probability or expectation.
- **conclusion**: sInf equals loss at the actual empirical mean.
- **source_delta_and_dependency**: Image contains mean loss and is bounded below by it via M001; IsLeast.csInf_eq is applicable. The image is not asserted finite.

### M003 BanditRL.OnlineLearning.squaredBestRegret_eq_comparatorRegret

Verdict: accepted-with-explicit-delta.

Unfolds complete squaredBestRegret and comparatorRegret and rewrites with the actual squaredLoss_minimum_eq for the same y,T,hy.

- **objects**: squaredBestRegret and shared comparatorRegret at actual mean.
- **hypotheses**: hy only; prediction is arbitrary real-valued.
- **quantifiers**: All y,prediction,T satisfying the prefix condition.
- **normalization_and_indexing**: Same cumulative sums and horizon on both sides.
- **information_structure**: No prediction feasibility or causality follows.
- **conclusion**: Exact signed regret identity.
- **source_delta_and_dependency**: Definition unfolding plus M002; no expectation/minimum interchange or assumed regret bound.

### M004 BanditRL.OnlineLearning.comparatorRegret_le_squaredBestRegret

Verdict: accepted-with-explicit-delta.

Rewrites M003 then applies sub_le_sub_left to the actual M001 loss ordering. Inequality direction is correct; predictions need not be feasible/causal.

- **objects**: Regret against a feasible fixed comparator versus minimum benchmark.
- **hypotheses**: hy and u in [0,1]; prediction arbitrary.
- **quantifiers**: Every such y,prediction,T,u.
- **normalization_and_indexing**: Same cumulative prefix, no averaging.
- **information_structure**: Representation order only, not algorithmic performance.
- **conclusion**: Comparator regret is at most best-fixed regret.
- **source_delta_and_dependency**: Subtracting the smaller minimum reverses the loss comparison correctly; negative regret remains possible.

### M005 BanditRL.OnlineLearning.meanPredict_bestRegret_bound

Verdict: accepted-with-explicit-delta.

Rewrites M003 using meanPredict y then simpa only comparatorRegret from existing theorem_1_3 with identical y,T,hT,hy.

- **objects**: Actual first-half strict-past meanPredict and produced minimum.
- **hypotheses**: T>0 and all prefix targets in [0,1].
- **quantifiers**: Every qualifying stream/prefix; no IID assumption.
- **normalization_and_indexing**: 4+4 log T with T coerced to real; source rounds 1..T.
- **information_structure**: Existing meanPredict_prefix and definition fix current output from strict past.
- **conclusion**: Upper bound on signed pathwise best-fixed regret.
- **source_delta_and_dependency**: M003 transports existing theorem_1_3 for this same predictor; no new arbitrary-initial or optimality claim.

### M006 BanditRL.OnlineLearning.meanPredict_bestRegret_refined

Verdict: accepted-with-explicit-delta.

Rewrites M003 and applies actual meanPredict_regret_refined with identical y,T,hT,hy; preserves initial-half quarter and range(T-1) denominators real t+2.

- **objects**: Same actual predictor and attained minimum.
- **hypotheses**: T>0 and same prefix interval condition.
- **quantifiers**: Every qualifying stream and positive horizon.
- **normalization_and_indexing**: 1/4 + sum over range(T-1) of 4/(real t+2), source rounds 2..T.
- **information_structure**: Initial 1/2 is essential to sharp first-round term; no future data.
- **conclusion**: Exact refined upper bound, not optimized or asymptotic equality.
- **source_delta_and_dependency**: M003 transports existing meanPredict_regret_refined; T1 has empty tail, T0 excluded.

## Complete definition and canary audit

The owned squaredBestRegret is exactly cumulative real square loss minus real sInf of the loss image of [0,1]. That image is generally infinite, not a finite list. Its least element is produced in M002 by membership and a universal lower bound; no assumed minimizer or totalized empty infimum drives the result. The definition has arbitrary real y/prediction and no feasibility or causality binder. The meaningful performance theorems specialize to actual meanPredict.

All twenty named canary proofs and both complete time-only fixtures were read. alternating/quarters have all-time interval-membership proofs. Empty_minimum/empty_regret actually invoke public identities at T0, without uniqueness. Alternating data 0,1 has mean1/2 and attained cost1/2; quarters data1/4,3/4 has cost1/8. Positive-T uniqueness uses the existing uniqueness theorem. Actual prediction values are 1/2,0,1/2; the same predictor has regret1/4 at T1 and3/4 at T2. Fixed comparator0 and1 order proofs invoke M004. Actual_bound, actual_refined and actual_refined_one call the new endpoints; actual_causality uses the real strict-prefix theorem, not a supplied stability or regret conclusion. Actual_identity uses the new minimum/comparator equality.

The signed_alternating proof uses the fixed time-only alternating function as both exogenously fixed data and prediction; it computes regret -1/2 at T2. This is a valid finite signed example, not an input-reading oracle or a proof of generic causal performance. It does not imply negative IID excess risk, expectation/minimum exchange, an ordinary limit, or minimax optimality. Printed1–2 expected fixed benchmark remains REQUIRED next.

## Actual gate evidence and limits

The public focused build exits0 with3329 jobs, and whole canary focused build exits0 with3330 jobs, including cache replay. The direct type-identity run exits0: six neutral-to-draft and six draft-to-public Prop identities, twenty canary identities and six complete definition identities. The actual named axiom log has38 unique checks, all limited to propext/Classical.choice/Quot.sound, no sorryAx. Twenty-six complete native header guards pass; safe-verify is a header/substring/forbidden-token scan, not Lean compilation. The actual selected compiled graph has38 nodes (32 theorem and6 definition),3296 direct type/value references and all16 prespecified VALUE pairs, independently checked against edge data. It is not the full registry or a coverage proof.

Unused-variable warnings in type declarations and the reused FTL proof are nonblocking and remain visible. Earlier preparation failures are retained. No theorem statement, public definition or source premise was weakened. The six results are derived producers/representation/adapters, not six printed theorems or six newly discovered rates.

## Exact original future reader requirements

- **R1 — future-required:** Keep source printed2 square minimum, printed3 actual empirical-mean minimizer, printed4 theorem1.3 and printed5 refined bound distinct; six derived producers/representation/adapters are not six printed theorems.
- **R2 — future-required:** The real sInf benchmark must be proved nonempty and attained by the actual feasible empirical mean; no assumed minimizer or totalized-inf shortcut. Positive-horizon uniqueness is separate; T0 is only the explicitly disclosed empty-prefix extension.
- **R3 — future-required:** Retain interval targets for the same finite prefix, source rounds1..T versus Lean0..T-1, and refined source2..T versus range(T-1) with real denominator t+2; performance endpoints require T>0.
- **R4 — future-required:** Generic identities/order consume an arbitrary supplied real prediction trace and do not assert its feasibility or causality. Performance endpoints use the actual meanPredict first1/2 and later strict-past empirical mean, not an arbitrary future-aware algorithm or arbitrary initialization.
- **R5 — future-required:** Keep signed pathwise best-fixed and comparator regret; their values may be negative. No nonnegative regret, absolute-value/rate/ordinary-limit claim follows from the minimum representation.
- **R6 — future-required:** Do not interchange expectation and a hindsight minimum. Printed1-2 minimum of expected fixed loss and causal cumulative IID variance benchmark remain required next, distinct from this produced pathwise minimum.
- **R7 — future-required:** Reuse the actual shared empiricalMean/comparatorRegret/meanPredict and existing theorem1.3/refined proofs in the same library and registry. Draft closed-Prop/whole-definition equality compilation is separate from actual theorem-body proof; disclose every actual source delta.
- **R8 — future-required:** Keep source/compiled-body/canary/kernel/combined/root/Tests/harness/reader/site/native/PR gates separately evidenced. Only bounded square-minimum hinge may close;16C1sourceitems/proof-totalnull, five main-relative modules, full C1, incompleteC2,3-16/necessaryappendices and active totalGoal remain required. OPENunmergedPR192stack is not main/live completion.

All R1–R8 remain pending reader obligations, unchanged from CONTRACT; none is discharged here. Combined root/Tests/full harness, registry/readers/site/pixels, own shadow/contributor, FINAL, native acceptance and PR remain separate gates. This BODY verdict accepts neither package nor Chapter1/2 nor the active whole Goal. Sixteen source items are not a proof-leaf total; remaining expected/IID benchmark, other main-relative audits and necessary chapters/appendices remain required.

## Raw reviewed bindings

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
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/snapshots/CONTRACT-review-tasks--ONLINE-SQUARE-MINIMUM-20261008.md.raw | 47df5a2a1660eb9ac5376d3aaa1a1a1f1a28e527cc36f4d0854d125474050407 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/snapshots/CONTRACT-review-conversion-windows--ONLINE-SQUARE-MINIMUM-20261008.md.raw | a147fe734e4c4f46667a0c7c2f3e04c675d6b1a1cdfe4a1969248b1844115f35 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/snapshots/CONTRACT-review-proof-obligations--ONLINE-SQUARE-MINIMUM-20261008.md.raw | 2f8cc9142231c5736aaa617ddf7bb3a6cf85dea9b24fe84fef1da32f93b3de8f |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/snapshots/CONTRACT-review-proof-blueprints--ONLINE-SQUARE-MINIMUM-20261008.md.raw | f1b30a3e972dac14ec1f01af0c345114fde05e99f930ad99f6946a72be3149a4 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/snapshots/CONTRACT-review-research-wiki--retrieval-index--ONLINE-SQUARE-MINIMUM-20261008.md.raw | 9d4cf1d3a3f0bea19aad1b3711642079a50535abc94517ef0530852b786f2dc6 |
| E:/ABRL/worktrees/research-online-ogd/tmp/pdfs/orabona-v10.pdf | cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/30_worker-M001-v1.md | bd026d6fb5fce2b183b74c15d4089f6eb41126d79a30d9f48140cac4363d12db |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/30_worker-M002-M006-v1.md | 8deea35775daf531a599e05fd0d2c23df3939305f6328c752725a3de3a4a20c2 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/actual-canary-lookup-v1-exit.json | 298b064e3326c00eb57d3c35888338828a0eccd045aa266fc359c0b4d74a7ee2 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/actual-canary-lookup-v1.log | 49f5b7a8b6709d93824912476f07f9b30bcdd6159e443f3a4853336f60e4d2d3 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/actual-endpoint-lookup-v1-exit.json | 6bc02d328c44b2f7008bd545549958e25ca2e2442c9889d77cef41a0a92d8b6a |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/actual-endpoint-lookup-v1.log | e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/actual-public-canary-headers-v1.json | e9557f1db3b877d5cbefb5ff415cfcd7f6e3ba6fe88772d0be4d6c2e5ee56b45 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/actual-public-lookup-v1-exit.json | 55ff762b7f150db68b6af543896e178d940ef9013fc5a3c88662d8bf61a90efe |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/actual-public-lookup-v1.log | eaef494cd76c9d9b1541e1978aa79bd03bc6a9cb85ca957a11ea8b1dbf8884a5 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/all-axioms-v1-exit.json | 4bbc2921ff3c6b7a4c99cb0742ededd248a646966c0054269f4265f26021a9c5 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/all-axioms-v1.log | 608ecf7619e5a4c30149a56ad8e6c69b5114bc71fcdf60dfcc52cd3fe19a0cda |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/all-exact-types-v1-exit.json | c2a9cdd7c70e3b6a5ca125910d5453c82c3d974e02a376df33dec91844c50c41 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/all-exact-types-v1.log | 73781d0995850639cf5e7001bc9efaaf8a5eb1c7784bdc60bbc8c37778592883 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/all-six-focused-build-v1-exit.json | 3f000e0844786af612bb867c3a6de751adbd5dedfa2e44e3e1d405e14f01aa87 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/all-six-focused-build-v1.log | 63489f4d82c34973b9da69420f82234dcd96205ecc30b51e98827fb107a73388 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/audit-bodies-v1.py | 76a94ddb08f3a86138540aa3f113806e7de39d0dccae08f28737e8d1fac83e6c |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/axiom-bindings-v1.json | afc08e69831f8c670775d443ed5d11e70300d83db27c14a34509442ed628f897 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/body-bindings-v1.json | 8250d961cca74c2ee1a630166e581ac3b623469f92392f486be46a34fc154085 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/BODY-review-packet-v1.md | 225352dc5d900122fac6cbc685b619b5becc379d97251965943d9dc83cd8ea94 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/build-canary-v1.py | 0cc9cc71d077fac39f715798930fe2855c144ba8d5ed12ecdf83b8f35afde5b8 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/canary-candidate-v1.lean.raw | 275e4c80fd8c8769293d810cc4e94ecc67d64f9f9c0f272f3e6c1340279ee881 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/candidate-event-v1-exit.json | 4c0131390197e355d5fdfc24e4c5ede7805340082c2376c86925c28716c6f95a |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/candidate-event-v1.log | 9fd021a8298d45093a41902b3b0dbc1ed2394b156f8b0c13e0f0e056906bacfd |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/common_reviewed_v1.py | 22379d8578d58bbaf525019f68283518f29de534496b6e8c638c072aaa5beb31 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/compiled-value-graph-v1-exit.json | 98218e4505e124e0a5b590fc47776523eca8e2db533d9f7b0858524a5155fe35 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/compiled-value-graph-v1.json | 770f3dbedfc4d2bf739bd70cd0ef0a2360fc996e6b973a6e041cc5d00f57d0f1 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/compiled-value-graph-v1.log | e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/contract-review-baseline-resolutions-v1.json | a20da589dc13b0bbbbb00d03f6834811a466f6bd825e1c2ed7b54d0304c0312c |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/first-leaf-fence-v1-exit.json | 7c2627029918e9c98d21e240526fe66e6776c962d4175e59d315210bdfc85ed2 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/first-leaf-fence-v1.json | 405cf636ae3cd2ea9cddd7f29d074b1e7273d1ba922de925673a8ccce49c296d |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/first-leaf-fence-v1.log | 405cf636ae3cd2ea9cddd7f29d074b1e7273d1ba922de925673a8ccce49c296d |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/first-leaf-focused-build-v1-exit.json | d0d2421cf0d038238bd85b3bcddbf0a4a9d00402578820e2809fc9cbab59e0c9 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/first-leaf-focused-build-v1.log | 53ecc47955924e736e239431d83aadaf5f24b78fa950d631a18b412af42d0866 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/first-leaf-safe-verify-v1-exit.json | 25d911899bcf6b11c4f77e4a980bae92050c5adfd396b24b22381a1f4e1ac876 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/first-leaf-safe-verify-v1.log | a0431aaffc473d99c2da1d11df8506a30b4bf4b57cd0b172b4f76228e0b72ee2 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/first-worker-compiled-v1-exit.json | 32b386be35a01b4adfeeaf105443fd1df175e055f1b6ce4d7c717a99d68c2e0a |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/first-worker-compiled-v1.log | ab139eeb6ed16dbefa3cae090276347063fb8608fa726898d1ba0831c747f6e5 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/first-worker-running-v1-exit.json | 439737dcd828c4dd38c647352b62f1f77e0afb6c90b864f45fdd64ff12e8b275 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/first-worker-running-v1.log | 10cc248af2343dcfeb02dd97ab7377b474623f8e40a360d58a07ce181ac2e9e5 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-fence-bindings-v1.json | 89bfb5f36e5908be541be0a93363b7f05f7c5ce1eaeea5bf4d3223f66f08fd06 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-fence-canary-actual_bound-v1-exit.json | 868b7094fd6c72766de5c64d63c3e40631b9217e40df3facda1885707e1c0b83 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-fence-canary-actual_bound-v1.log | f55dd5512554c3e522306a05d53bbe3c882383cc99a1a1fafa4accc69bb31bca |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-fence-canary-actual_causality-v1-exit.json | 618c9c1f298d751b86fe01864397f6e2a18c022021711964b529071aa3117a3a |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-fence-canary-actual_causality-v1.log | 2a080977f8c633af4561dc685566b8773176b2df07e2654eb896ff9b3ebd4791 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-fence-canary-actual_identity-v1-exit.json | 99e2b0cc7fe7a235d3d3206341229310670e4c8e38303c5619a145ad0e7c7e0d |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-fence-canary-actual_identity-v1.log | 62813d59a29d1238854dff5c6a791792c72d3b0d189a7635f81de9c6d4bbbe54 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-fence-canary-actual_prediction_values-v1-exit.json | 9fddc27e8f838c9c403d7338d327540ed21f4478b004f7a271813420758bc6c7 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-fence-canary-actual_prediction_values-v1.log | 459c9e43e75a75a1ffbb907adc522595ff2d3041337294dc2631eef377f5e82f |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-fence-canary-actual_refined-v1-exit.json | abcba030bf06d55b373a5fa1beda67c76045b0f738718ec542d04fb58759b87c |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-fence-canary-actual_refined-v1.log | 3babba8b8cc9e741293629c1b452e9ed7187ef94e5c7ffa2af5622f94eea2a11 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-fence-canary-actual_refined_one-v1-exit.json | 7d09581584919d0993c9e78c982a73d4b3ce35bb17ff030163ef44f2c1beceb7 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-fence-canary-actual_refined_one-v1.log | 98c83a97280b5458bfacf61e0fd5b495d38d28fa9bd406c1486db684964508e6 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-fence-canary-actual_regret_one-v1-exit.json | 1ce6a189f4bda992890e81ba7266edbf0ab73eb0c7beb731320dcf012f7d2ab0 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-fence-canary-actual_regret_one-v1.log | 1c48321444376ba0d12720d9688d6852a2b6738c40d3c977a793a266993b4620 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-fence-canary-actual_regret_two-v1-exit.json | 81ddcd7d86d290c34dabfa5b0fa424338fd959acc30b08daf4092b4d4f10bfdb |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-fence-canary-actual_regret_two-v1.log | a846a7cd9e7b6a8a9aab9294ca0a644b951167f3fdf979d338d0218cc1df27a7 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-fence-canary-alternating_mean-v1-exit.json | f9687f177a0911e4c16f5efb86f258c9aaec5ea0df06e3dc1a245de5f687976e |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-fence-canary-alternating_mean-v1.log | f97db27ab2933cc3ed5e08693e6e246f96c9156a5e659cf84c9ac8a211c2e1ae |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-fence-canary-alternating_mem-v1-exit.json | 5b94c71b75555a7701dbad7659aff7f23dbe15ff594ae51034875f989b657c65 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-fence-canary-alternating_mem-v1.log | 741a2d927a085ef0d7bdfb0103ea5823a9991dff17dae3624c97cdf00eb37154 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-fence-canary-alternating_minimum-v1-exit.json | a15527027f64e0b30b0a3b18a0ea25a1ec5efd8ab1eecac62668ce4f8ac80396 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-fence-canary-alternating_minimum-v1.log | a5952513c3bea8971f2cb6ad64b0973374dad83dc5c3445b28ab723bcd4bfe93 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-fence-canary-alternating_unique-v1-exit.json | f7b6dc03cd39140cdb1bac31849367051e08be95ab6d534ec7c38e3dd090b48b |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-fence-canary-alternating_unique-v1.log | 838dfb899cb1bca582845aced4fd63ab0c2ce20471657803921a419115ab8b3b |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-fence-canary-comparator_one_order-v1-exit.json | 474e1a84e7ba69b83098cf2056bc7931d92015014d32ea62e8f79511c9f9706f |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-fence-canary-comparator_one_order-v1.log | 6cc1e3574aeac0291a29a8292b95709d7113ee47d85ae899b37ec5287d47a95f |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-fence-canary-comparator_zero_order-v1-exit.json | fbfd010f3a4843293d8a50a5b41f9cb97c5f8a6eaf86acbe625852a271da41c3 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-fence-canary-comparator_zero_order-v1.log | a01df6a551889ecc0846232328fb647a57a5acd7919de67e3c12d2b9d72e226e |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-fence-canary-empty_minimum-v1-exit.json | 9f98516e59590e97b764fbdc505da8ea9334ab3ca639ad4419373187eedeaf69 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-fence-canary-empty_minimum-v1.log | a8455c35a26d704f1d91c293d82a92b18a45b357d825918a934de10aab3eca66 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-fence-canary-empty_regret-v1-exit.json | 39ef3753a78dd3ce0cb91125c2c5877ec6eef1728ad964142bf476c7b2103cfc |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-fence-canary-empty_regret-v1.log | 9bcd6fba48ff8102b882844f70890c641192c8504da3ea061ec4a4d649486730 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-fence-canary-quarters_mean-v1-exit.json | 1bd106ae91b8d02419f18ca5cf4bc5c46a9feea9e4dc0a4cd97fbd4c215b5154 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-fence-canary-quarters_mean-v1.log | 2543d2db3e4502e5e3ef51aa23e896da757587f1006f3dfbce36a82d52914f00 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-fence-canary-quarters_mem-v1-exit.json | b7fb252215d612777ff84c0325e057b9f95f534fb75d427384b4c4453532dadb |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-fence-canary-quarters_mem-v1.log | 9a399a6df63c972d2a497d44659f9dcd32a78713a018aed74b12042de5d5a4af |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-fence-canary-quarters_minimum-v1-exit.json | e213a1adac671f1709c006b874bf8586479e571c237e72880c95e0f5d8ea5fb1 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-fence-canary-quarters_minimum-v1.log | f12ddf07608fd9bdd6f5d8f7754c0d3f545cc234ba8e9f65a45a042e95ccaa59 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-fence-canary-signed_alternating-v1-exit.json | 605b250b72f30162b5278c803b4ba5cca02b3e9420ede118b402d060fb74ebab |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-fence-canary-signed_alternating-v1.log | 0dcd29ed5f085892267a4c486afe506b472f58bd75645e6351aa6b55dd768083 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-fence-public-comparatorRegret_le_squaredBestRegret-v1-exit.json | f0124c8ba4419d6b45d66bd4f65f273d6067ca62411d38d7eab853be5e5a33e7 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-fence-public-comparatorRegret_le_squaredBestRegret-v1.log | 9bddb2f4e8300c2888366d1f1aa174cfd1fcf7e5dbbe582cacdb2490833c3a41 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-fence-public-guessing_prefix_minimum-v1-exit.json | 5b7f109a2b4c42a1e5fd9be211761a4e3ac501af85df1470984765a38aa5a750 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-fence-public-guessing_prefix_minimum-v1.log | ed042d03b6c320188316d7c9e1a8a6242dcf32e9fe9b49ee94e4e5a24fc4b7e6 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-fence-public-meanPredict_bestRegret_bound-v1-exit.json | 9e28660c527f5537723b0403a7e30c62673820c196f0b3030b816ffd5512649d |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-fence-public-meanPredict_bestRegret_bound-v1.log | bf7d66edf560540a48543f4e81ae7a928415aa4d95220e940521b838257c5861 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-fence-public-meanPredict_bestRegret_refined-v1-exit.json | 4ab05ec3fa3aff67a270661c3003f3ea6f2766768deded6a53c324ce4ac0d067 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-fence-public-meanPredict_bestRegret_refined-v1.log | ac765f793942e4954243d23359fd6f39d79cd9f20e63966f2f9a0bf42cc00cb5 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-fence-public-squaredBestRegret_eq_comparatorRegret-v1-exit.json | 9277e394cd4c473ea7a7eb1d0a20b9a68aabf0e22872dd161b81aea785eef75a |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-fence-public-squaredBestRegret_eq_comparatorRegret-v1.log | 541c6a85e4d54639eade011f1b6ebf073c33370a811fee8c38cc38decb1fec27 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-fence-public-squaredLoss_minimum_eq-v1-exit.json | 74daaa5715319476ce01f76bf2e726bc25340ee80902a27d6212f1afedadc40c |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-fence-public-squaredLoss_minimum_eq-v1.log | e6457ff6c9b4fd643fef7536a8cc80c91acf8ed82f5cae45b7dae9a89726b107 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-header-fences-v1/canary-actual_bound.json | f55dd5512554c3e522306a05d53bbe3c882383cc99a1a1fafa4accc69bb31bca |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-header-fences-v1/canary-actual_causality.json | 2a080977f8c633af4561dc685566b8773176b2df07e2654eb896ff9b3ebd4791 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-header-fences-v1/canary-actual_identity.json | 62813d59a29d1238854dff5c6a791792c72d3b0d189a7635f81de9c6d4bbbe54 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-header-fences-v1/canary-actual_prediction_values.json | 459c9e43e75a75a1ffbb907adc522595ff2d3041337294dc2631eef377f5e82f |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-header-fences-v1/canary-actual_refined.json | 3babba8b8cc9e741293629c1b452e9ed7187ef94e5c7ffa2af5622f94eea2a11 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-header-fences-v1/canary-actual_refined_one.json | 98c83a97280b5458bfacf61e0fd5b495d38d28fa9bd406c1486db684964508e6 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-header-fences-v1/canary-actual_regret_one.json | 1c48321444376ba0d12720d9688d6852a2b6738c40d3c977a793a266993b4620 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-header-fences-v1/canary-actual_regret_two.json | a846a7cd9e7b6a8a9aab9294ca0a644b951167f3fdf979d338d0218cc1df27a7 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-header-fences-v1/canary-alternating_mean.json | f97db27ab2933cc3ed5e08693e6e246f96c9156a5e659cf84c9ac8a211c2e1ae |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-header-fences-v1/canary-alternating_mem.json | 741a2d927a085ef0d7bdfb0103ea5823a9991dff17dae3624c97cdf00eb37154 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-header-fences-v1/canary-alternating_minimum.json | a5952513c3bea8971f2cb6ad64b0973374dad83dc5c3445b28ab723bcd4bfe93 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-header-fences-v1/canary-alternating_unique.json | 838dfb899cb1bca582845aced4fd63ab0c2ce20471657803921a419115ab8b3b |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-header-fences-v1/canary-comparator_one_order.json | 6cc1e3574aeac0291a29a8292b95709d7113ee47d85ae899b37ec5287d47a95f |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-header-fences-v1/canary-comparator_zero_order.json | a01df6a551889ecc0846232328fb647a57a5acd7919de67e3c12d2b9d72e226e |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-header-fences-v1/canary-empty_minimum.json | a8455c35a26d704f1d91c293d82a92b18a45b357d825918a934de10aab3eca66 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-header-fences-v1/canary-empty_regret.json | 9bcd6fba48ff8102b882844f70890c641192c8504da3ea061ec4a4d649486730 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-header-fences-v1/canary-quarters_mean.json | 2543d2db3e4502e5e3ef51aa23e896da757587f1006f3dfbce36a82d52914f00 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-header-fences-v1/canary-quarters_mem.json | 9a399a6df63c972d2a497d44659f9dcd32a78713a018aed74b12042de5d5a4af |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-header-fences-v1/canary-quarters_minimum.json | f12ddf07608fd9bdd6f5d8f7754c0d3f545cc234ba8e9f65a45a042e95ccaa59 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-header-fences-v1/canary-signed_alternating.json | 0dcd29ed5f085892267a4c486afe506b472f58bd75645e6351aa6b55dd768083 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-header-fences-v1/public-comparatorRegret_le_squaredBestRegret.json | 9bddb2f4e8300c2888366d1f1aa174cfd1fcf7e5dbbe582cacdb2490833c3a41 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-header-fences-v1/public-guessing_prefix_minimum.json | ed042d03b6c320188316d7c9e1a8a6242dcf32e9fe9b49ee94e4e5a24fc4b7e6 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-header-fences-v1/public-meanPredict_bestRegret_bound.json | bf7d66edf560540a48543f4e81ae7a928415aa4d95220e940521b838257c5861 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-header-fences-v1/public-meanPredict_bestRegret_refined.json | ac765f793942e4954243d23359fd6f39d79cd9f20e63966f2f9a0bf42cc00cb5 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-header-fences-v1/public-squaredBestRegret_eq_comparatorRegret.json | 541c6a85e4d54639eade011f1b6ebf073c33370a811fee8c38cc38decb1fec27 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-header-fences-v1/public-squaredLoss_minimum_eq.json | e6457ff6c9b4fd643fef7536a8cc80c91acf8ed82f5cae45b7dae9a89726b107 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-safe-canary-actual_bound-v1-exit.json | 24b348c1bbd123a253e2b6877fb7bf481123d93b0d534d0459284aed36e08d7f |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-safe-canary-actual_bound-v1.log | 1507535926af105a0094b7dd345881d66f5e7db16c77ed525a0682da3f83a4a2 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-safe-canary-actual_causality-v1-exit.json | f35b6c044e18ff03670f2207d9c19b4f954b93e18a12202f5a2f204346047b28 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-safe-canary-actual_causality-v1.log | 7af201ccaa7caee2762ca34a4be80875edcf05d5c861ad93c0883b363872b8eb |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-safe-canary-actual_identity-v1-exit.json | 65b4f515bd9bc7a2a8175da75659389f85033a960ca9238ae9aa2a59634f977c |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-safe-canary-actual_identity-v1.log | 7c0b4d05fd1f4049e102de8069542e749657068a00b04908fb2507a5adeed440 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-safe-canary-actual_prediction_values-v1-exit.json | df5deadef83907947abd03256b8753c8d056acbc643623b5badd747d57cc6f47 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-safe-canary-actual_prediction_values-v1.log | b07853309fb42bf5c44602ba000a941849a998f3e012a12df0704070ccf05d02 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-safe-canary-actual_refined-v1-exit.json | 80771e3b749f4897e615af94c198f69e6655e42c96569e6318f0d4b814bb23c1 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-safe-canary-actual_refined-v1.log | 06618963a74c75ef0780254c0551b00c461bbeb9a773e14e0ba8c604aac8cf07 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-safe-canary-actual_refined_one-v1-exit.json | ca606fab8213065bbb5fddec3186689de9445661290c1a83bd541186edf65dff |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-safe-canary-actual_refined_one-v1.log | a5695faf1068ca0437a8c8bb2b18331efa48c0e927e93c67bf6c2d8f2915ce73 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-safe-canary-actual_regret_one-v1-exit.json | 4ad60edd668fdc06f3d76eac7cbef0b0c45f4d5c4a299e90e2f131bbeefa0090 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-safe-canary-actual_regret_one-v1.log | c4ad0e57ec1bad585c05312bb16e1149559fed08cff13682a615c58fc5619742 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-safe-canary-actual_regret_two-v1-exit.json | 656967b92b5cf6167af7d838f9f3b66c95dcb63db2c976a480088ca3f3ad9f77 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-safe-canary-actual_regret_two-v1.log | 31d2eccadfdd66538fa6a3f2235162859af8b365963343e95c82c99fc83ab6ce |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-safe-canary-alternating_mean-v1-exit.json | 4f7c6f88a5715a60df95370ef26a7af685c5a76461bf76cf1acf37f48b1eced7 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-safe-canary-alternating_mean-v1.log | 578b3e93349924965368e64ff66d0a00ee26a2c53f54b690a684c63bec7fbf8b |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-safe-canary-alternating_mem-v1-exit.json | d95c0dc95883a1ce010b9ea73d77661e2877af3012d93e9eb9c125ec3a5b99a7 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-safe-canary-alternating_mem-v1.log | 666058ff0573f8c45e5c06ca2533cd66dfcc519eb0bd45eb0898c3ec33a01f69 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-safe-canary-alternating_minimum-v1-exit.json | 95b30876812846e200d26408a8aa21bbdac97496035f322e0603c42d8233b544 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-safe-canary-alternating_minimum-v1.log | 8c7756d1076e44282c201d7c430d9da197f8ab69ed2312bf756b899cb2fc06d3 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-safe-canary-alternating_unique-v1-exit.json | 51b2a622b707f37e86e1827383554d283010ba9cb950444d96e32278d9f5dc7e |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-safe-canary-alternating_unique-v1.log | 6d7be5059cdb84a58ea5aa46eb148d43d74d64d5ace4743ee6663e68814828d0 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-safe-canary-comparator_one_order-v1-exit.json | accce8459defb82f4fdb597d85ab50c00b30ed25a1b294b43276f1026eeeab1f |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-safe-canary-comparator_one_order-v1.log | 83ac9c8a440328256c75f111eb533b96ecacbb7984e85ee9df7f6731601e1161 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-safe-canary-comparator_zero_order-v1-exit.json | 38593955fe6959607232eaf37a04aa44dbf9c9b0e9a333cf11505881d9508abd |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-safe-canary-comparator_zero_order-v1.log | a2a8ac21d67c2d975d6f984b941b943337f94f3f9678d07f5da7699de59c5c48 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-safe-canary-empty_minimum-v1-exit.json | a450608db122fd7b30e45e6d11161f4874f1d737bb737a01d6566693fef3e9c5 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-safe-canary-empty_minimum-v1.log | bea428d2c94aebc737c75ed75d872b3a92d8a467bfdd95c592c4a79be1000473 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-safe-canary-empty_regret-v1-exit.json | a419fb7cd4e982f94e8dac8abcbd0a277475953323e79b40847c1c1fbb6cf7b9 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-safe-canary-empty_regret-v1.log | 8ddc6fe1027278172637ad99b6afdd33b296abe10d1a66cdf61a33d9bbea15d2 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-safe-canary-quarters_mean-v1-exit.json | b90488d10c485d20520535bb3878452b317e97f21a25155789125c983174d509 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-safe-canary-quarters_mean-v1.log | bee3e2584b5f6c2068ffe46f05565e6dc1482ea42496c9131281437b8caa17ab |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-safe-canary-quarters_mem-v1-exit.json | 1d27b81758d98be0e803dd2ad7b8421fbdbf1d230d1b69b1d44a5b6b5616314c |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-safe-canary-quarters_mem-v1.log | 819b56944fa722ebddee5e0d34198ed850cd2463bc7911e0a392013ba1c912bd |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-safe-canary-quarters_minimum-v1-exit.json | 9c450ef9bfd2adc7264f9c0be8d9d5174685fdc7386c080aa3a9d254c6dc09c5 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-safe-canary-quarters_minimum-v1.log | 23ee2ee5a2fcbace4ed7668f33ee75c5606314cdb51ffdbd48621085340020de |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-safe-canary-signed_alternating-v1-exit.json | 8e5a43bc9b73ebb800fa1a9357d6be326004107a83417f14d1fe9907a297ba05 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-safe-canary-signed_alternating-v1.log | c3a212921546b8dfed47c2bdd0beb9eea8bc00b7533f92098f12af0fa2ffdd8d |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-safe-public-comparatorRegret_le_squaredBestRegret-v1-exit.json | 4eab8cb1c59bc0a874a036bb9b17fe277d121a779cfd167ffa19afcc79815153 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-safe-public-comparatorRegret_le_squaredBestRegret-v1.log | 4edbf64ee147c4f0163a6cd966471e181b3a842a89a4bc95290b94b6f077db89 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-safe-public-guessing_prefix_minimum-v1-exit.json | a45931432c5d3bf29e507492944d0b70825345772ab5564a1cc06ce5f455abd0 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-safe-public-guessing_prefix_minimum-v1.log | a0431aaffc473d99c2da1d11df8506a30b4bf4b57cd0b172b4f76228e0b72ee2 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-safe-public-meanPredict_bestRegret_bound-v1-exit.json | ad00376967e4dedc7cf41e69d2bc3ec47d5d92b6aca82b43b2dd344ce2956669 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-safe-public-meanPredict_bestRegret_bound-v1.log | 2494426b2703480786fcac826d06bf7a5d89e000f4d6786627ce8f64e1248778 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-safe-public-meanPredict_bestRegret_refined-v1-exit.json | 9ab7a2574171ea5d13283d8d1c6ca77fd25924276c89114877d022383a030a4d |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-safe-public-meanPredict_bestRegret_refined-v1.log | ee6f40ab54a47b31d1a9c4f97c5719de742113b577091496d42c9ef7f5c3d57b |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-safe-public-squaredBestRegret_eq_comparatorRegret-v1-exit.json | eff3c89ecd9d6a8a64623754f0ef68bd30df91e1f9a24caa9a210fb62e29d437 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-safe-public-squaredBestRegret_eq_comparatorRegret-v1.log | d0a51d4f889d308eb0e675b306689c71dcb648e5c6b6cffcb5a3c019697608dc |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-safe-public-squaredLoss_minimum_eq-v1-exit.json | 51a637ca633e8e753b92046172399d501dafea8c53159131fe976c93c1366965 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/full-safe-public-squaredLoss_minimum_eq-v1.log | 75c7388427aa974e630b3214b94663fdead6aafed09df66dfcd93ba42272a4ca |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/leaf-progress-v1.json | 55da446182a6d546adc58d2322dc1547e4904240707b17729ff4ddb013fc7847 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/leaf-progress-v2.json | 55ba510394a8195813fbabff06747242426cd3de14d131ebde0bde4ee3b60c4c |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/leaves/all-axioms-v1.lean | fb3a525e0a8a0de67d59f8cd37fb559ad2609c5f71288c716a3419b4c2dce4b9 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/leaves/all-exact-types-v1.lean | 86e55c2a6e436837a8ab1d914e5ce7038a4cc3259f03fc793d8ada8721379aa7 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/leaves/export-actual-dependencies-v1.lean | 2fd8466be64b3f1a6297244a8d01454a8830572fb86141d0060c4e4e155e315b |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/M002-v1-fence-exit.json | 8814fba8829401dbd05a8eba62b5dd32d1ab8a87757743a95e5cb46ab1e96a93 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/M002-v1-fence.json | 8cbc7871372c0098eb400ba1c177f1cc073acd143180dc4dbf4dd4e11d9f8829 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/M002-v1-fence.log | 8cbc7871372c0098eb400ba1c177f1cc073acd143180dc4dbf4dd4e11d9f8829 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/M002-v1-safe-verify-exit.json | 3c1857ef7d8698ec7b802df9de2d6a37700f1800d42c358c7b21faf88e81fc49 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/M002-v1-safe-verify.log | 75c7388427aa974e630b3214b94663fdead6aafed09df66dfcd93ba42272a4ca |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/M003-v1-fence-exit.json | 38a7dc0e02bb8abd7dc53532cc72461271083af2a3489ac355a0143a80682a40 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/M003-v1-fence.json | 2a416b3b1732c67bea53265264ca99e9594ed323ed789178289712d16b7eaafe |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/M003-v1-fence.log | 2a416b3b1732c67bea53265264ca99e9594ed323ed789178289712d16b7eaafe |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/M003-v1-safe-verify-exit.json | 2540c1631f0c136568d9d2833e8058fe85b98bc033976682428f9bc8dda244eb |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/M003-v1-safe-verify.log | d0a51d4f889d308eb0e675b306689c71dcb648e5c6b6cffcb5a3c019697608dc |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/M004-v1-fence-exit.json | 71bbfc32b90a41a6148218b0ce0c956243c67db38f0a645144b8385ab09b91af |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/M004-v1-fence.json | 5e3b51a4e6ee991939adad8355a190875717ad6d19f3890a26c6867bcf094337 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/M004-v1-fence.log | 5e3b51a4e6ee991939adad8355a190875717ad6d19f3890a26c6867bcf094337 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/M004-v1-safe-verify-exit.json | eae542f5b6896a0c5160d1192e4f0502cd54c4805c31cef3b00c800540e7bd43 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/M004-v1-safe-verify.log | 4edbf64ee147c4f0163a6cd966471e181b3a842a89a4bc95290b94b6f077db89 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/M005-v1-fence-exit.json | 5a654e5bf80368f34b3063a76c14e35b75dcd5ede4f82d851e6d4a9bb572c835 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/M005-v1-fence.json | ebc581b3f6a7d707e1c06d84e0d3441febbbc8bb520bff614b47047707bfdc77 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/M005-v1-fence.log | ebc581b3f6a7d707e1c06d84e0d3441febbbc8bb520bff614b47047707bfdc77 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/M005-v1-safe-verify-exit.json | 7c05b2b56e6df1573aac5f593199cece0a1da6271328f337f7f70683ae00b994 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/M005-v1-safe-verify.log | 2494426b2703480786fcac826d06bf7a5d89e000f4d6786627ce8f64e1248778 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/M006-v1-fence-exit.json | c7dc2aeadcbb377df96b45c816bc5a2d85c1806c57833b00a4bd921d62773db2 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/M006-v1-fence.json | f9d8a76667c421fa52c5e8f6e744aeb193f5d4f17391c0c221591bd78e1d372c |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/M006-v1-fence.log | f9d8a76667c421fa52c5e8f6e744aeb193f5d4f17391c0c221591bd78e1d372c |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/M006-v1-safe-verify-exit.json | 925c56c347d2b33db1716da4bcde7f161c07511b529c428cb47ff7f93adfaec2 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/M006-v1-safe-verify.log | ee6f40ab54a47b31d1a9c4f97c5719de742113b577091496d42c9ef7f5c3d57b |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/memory_digest-candidate-v1.md | 3da1fa3361ef43d2e37dbf73142224ad11bb8317ea2c88172d15af5e64834e3e |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/prepare-body-review-v1.py | d046764b0cc95add94022f120e85c63f0697c0cdde863e9bbbd5002c84a1da95 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/proof-obligations-candidate-v1.json | 5c7c89c23b66548410c923d387d605f638488165236b6ff24335230be4c2355c |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/prove-remaining-v1.py | 3bdd99a9a10ea17987214e74e52894c1ef21c04f6a25ee24274821528adfaa6a |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/proving-event-v1-exit.json | 956fcc7d6adca6a778886dc157dbf628134a0bc6a09c2f7efdf2c594976b5274 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/proving-event-v1.log | dbbb00c9d7704f68a428afd9cccf5d5a4b3963920e9a9035a1be9cd27c3e07e4 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/public-canary-focused-build-v1-exit.json | d864ec93178d339d4b7ed9d675c3fae646f5df74c84c850c0d922c1874eb014f |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/public-canary-focused-build-v1.log | b72ef47b1fe95f8f58f522ad3278f0f061c72ed060b31d7b068f03d746e9ae2a |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/public-canary-v1.json | 8a356c22273f6db7b5fe84371ebb4137cfa0f32aab7004743fcf35c8274f677f |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/public-candidate-v1.lean.raw | 7bbfb2538dcdaed8c208571c248723d89ed8980e5e899339aa4c3b48a55c3210 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/remaining-worker-compiled-v1-exit.json | c4cda42b73a6340451213c1d0f0920380997ccc70d80ddbf0f3239c74035e3e9 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/remaining-worker-compiled-v1.log | d67f9e3175afb938dcb8306274020d9c2a7cfc34141d6b4219d5a2507de647f2 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/remaining-worker-running-v1-exit.json | a003372cef4bcab9bd826463e6d8b3431068bdb4b5990efbb5cf72c5139ca595 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/remaining-worker-running-v1.log | 9671d8b582fa483875f4e6a159fd89b2ae3fbaac6d6b02f6e7486ca4c1248bce |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/required-value-pairs-v1.json | 70c3c743963fe1119ff11db0fa0137a1130e9091fdd2162020dd6ab9254b017a |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/snapshots/BODY-review-conversion-windows--ONLINE-SQUARE-MINIMUM-20261008.md.raw | a52648d91408235a21549fad820638c6edc28e9980fe35985eceb9cf82d7bd33 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/snapshots/BODY-review-proof-blueprints--ONLINE-SQUARE-MINIMUM-20261008.md.raw | 5422693cdc4923590822e88551d66dee91d12052d4bc0000c7584b1438897df7 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/snapshots/BODY-review-proof-obligations--ONLINE-SQUARE-MINIMUM-20261008.md.raw | 7d6d807140f167167b6a9e64b56f61ed7e4bfe39052a32c35bfe7451449a52c5 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/snapshots/BODY-review-research-wiki--retrieval-index--ONLINE-SQUARE-MINIMUM-20261008.md.raw | e9ab9711269259930173a2556d8d5a02a50873e538ccafa0a9236a0da32ddcdd |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/snapshots/BODY-review-tasks--ONLINE-SQUARE-MINIMUM-20261008.md.raw | 78dce01ca36fc34ee1965fa10f933c4bd26305546157b701d023b42ab36dae57 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/snapshots/first-leaf-public-v1.raw | 1b49af6e447b58f076ef84ff72380e0b91ca70a602833f8f15ceb04782b8373c |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/source-contract-inputs-v1.json | 93a048420015392099387c83652b8e4123df48afa50529839ee88911a7b630d4 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/source-contract-receipt-v1.json | 69c5e969846ad4d01a394e24ed6e5a57feea13680f83a9eb2f47274b7955b931 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/source-contract-review-v1.md | c726beab1eff1c661acd5ddd5fc485303d0ca33650293d4e02d70dc285cf9f15 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/stabilize-first-leaf-v1.py | dd2f87999cc4cca49f0025ef82e76820faf7dda747dbf4829ad534fdaa00c271 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/stabilized-contract-v1.json | 994a53572db03e3804509488e0c38647aa18433cb7b06b87b1ebe692eeab574b |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/stabilized-event-v1-exit.json | 425ffef703a51d924b6b6d882ce5dd165f24b10a17c633ea99bf2a4b7af2dc6d |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/stabilized-event-v1.log | bb43456c0a3088de45718390570b5db818a409a3773c7d9da4cd5e0c287de9c7 |
| E:/ABRL/worktrees/research-online-book/BanditRLProof/OnlineSquareMinimum.lean | 7bbfb2538dcdaed8c208571c248723d89ed8980e5e899339aa4c3b48a55c3210 |
| E:/ABRL/worktrees/research-online-book/Tests/OnlineSquareMinimumCanary.lean | 275e4c80fd8c8769293d810cc4e94ecc67d64f9f9c0f272f3e6c1340279ee881 |
| E:/ABRL/worktrees/research-online-book/runs/online-square-minimum-20261008/BODY-review-inputs-v1.json | 7676a466b671c23da49c0d30245edbc71100a98b11bcd38939eb16a89aa9d932 |
