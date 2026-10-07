# FTL state: distinct FINAL source/reader review

Verdict: **accepted-with-explicit-delta**, bounded package recommendation only. Actor `/root/source_reviewer`; requested GPT-6 Astra / medium, runtime unverified. Prior CONTRACT/BODY/presentation-scope history is disclosed; not blind, human or external review.

All 785 current fixed raw rows match. Independently resolved 157 CONTRACT, 441 BODY and 19 scope inputs, plus all 161/444/21 receipt rows: only the approved preimplementation scanner path resolves to its exact immutable snapshot. No silent update of old reviewed bytes. Current scanner and configuration are separately bound.

No blocking mathematical, metadata or reader repair found. Original R1–R8 are discharged below without renumbering or replacing their text. This decision does not perform native acceptance, PR delivery, merge or deployment and does not complete Chapter1/2 or the whole Goal.

## Mathematical scope and seven-slot checks
The complete Mean/FTLState/canary contents remain identical to the accepted BODY byte bindings. All nineteen target seven-slot analyses and actual body findings are reproduced below. Nine new production proofs and three definitions establish two source subobligations; six canaries are validation, not six printed results. All-real algebra is wider than source-admissible interval initialization. The half-only quarter and existing rates are not extended to arbitrary initial values. No loss/state/argmin/regret oracle is added.

### N01 — BanditRL.OnlineLearning.empiricalMean_decomposition
Verdict: accepted-with-explicit-delta. Finite sums expand into a quadratic; n*mean=sum obtained from n>0. Ring algebra gives exact residual.
- **objects**: Real empirical mean and squared prefix loss
- **quantifiers**: Every real stream, positive n, real u
- **assumptions**: n>0; no interval premise
- **conclusion**: Exact loss decomposition around mean
- **constants_indices**: Residual n*(u-mean)^2; range n
- **information_order**: Hindsight prefix including all n observations
- **source_delta_boundary**: Algebraic producer generalizes interval source; not causal action

### N02 — BanditRL.OnlineLearning.empiricalMean_minimizes
Verdict: accepted-with-explicit-delta. Consumes actual decomposition and nonnegative n*square; desired minimization is not an assumption.
- **objects**: Same prefix squared losses
- **quantifiers**: Every stream, n>0, real comparator
- **assumptions**: Positive n only
- **conclusion**: Mean minimizes over all real comparators
- **constants_indices**: No additive error or rate
- **information_order**: Hindsight minimizer
- **source_delta_boundary**: Stronger ambient comparison; interval membership supplied separately

### N03 — BanditRL.OnlineLearning.empiricalMean_mem
Verdict: accepted-with-explicit-delta. Positive real denominator, termwise nonnegative sum and sum<=n produce closed interval membership.
- **objects**: Real empirical mean
- **quantifiers**: Every stream and positive n
- **assumptions**: All i<n labels in closed [0,1]
- **conclusion**: Mean belongs to closed [0,1]
- **constants_indices**: Both endpoints admitted; n=0 excluded
- **information_order**: Only observed prefix needed
- **source_delta_boundary**: Source feasibility producer, not a global stream restriction

### N04 — BanditRL.OnlineLearning.empiricalMean_unique
Verdict: accepted-with-explicit-delta. Positive n and loss comparison force the residual square to zero; no hidden uniqueness oracle.
- **objects**: Mean and arbitrary real u
- **quantifiers**: Every stream,n>0,u
- **assumptions**: Loss(u)<=loss(mean)
- **conclusion**: u=mean
- **constants_indices**: Positive n essential for uniqueness
- **information_order**: Hindsight prefix
- **source_delta_boundary**: Uniqueness refinement, not extra source assumption

### N05 — BanditRL.OnlineLearning.empiricalMean_succ
Verdict: accepted-with-explicit-delta. Splits t=0 and otherwise proves both denominators nonzero; sum_range_succ, casts, field_simp and ring produce recurrence.
- **objects**: Real prefix means
- **quantifiers**: Every real stream and natural t
- **assumptions**: None
- **conclusion**: Exact successor update
- **constants_indices**: Denominator real t+1>0; includes t=0
- **information_order**: Uses prefix mean and current y(t)
- **source_delta_boundary**: All-real all-time recurrence; empty mean is 0, not arbitrary initial

### N06 — BanditRL.OnlineLearning.ftlPredict_prefix
Verdict: accepted-with-explicit-delta. Unfolds predictor/mean and proves finite sum equality from strict-prefix hypothesis. No current or future sample is needed.
- **objects**: ftlPredict for two streams
- **quantifiers**: Every initial,y,z,t
- **assumptions**: Equal labels for every i<t; same initial
- **conclusion**: Equal predictions
- **constants_indices**: Includes t=0
- **information_order**: Strict past, no current/future dependence
- **source_delta_boundary**: Fixed exogenous initial; not a guarantee for future-dependent external parameter choice

### N07 — BanditRL.OnlineLearning.ftlPredict_mem
Verdict: accepted-with-explicit-delta. Splits initial branch; positive branch applies actual empiricalMean_mem. Source feasibility is derived.
- **objects**: ftlPredict interval membership
- **quantifiers**: Every initial,y,t
- **assumptions**: Initial in [0,1] and all i<t labels in [0,1]
- **conclusion**: Prediction feasible
- **constants_indices**: t=0 retains initial; positive t uses mean
- **information_order**: Strict past only
- **source_delta_boundary**: Source-admissible general initialization; no current label premise

### N08 — BanditRL.OnlineLearning.ftlPredict_half
Verdict: accepted-with-explicit-delta. Definitional equality with existing meanPredict at half initialization; no changed learner.
- **objects**: General predictor and old meanPredict
- **quantifiers**: Every real stream,t
- **assumptions**: Initial specialized to 1/2
- **conclusion**: Exact predictor equality
- **constants_indices**: All t including zero
- **information_order**: Same stream and time
- **source_delta_boundary**: Bridge to existing half-initial source theorem, not new regret rate

### N09 — BanditRL.OnlineLearning.ftlState_first
Verdict: accepted-with-explicit-delta. Unfolded first local update cancels initial over denominator one, producing actual pair (1,y0).
- **objects**: Whole recursive count/value state
- **quantifiers**: Every real initial and stream
- **assumptions**: None
- **conclusion**: State at 1=(1,y(0))
- **constants_indices**: First denominator 1 cancels initial
- **information_order**: One observed label
- **source_delta_boundary**: Arbitrary-real structural identity, not admissibility for outside initial

### N10 — BanditRL.OnlineLearning.ftlState_eq_predict
Verdict: accepted-with-explicit-delta. Nat induction establishes both count and value. First successor uses ftlState_first; later successor uses empiricalMean_succ after induction. No state identity premise.
- **objects**: Whole state and predictor
- **quantifiers**: Every real initial,stream,t
- **assumptions**: None
- **conclusion**: State=(t,ftlPredict initial y t)
- **constants_indices**: t=0=(0,initial)
- **information_order**: Actual recurrence must produce identity
- **source_delta_boundary**: Sufficient-statistic implementation theorem; no supplied state oracle

### N11 — BanditRL.OnlineLearning.ftlState_prefix
Verdict: accepted-with-explicit-delta. Rewrites both actual state identities and invokes predictor-prefix theorem; whole pair equality follows.
- **objects**: Two whole count/value states
- **quantifiers**: Every initial,y,z,t
- **assumptions**: Same strict prefix and same initial
- **conclusion**: Whole states equal
- **constants_indices**: Zero horizon included
- **information_order**: Strict past for count and value
- **source_delta_boundary**: Causal structural refinement, not only equality of displayed mean

### N12 — BanditRL.OnlineLearning.ftlState_mem
Verdict: accepted-with-explicit-delta. Rewrites actual state identity and invokes predictor feasibility with exactly initial and strict-past assumptions.
- **objects**: State value coordinate
- **quantifiers**: Every initial,stream,t
- **assumptions**: Feasible initial and strict-past labels
- **conclusion**: Second coordinate in [0,1]
- **constants_indices**: Count not constrained to interval; zero included
- **information_order**: No current/future label hypothesis
- **source_delta_boundary**: Source feasibility follows actual state identity

### N13 — BanditRL.OnlineLearning.ftlState_half
Verdict: accepted-with-explicit-delta. Rewrites actual pair identity and half predictor equality; whole same-trajectory specialization.
- **objects**: State and old half predictor
- **quantifiers**: Every stream,t
- **assumptions**: Initial=1/2
- **conclusion**: Whole state=(t,meanPredict y t)
- **constants_indices**: All times
- **information_order**: Same actual stream
- **source_delta_boundary**: Exact specialization, no general-initial quarter guarantee

### N14 — FTLStateProbe.initial_and_first
Verdict: accepted-with-explicit-delta. Zero states computed by rfl; first states invoke actual ftlState_first for both endpoint initializations.
- **objects**: Two endpoint initial states, constant-one stream
- **quantifiers**: Closed test proposition
- **assumptions**: Specified initial 0 and 1
- **conclusion**: Distinct zero states; same (1,1) first state
- **constants_indices**: Times 0 and 1
- **information_order**: First observation overwrites initial
- **source_delta_boundary**: Validation only; no new source theorem

### N15 — FTLStateProbe.varying_updates
Verdict: accepted-with-explicit-delta. Invokes actual state identity and computes the nonconstant finite sums giving means 1/2 and 2/3.
- **objects**: Probe stream 0,1,1,... and initial 3/4
- **quantifiers**: Closed test proposition
- **assumptions**: Specified data
- **conclusion**: States (2,1/2) and (3,2/3)
- **constants_indices**: Counts 2 and 3
- **information_order**: Initial is not an extra observation
- **source_delta_boundary**: Nonconstant validation of genuine running mean

### N16 — FTLStateProbe.current_target_after_prediction
Verdict: accepted-with-explicit-delta. Uses state-prefix theorem at time one, separately computes differing current targets and distinct time-two states.
- **objects**: Constant-zero and probe streams
- **quantifiers**: Closed test proposition
- **assumptions**: Same initial 0 and same prefix at t=1
- **conclusion**: Same prediction state before differing current target, unequal next states
- **constants_indices**: Times 1 and 2
- **information_order**: Current target acts only after prediction
- **source_delta_boundary**: Validation of causal order, not current-input invariance after update

### N17 — FTLStateProbe.feasibility_and_outside
Verdict: accepted-with-explicit-delta. Uses state feasibility for admissible initial one; computes initial two outside and uses first-state producer for updated zero.
- **objects**: Feasible and outside initial states
- **quantifiers**: Closed test proposition
- **assumptions**: Specified initial 1 or 2, probe labels
- **conclusion**: Feasible later value; outside value at zero; first updated value 0
- **constants_indices**: Initial 2 outside [0,1]
- **information_order**: First observation restores value in this fixture
- **source_delta_boundary**: Outside initialization is ambient validation, not source-admissible learner

### N18 — FTLStateProbe.half_state_regret
Verdict: accepted-with-explicit-delta. Rewrites actual half-state identity; computes regret 3/4 and invokes old meanPredict_regret_refined with actual interval evidence for the inequality.
- **objects**: Half state cumulative loss and final mean comparison
- **quantifiers**: Closed two-round test proposition
- **assumptions**: Specified probe and half initialization
- **conclusion**: Actual regret 3/4 and refined upper bound
- **constants_indices**: T=2; quarter plus later harmonic term
- **information_order**: Same trajectory and hindsight comparator
- **source_delta_boundary**: Must later invoke actual old refined producer; no general-initial rate

### N19 — FTLStateProbe.general_initial_not_quarter
Verdict: accepted-with-explicit-delta. Uses feasibility theorem at zero and computes first loss one>quarter, with an admissible initial and target.
- **objects**: Initial-one zero-label first-round loss
- **quantifiers**: Closed test proposition
- **assumptions**: Feasible initial 1 and label 0
- **conclusion**: First loss 1>1/4
- **constants_indices**: First round only
- **information_order**: Prediction before label
- **source_delta_boundary**: Source-admissible counterexample to extending half-only quarter bound

## Complete definitions

### ftlPredict
- **objects**: Real initial and stream to real prediction
- **quantifiers**: All real initial,y,natural t
- **assumptions**: None in definition
- **conclusion**: Initial at zero, empiricalMean at positive time
- **constants_indices**: No division by zero branch; empty mean distinct
- **information_order**: Only strict prefix on positive branch
- **source_delta_boundary**: All-real definition; interval source specialization later

### ftlMeanStep
- **objects**: Natural count/real value pair and real target
- **quantifiers**: All pairs and targets
- **assumptions**: None
- **conclusion**: Count+1 and value+(target-value)/(real count+1)
- **constants_indices**: Denominator strictly positive for natural count
- **information_order**: Only supplied state and current target
- **source_delta_boundary**: Ideal exact-real local update; not bit/time complexity

### ftlState
- **objects**: Recursive natural-time count/value state
- **quantifiers**: All initial,stream,t
- **assumptions**: None
- **conclusion**: Base (0,initial); successor applies local step to y(t)
- **constants_indices**: State time t corresponds to source prediction t+1
- **information_order**: Recursion consumes current target after existing prediction
- **source_delta_boundary**: Equation-style full definition requires raw/compiled validation, not naive := extraction

## Original R1–R8 current decisions

R1 — satisfied
Original requirement: Attribute arbitrary feasible initialization to printed p3 and the running-summary construction to p6; distinguish the p4/p5 half-initial theorem. Nine new proof declarations are not nine printed source results.
Evidence: Current source-card07 and every new note explicitly separate printed p3/PDF15 arbitrary initial, p6/PDF18 summary and p4–5/PDF16–17 half performance; nine declarations versus two source obligations stated.

R2 — satisfied
Original requirement: Show the complete predictor, local count/value step and recursive state definitions. Distinguish all-real algebraic extensions from source feasibility requiring initial and strict-past labels in [0,1].
Evidence: Current card07 displays full mean, predictor, local step, zero/successor recursion and pair identity; notes and actual definitions distinguish all-real algebra from initial/strict-past interval feasibility.

R3 — satisfied
Original requirement: Explain state(0)=(0,initial), empty empirical mean=0, and the first update cancelling initial. Preserve all-time successor identity with positive real denominator t+1 and all zero/one-time boundaries.
Evidence: Card07 and notes01/05/06 explicitly distinguish empty mean zero from prediction c, first cancellation and denominator t+1; actual N05/N09/N10 unchanged.

R4 — satisfied
Original requirement: Explain whole-state strict-prefix equality with the same fixed initial parameter; prediction precedes current-label update. Do not infer causality for an externally future-dependent choice of initial.
Evidence: Card07/notes02/07 fix c before observations and compare the same c; current target is processed after prediction. External future-dependent c explicitly excluded.

R5 — satisfied
Original requirement: Connect the actual state identity to existing empirical-mean decomposition, minimization, feasibility and uniqueness producers. Separate hindsight prefix argmins from causal predictions; no supplied argmin/state/regret oracle.
Evidence: Current card07 and central note describe actual decomposition/minimization/uniqueness and interval feasibility, distinguish hindsight leaders and causal predictors, and reject supplied state/argmin/regret certificates. Compiled VALUE checks remain exact.

R6 — satisfied
Original requirement: State exact half specialization and retain the half-only quarter bound. Explain all six validation fixtures, including changing means, current-target perturbation, outside-initial ambient test and feasible initial-one counterexample.
Evidence: Note09/half card and all six described canaries preserve same half trajectory, first quarter restriction, actual regret3/4, outside-initial2 ambient case and feasible initial1 loss1>quarter.

R7 — satisfied
Original requirement: Limit running-summary claims to mathematical noncomputable exact-real count/value state. No fixed-bit memory, executable implementation or runtime certificate. Validate complete formulas, current HTML and actual pixels at FINAL; preserve shared definitions and registry ownership.
Evidence: Current card07/full HTML state exact-real noncomputable count/value with growing count, no bit/time/executable certificate. Independently viewed 13 listed current panels; original-detail and exact pixel comparisons resolve initial apparent note08/09 clipping. Corrected catalog12 contains both clauses without neighboring theorem. No mobile/full-page/all31 independent pixel claim.

R8 — satisfied
Original requirement: Keep stages and counts explicit: four retained Mean proofs, nine planned new public proofs, three definitions and six validation proofs; no current BODY acceptance. Sixteen source items are not a proof total (null); W/V mapping, logarithmic lower-bound audit, eight main gaps and remaining chapters/appendices remain required. Distinguish inherited historical ledger pending labels from current decisions. For equation-style ftlState use complete raw-definition hashes and actual compiled definition identities/types/kernel evidence, not an unsupported native := header-extractor claim.
Evidence: Original requirement text retained as prior-stage context. Actual BODY and combined evidence now supplies nine proofs/three definitions/six tests; 16 source items/proof-total null and W/V/loglower remain open. Mean main gap resolved; seven other gaps remain unwaived. Recursive definition uses full raw pins and compiled induction identity, not native := fence. Native/PR future helpers bind registry-v5/pixel-review-v4 and require accepted FINAL; not executed.

## Presentation hook and evidence audit
The shared opt-in scanner validates canonical name/file/start/end, raw source SHA, LF block SHA, public definition kind and no skipped non-comment code; unlisted extraction stays unchanged. Six actual boundary tests cover complete extraction, stale pins, rehashed truncation, wrong file/name/start, duplicates/invalid metadata and missing-config defaults. Current actual scan returns the complete three-line ftlState without the next theorem. This is a source presentation hash, never a native recursive header fence. All 10,823 inherited registry IDs/URLs/hashes independently compare equal, and only the new ftlState hash differs among twelve new nodes; other eleven new hashes are unchanged. Registry-v5 raw hash matches the applicable overlay and actual site registry. The broader 100-definition proposal remains unapplied and separately auditable.

The successful current evidence is root 9093 jobs, Tests 9244 jobs (cache-inclusive), 472 harness tests with seven existing skips; 24 standard-only kernel names, 19 exact proposition identities/supported theorem guards and 16 actual VALUE pairs in 24 selected nodes/1979 references. Actual site-v4 is clean at source 808b2f7220a546d8cb8c5cacbb87135fc9552644; check reports 950 pages, 845 modules, 10835 declarations. Exact PR188 contributor covers eight production paths. Main-relative seven OTHER gaps remain failed-unwaived. Scoped whitespace exceptions remain explicit. No claim every module was rebuilt cleanly.

Partial registry-v4 failed and is not final evidence. Active v5 acceptance/publication/delivery helpers and v6 selection explicitly use registry-v5/site-v4/pixel-review-v4, exact base e2323f4ca649a30e420bde1a33dbf1d4997c4c9b and future fail-closed gates. No such actions have run. Historical preparation/key/guard/rfl/layout/no-goal/site-feature/overflow/scanner-import/relative-path failures remain preserved; no Lean weakening. Conservative BODY-stage pending text is historical presentation, not a claim that current successful gates did not occur.

## Actual pixel observations and observer correction
Independently viewed these 13 current panel images (not all 31 root-viewed images):
- `runs/online-ftl-state-20261007/source-card-07-v4.png`
- `runs/online-ftl-state-20261007/public-note-01-v4.png`
- `runs/online-ftl-state-20261007/public-note-06-v4.png`
- `runs/online-ftl-state-20261007/public-note-07-v4.png`
- `runs/online-ftl-state-20261007/public-note-08-v4.png`
- `runs/online-ftl-state-20261007/public-note-09-v4.png`
- `runs/online-ftl-state-20261007/module-new-declaration-06-v4.png`
- `runs/online-ftl-state-20261007/module-new-declaration-12-v4.png`
- `runs/online-ftl-state-20261007/reader-first-viewport-v4.png`
- `runs/online-ftl-state-20261007/algorithm-v4.png`
- `runs/online-ftl-state-20261007/worked-example-v4.png`
- `runs/online-ftl-state-20261007/source-card-05-v4.png`
- `runs/online-ftl-state-20261007/source-card-06-v4.png`

The source card shows the complete aligned recurrence and pair identity; catalog12 now excludes the following theorem. Current browser evidence reports zero formula scrollers and no MathJax errors/failed requests. I initially perceived left clipping in note08/09 tool renderings. That concern was investigated before decision: exact raw hashes match, original-detail note08 is complete, and read-only pixel comparison confirms identical complete title prefix, declaration common prefix and Mathematical-reading-label pixel blocks in note09 at the same coordinates. Dark text begins at x22; the raw images are 1030×2003. This reconciles an observer/tool-rendering concern without a source or capture repair. No unsupported clipping defect remains. These are desktop panel views, not mobile/fullpage/live certification.

## Remaining obligations
Source inventory sixteen is not a proof-leaf count (null). W/V domain mapping, logarithmic-unavoidability source/lower-bound audit, chapter reconciliation, seven other Chapter1 main gaps, Chapter2 and unenumerated Chapters3–16/necessary appendices remain required. Whole Goal active. All original R requirements and prior reports remain immutable.

## Raw reviewed inventory
| Path | SHA-256 |
|---|---|
| `docs/contracts/online-ftl-state-v1/.gitattributes` | `705fd4d6451a31d36b3df7de96f83f30ac976c9b4a6d1e51671d8e2f33e2d0da` |
| `docs/contracts/online-ftl-state-v1/chapter-one-source-ledger-draft-v1.json` | `7f75d965888db4902b76337ee707133932f9be3a8b320bfd83000e26c55b4a75` |
| `docs/contracts/online-ftl-state-v1/contract-manifest-v1.json` | `8eca33d36ca0fa2f397c3ab3017f23b30694fbae6b47d2eba4eb3b2b3194ed67` |
| `docs/contracts/online-ftl-state-v1/contract-v1.md` | `2a302163f381ad05f4c6222320a74b409baab6c4e9088ad0d4bdece645c0fff0` |
| `docs/contracts/online-ftl-state-v1/definition-fingerprints-v1.json` | `32e9dab5e180ac312ad2b0655ce1d7fb5d8a1d24758a5fb3c04bc07da80700a8` |
| `docs/contracts/online-ftl-state-v1/dependency-DAG-v1.json` | `a87fc0ab45833ee2381ac54638de08615477b63f5716ca1c1ba45c2d1c5f2ec6` |
| `docs/contracts/online-ftl-state-v1/existing-Mean-context-v1.txt` | `dc0862d6853a0a79643aea2df1bd1dd27d51eadcc69287043a2d5b0b710cbdd3` |
| `docs/contracts/online-ftl-state-v1/existing-Mean-headers-v1.json` | `1952c3250166c61642622b24b8d2e62849e12439648016053bcbb52a69d2c9e2` |
| `docs/contracts/online-ftl-state-v1/new-public-headers-v1.json` | `2ba8f23d41d0d123a4da3f7aa6afe91b33a84505efca2e002e4b9f0b4a526dbf` |
| `docs/contracts/online-ftl-state-v1/planned-canary-headers-v1.json` | `3732250ac6600a6466ce670e3b9270ba5f124a5bba8723b382c4b3725105fe26` |
| `docs/contracts/online-ftl-state-v1/production-definitions-v1.json` | `d1b7b4932bf705a03c2c3e366d710ffda82ca86c8fc30fd7f46c6cd453b2b6d9` |
| `docs/contracts/online-ftl-state-v1/proof-value-obligations-v1.json` | `ab1630e9c2e72bde19436b677dd690f730fe83c9198f5e3dd69cf898772d9126` |
| `docs/contracts/online-ftl-state-v1/semantic-signature-v1.json` | `7d1677e1a4762aad7ba21d262e0397bfc203109432dd5fda1d30060412708e35` |
| `docs/contracts/online-ftl-state-v1/source-card-v1.json` | `f49474b94bc82223de2b75b6d64f18bad63dd5bac649ea5c70e0a7f368912195` |
| `docs/contracts/online-ftl-state-v1/statement-fingerprints-v1.json` | `6754dc48c8946c3321c246975cb9bb1678c0526cea58dae4fc742835a8b01e2e` |
| `docs/contracts/online-ftl-state-v1/test-definition-v1.json` | `51750f1341610426ecbae2843cd89c850e5c041e5c0d52bdcbe3a248d6a5e76c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/.gitattributes` | `705fd4d6451a31d36b3df7de96f83f30ac976c9b4a6d1e51671d8e2f33e2d0da` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/00_context.md` | `2fec28aadcacfec31923d17746681189cb75f9f406b5c041751dabcb045013c4` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/10_upper_director-v1.md` | `b47869e78c00a8b5f495ca9247b434c3561ef630a5d5d8bce1a271d97c58d15c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/20_architect-v1.md` | `e55069db8eca97afe10aba77335a19aa70791060eb55d2a9b70fa14ad33f15c3` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/base-PR188-fresh-v1.json` | `c83c8ae7cb25a5ec44e579ce5e8b5c668641b4b79391d62792bbe813915b8003` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/blind-binding-audit-v1.json` | `a028a1b64c18b643ecf6952fad2dd42afb2af7172cdc072a819db7691d0bc66d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/blind-decoder-receipt-v1.json` | `74157d06f1127b7e9247e7cd0442a67bdf400ed80c7eef0616474f1ad892e98a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/blind-decoder-v1.md` | `6e492341b48999a64c278a05333eb837953a9f43f6e795a1a1bb2d259a61c190` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/blind-packet-v1.md` | `e9f390cd6b9bbae22cf1ba8c2ca9dc964fe1b4d8514ea033bbb550219ab705c8` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/blueprint-own-v1-exit.json` | `66b729264c978a4fe76216676d13831058b1cdc42dfe1c26b163d2b09b886b13` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/blueprint-own-v1.log` | `5308035eb9513306433f2a704bd674e028ec453314f745bd2d33841e1e5fc776` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/canonical-worktree-audit-v1.json` | `504a9aca96e98cb9603afb94f35e31a9942c73079361d67ada65c62077aa10a1` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/common_v1.py` | `da4526f70c84acd84f5890559a989958326c6d02329d958cfd69ca480f123a44` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/continue-contract-v2.py` | `c4cfb1feea9cd85cb2fd69bb694fd151778fb215e8dee43c97bfbb1ee026d7ee` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/contract-preparation-failure-v1.json` | `b53a8b796bb449c1c981a7341f9549c4809e022ce9b5fc6eb4bbf7e6f0c9d0e0` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/contract-schema-repair-v2.json` | `413c0da6ec2be6e6f945d7eb602085d1efa8636bd5a62e1b8013507c4b067fef` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/draft-event-v1-exit.json` | `2d350cdaeded6cca2e29656664d7f42b1fe4e02e34fa305b63d3e11ab515761a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/draft-event-v1.log` | `4e0039138b3ac3c25378c286181873cbed0dbcdc19dd0f7481aca7c36f58d2ec` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/draft-freeze-v1.json` | `af56062686b28e15383a81b0c6045d8d1d0d0b7993f28641d994e3eb1089b882` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/draft-metadata-repair-v2-exit.json` | `75d660af8e51244597bf4cfd68eed0d08643e6e6427496a3ff4722035f777b70` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/draft-metadata-repair-v2.log` | `8cbb56e48eedb0d9b3310b067d16f6453b907d1c18b889b7ffa66601238c697c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/existing-Mean-type-identities-v1-exit.json` | `5ff8a571a0c2cfe0b3c1a830308f2866c0160634cf8c0faa81f442aeb0438003` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/existing-Mean-type-identities-v1.log` | `e7135de220edb3dea3d1b96230bd891d13003da6ac76a3f50652b6c514387275` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/fresh-fetch-v1-exit.json` | `5b67f221646907663594871a6a2d7c4b3b623e12c216ce4a178698cef2329fc9` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/fresh-fetch-v1.log` | `cfa5e943863a3844ac95ab66cbedc89f812445e00d82601bf1e4e25fb24b1733` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/help-blueprint-refresh-v1-exit.json` | `a1cb809c36a6843eca39911b1e68d0250c4088f4a6a03296235d4226e261cbdb` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/help-blueprint-refresh-v1.log` | `9ed3b46491b1470d6a0bebb1277e25f5cd8e06ea10039b1397e66397aa63e65c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/help-frontier-refresh-v1-exit.json` | `f8cb75b6b643c4191954d8823508ca5908a4d9d8a3daf7c25097c7a545aa18e8` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/help-frontier-refresh-v1.log` | `bff73ff554907d7c5dd50b99f2491f5675e93afb29829e402ec383fb52fe3cdc` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/help-frontier-shadow-v1-exit.json` | `74da8f3eb10ace738bb5780c306d2df4d1c7ac74b89507a4c55428ea28c65715` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/help-frontier-shadow-v1.log` | `ad548f6e24b3214fbf5796c632caa24debbaa21c6622f7dab8abe268f521de7d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/help-lifecycle-event-v1-exit.json` | `e4c01f72490f73237a8e343badc088924b1debadb1c7321d1ece835713aa1150` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/help-lifecycle-event-v1.log` | `b1e8b438a9b725793b9888d206e98a971ace3df200ec90ed9cb63eab26b28507` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/help-list-lean-decls-v1-exit.json` | `42340bbf3d99da22670052240af8197738b9923bbc7270e67f78dc01c3b87325` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/help-list-lean-decls-v1.log` | `258218f16a12b1a530d85ae83e6c2449237af8a0a1153bb35de40245d665b131` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/help-list-mathlib-v1-exit.json` | `fc4565ed34b585e7aa37460df779a13dc3c41b1af34eb797035695f0960ad8ba` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/help-list-mathlib-v1.log` | `eedc3e9609fdc7a3bcf76443a33933477de80dcc4ec9906b64a691e29b207e9d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/help-list-papers-v1-exit.json` | `cc74d0d29612a60327dc393f569d1e87128ef54bc83363bc65bdd8502527c955` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/help-list-papers-v1.log` | `57fdd9fadca031cddeec9da9c4ba947cccb3b1b155129de3a81b72b0c811a696` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/help-list-weapons-v1-exit.json` | `83791cc7a16a31323f8b21f892343f9d17e70bf5c57093701d01bc544be39ea6` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/help-list-weapons-v1.log` | `529fdc45da8d53249b6cea7712803e68cc0251026c7a66d1a067ac6413c9617d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/help-memory-record-v1-exit.json` | `4e9341031a8fe1d892afe7d6472ca4bf5b34d079a600cad062350cd0177c7ebc` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/help-memory-record-v1.log` | `89e8a7b2bb8d4fd593f0705289ca3c4c63015e48d0e8c9cbe5b71cf2c7cc44f4` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/help-new-task-v1-exit.json` | `4b4fa3596b295c5c7f4c36a6d87c1ce0126e5d0c034e99f7a8a3b9a2b69c4346` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/help-new-task-v1.log` | `25eb9342c3094bee57187630bd149d2c522fc9f7ac7e65bebe5c198eba60ed99` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/help-retrieval-record-v1-exit.json` | `5b670f9d8d64c39d8c91a5db77c767ae1b06774c5e0d42cb23b9952b5ff0739d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/help-retrieval-record-v1.log` | `73ac93f120215511ff0370d7ce100a9d0e83598ad882bcc5773cd1dc889b5321` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/help-root-v1-exit.json` | `ef4a3e842fb9fe51a2e28919a8d03c6452946900b6421ff78de1462abcc3f2eb` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/help-root-v1.log` | `daacf23e36eec4898dce3b3de02a07b71fb0f80f08e33e8dfe00722e7572970c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/help-safe-verify-v1-exit.json` | `6023f69536a78e220f320cc341451c6739a49a6b407891e4d5656c47e7cc5d39` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/help-safe-verify-v1.log` | `1773541c625f225e5a9abc61985c3ad19e871cf31aa0cf89cc440b3d8398862c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/help-search-memory-v1-exit.json` | `0b91dfdef90dc9df14536fb84a799bc576d28a743653db19f8a13e611a0b3842` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/help-search-memory-v1.log` | `b2f23faf2d0ee17c305335680ebdb2b83ca61999d18021e355d22587d712b79c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/help-statement-fence-v1-exit.json` | `1c2eb1b8d3273ad75abc75206521adb1dd04ff296b28e36c0f76d7ed51def5ff` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/help-statement-fence-v1.log` | `4f4fca9dfaac7a7c3de8025d3d0f7c4ba58d1f4b33feb08d19e12229942dba75` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/help-trial-log-v1-exit.json` | `c7ce18fe023e2d492982e29da685fd6a393dd4061d8fdb4c04b789e8aaf9704d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/help-trial-log-v1.log` | `ea7bd7e4d64216b46f554a90e02a3d58b4fcbe72766c2f7b316b656b94d19b32` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/initialize-v1.py` | `2df30014ed297b7d1458388e89fb62089177e7a0b0c5bd0d948544b7365da5c3` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/leaves/existing-Mean-type-identities-v1.lean` | `45aa9604c2be96a440dbc96a4d3439fc18fccf372e962bf48746ee04f8ba1fc2` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/leaves/neutral-closed-props-v1.lean` | `14ddb5b9a007da6a4a0aa24009f9b100b5651c1de2b76e133089ab958cd6c76f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/memory_digest.md` | `2dd3d8faf28260e6d235eabd157da9fa051337c8c2498cfeea6d77248a6ab565` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/neutral-closed-props-v1-exit.json` | `38b36945ed217ba497e3e325f5ddd578d543a463615e539d37d3779ee43a6c79` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/neutral-closed-props-v1.log` | `5ed416afd26e9928e5afbf46ad89f8c364f2caa7f6a0dcb32446557d75b52447` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/neutral-map-v1.json` | `38a8142ba1e24bdff8aa4ddee11a37dc30f2e94a7c674296252d47cea4906314` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/neutral-type-bindings-v1.json` | `1f0f900455a60dbb295993b02a53e0c1a85e7a2a200d494119b0ff2ea9fc2558` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/new-task-v1-exit.json` | `d8b80cf3e1fe36279aa36e8de04720686d029cc0b73f14bdd9219a6d69ff9835` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/new-task-v1.log` | `2a2229960220db21a215fc12a59c8ac75321f93fb7c890a7051d6df46df13ab1` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/owned-commit-paths-v1.json` | `ce0191651ed5612ed0291f0ff64dcfbc23f0f77725bb462f3824bf54724fe119` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/paper-boundary-v1.json` | `4b85e7690280863c2a4b3eaab46118453ac1aec397ef8563c47f7567bd57b4f5` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/prepare-contract-v1.py` | `658ec0105783f4b0a44eaccbeed6e8e04e594aa4f60749cdf4ee0d2ca18f27f6` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/prepare-source-contract-review-v1.py` | `d103a7e243c4bc861e9f67790bcf9028cfd42c9951e509fcfb836989c55a50dd` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/proof-obligations-draft-v1.json` | `aab7f1a9fc9f753c4788562c814f58a5337ca22c56bd97f2b9834f64ba70456a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/repair-contract-preparation-v2.py` | `6a29e7cfce04bf60b7564ff3265582984a7dc8217e4b8e1e5748e92b4b151867` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/retrieval-actual-Mean-FTL-v1-exit.json` | `1ca1299dc31dca814ed5bd612cc9591a9655269998e7d329660def0b5326a167` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/retrieval-actual-Mean-FTL-v1.log` | `61b3a92e137024b6e56d4aadd44da75806cb53ffbac498b7f3a359af52f7ac02` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/retrieval-actual-sum-v1-exit.json` | `0f583c14d077405e9de9c1a62b18300615c1c4f33f6ce6b5f1e3d23b4ee28355` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/retrieval-actual-sum-v1.log` | `1b11728857da006104a5d941cecd428c4ee30f9a6adfb525e60f94c1cec75de1` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/retrieval-decision-v1.json` | `351f0ecb55d4c68023837f666d366fdf40675e2d84f65e1918dc70d061f62588` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/retrieval-mathlib-v1-exit.json` | `90b922c872951fd3ed458724fd40dcd61a0c3aa06f0651c1936c17169d4f0f6a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/retrieval-mathlib-v1.log` | `884fab88619a3d1adcafe89eecddd2d98f4be5c6fa61262862134dde9e51d225` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/retrieval-memory-state-v1-exit.json` | `a7e7d7168ec8c32363e1618bb64ad28a0a28756f075be9ef1ae704e78e3f1ee9` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/retrieval-memory-state-v1.log` | `11999fd2b01349cb48f47e2291dcbda3daeae233e4d63611c1bad6c59a86faae` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/retrieval-named-mean-v1-exit.json` | `6d1332d28dec2c0ae87d38c4682d8b188e7f84573a00c0ee351abda590192512` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/retrieval-named-mean-v1.log` | `ecc7e02baea9b6a4e149d4047b11c79aa32c3d1a251f22fc734c655ec3e79f9f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/retrieval-named-predict-v1-exit.json` | `104b17fbb75178695b6e27738f107a51e4888a43cb98990936b0174ad0aa4ceb` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/retrieval-named-predict-v1.log` | `3955bf16a135d1b8ad941101686854de726b99d0d032a5ed44d76021872e5100` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/retrieval-named-state-v1-exit.json` | `96e9a03426bd2ab1d1a4bc6a9eec99d86afff34bb73efafd2564f444b165493f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/retrieval-named-state-v1.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/retrieval-papers-v1-exit.json` | `92b62197bf55b3cd506b18a772391472df90dae0e8a4bba2dc73cd2b1b1543ce` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/retrieval-papers-v1.log` | `9acd333996a893a7b5ccad3e674ece26ef05c8b737e7816b33043b121583a619` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/retrieval-weapons-v1-exit.json` | `3fc9d0b951f31fa5a95457205f2de49349d3136c57b2afaa885ba3b217b88745` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/retrieval-weapons-v1.log` | `a6e4b78de1a30fcf5a0ee66b868eb3ac1bfa68d2250c713f61e690ae064f7ef6` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/snapshots/BanditRLProof--OnlineLearningAsymptotic.lean.raw` | `4d704d07b9616ca48a1ee56d47af7f5f8ca9e3797d2a9b47d373038a25d79d59` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/snapshots/BanditRLProof--OnlineLearningFoundations.lean.raw` | `e23ebdca2f7ce21a16173c93390fd24d16ba36e403c9d084233f7480e75408b8` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/snapshots/BanditRLProof--OnlineLearningFTL.lean.raw` | `8c3574c657f08e0c5291f0689105f9459e92187502f092f4d36d848e52ab4219` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/snapshots/BanditRLProof--OnlineLearningHistory.lean.raw` | `3412177ab7dd0ac0e350d8fde7f91e61640d55743d1f17d15c62a65dd4492fc7` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/snapshots/BanditRLProof--OnlineLearningIID.lean.raw` | `92af24e6a2c2b1054503492b2bad97cd17ccea2217439f6d2f8a7bedb0de3d5e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/snapshots/BanditRLProof--OnlineLearningInformation.lean.raw` | `72bef017a43c293d0d3c449707e4a0e058f4655c2483b54c3120d7b41c98135a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/snapshots/BanditRLProof--OnlineLearningMean.lean.raw` | `d65b3e5d5d2e33a0fd94722f1d7d9a09819c963c693e28bf854fae00f5280aa1` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/snapshots/BanditRLProof--OnlineLearningRegret.lean.raw` | `231eda88cb1c45bf3bc9209bfbdd696fbfbe8a64b00303113a23cbc4dff3ca5b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/snapshots/BanditRLProof--OnlineLearningStochastic.lean.raw` | `0242481022883958afef677654fadd3f6e37b381f3fe463e3605f3eb0542f2bd` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/snapshots/BanditRLProof.lean.raw` | `7cdb1969bad2f7b42cfd7a25f6d15747d0d49178dadc244b70ab1f9b8c92c5ad` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/snapshots/CONTRACT-review-conversion-windows--ONLINE-FTL-STATE-20261007.md.raw` | `2a302163f381ad05f4c6222320a74b409baab6c4e9088ad0d4bdece645c0fff0` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/snapshots/CONTRACT-review-proof-blueprints--ONLINE-FTL-STATE-20261007.md.raw` | `8d120e57db47a419d1a0c2a85fe13c1dff82dfdbd6f25fe33ed0b4144f4866ac` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/snapshots/CONTRACT-review-proof-obligations--ONLINE-FTL-STATE-20261007.md.raw` | `2a302163f381ad05f4c6222320a74b409baab6c4e9088ad0d4bdece645c0fff0` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/snapshots/CONTRACT-review-research-wiki--retrieval-index--ONLINE-FTL-STATE-20261007.md.raw` | `2a302163f381ad05f4c6222320a74b409baab6c4e9088ad0d4bdece645c0fff0` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/snapshots/CONTRACT-review-tasks--ONLINE-FTL-STATE-20261007.md.raw` | `2a302163f381ad05f4c6222320a74b409baab6c4e9088ad0d4bdece645c0fff0` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/snapshots/docs--contracts--online-book-v1--coverage.json.raw` | `fd7580c2d0ec040352317d3c53dc583a6b9b75a68b4026ebf3b38f7010a98f1e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/snapshots/docs--contracts--online-book-v1--source-inventory.json.raw` | `a2a504cf40d73f9c5e36f00fc1ef3b949ccaf5a558ab603c1c2a86007f30efa7` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/snapshots/lake-manifest.json.raw` | `87c3e616f86244550ef39e7415186b11c1d4cf4bef20173196a619d9d4d48f48` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/snapshots/lakefile.lean.raw` | `0164f3b5b5bdcbb237ab15ae8b44da83e183f4b97d5f3832aa4a57f27dc69d45` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/snapshots/lean-toolchain.raw` | `b15a57f8ea4c890197465ce1156667ae13d9ed4ab8a9f263a920bf010d967d82` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/snapshots/MANIFEST.md.raw` | `f5d06f1fdcb68233153c5b0a5a61d58c1de5d48b97541a40ef56d44b83af2dfd` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/snapshots/native-scaffold-conversion-windows--ONLINE-FTL-STATE-20261007.md` | `94d32b4dcfabd5a7420ce416fdf17cb787649f4e72772d0cf1b6218c136e2b19` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/snapshots/native-scaffold-proof-obligations--ONLINE-FTL-STATE-20261007.md` | `17de0b07e3308b470789df5074877fb717c49ef6f6bd46fb44e016e09608826c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/snapshots/native-scaffold-tasks--ONLINE-FTL-STATE-20261007.md` | `ef4ec608fd7fe12dce160808024e6deb6d5cdd11e755e26d174931b7017d234f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/snapshots/runs--active_frontier.json.raw` | `567e5873aa2549a83f2820d758069213808da822a93087129877385a1addf7c3` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/snapshots/runs--lifecycle_memory.jsonl.raw` | `94be3ceb994768191ceb6a7545935c8d16c044511dfe8c4482e2fde493eaa5f8` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/snapshots/runs--lifecycle_sessions.jsonl.raw` | `2d381e7d4b33ed27d2d917f5b675d419ef4c73ef1392cd479820ffc81b05da5d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/snapshots/runs--online-ftl-sharp-20261007--accepted-decision-v1.json.raw` | `53f0226ca0a70094be3470a70a59c220fd60d6080aff039ac25aea1a1fc31ad0` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/snapshots/runs--online-ftl-sharp-20261007--delivery-obligations-overlay-v1.json.raw` | `83dec26a4df590d5b3176347ff6186140ba5702aefb768a09b220f886bb36a37` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/snapshots/runs--online-ftl-sharp-20261007--final-metadata-repair-receipt-v2.json.raw` | `d4c1bf8c2adc04e70c970263bc59a153f3858b8e4ec4d910392f386b6667d71c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/snapshots/runs--trials.jsonl.raw` | `1c79100065c3f6f5572feb8965661404587946bfa6eac77c02495e25d5218eaf` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/snapshots/Tests--OnlineLearningChapterOneCanary.lean.raw` | `9700f465791ab34e765c6aaf5c8891bcd33a9c5c141d61aa3d0b6a648648368b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/snapshots/Tests--OnlineLearningFoundationsCanary.lean.raw` | `a8f625750c9b0f395b8c49cc2a03eb681ba5d7ada7f5373c6052334c09397ecc` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/snapshots/Tests--OnlineLearningFTLSharpCanary.lean.raw` | `b3f56ed77c2578b60a3f8fb509aaac85f4419b38aa7d0cdabbf9f311fd0559d7` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/snapshots/Tests.lean.raw` | `27dd2cd3a6123f77eafe7cb1d213db94e0b7c56728cc14a44f2de7d7d0d74a9f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/snapshots/website--content--chapters.json.raw` | `9d334c8fe46d0527e9b0a1f1a8ee2672d0259cae36a0798e9f95e8f000ad764e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/snapshots/website--content--highlights.json.raw` | `00da906e499118724ef3bedf59e1376b7522cc537688358cc47b7143fcb6ee0e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/snapshots/website--content--readings.json.raw` | `c7c08e7e14ebe546467394874de0de222c3097ab5dd6d9cec883ccc8c8b7bb07` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/source-contract-packet-v1.md` | `a4ef3dda8370dcd60a48d7899ee98a61ae248d41be243d9f7dcf4814b9157b5b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/source-pdf15-v1.png` | `42bb911c94638c3e96bed6b043eb9f2de8d9dc6c226dd36e5c43d42896d02259` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/source-pdf15-v1.txt` | `037b6d907a868c339b881162333f6e56352cbebf285902eb6ed628ff4f8bd947` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/source-pdf16-v1.png` | `1cdaa7b80dc113b8083930eb1dcf245688aa921bfe112021d070610f8cab3eb8` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/source-pdf16-v1.txt` | `b8fe01f6c31bf15cfb67ea948a832f97e2c77f9e1f569a36fd9fa72e831796ee` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/source-pdf17-v1.png` | `8515e968b52d0d84928817aa489e890b5fa9a02207aa95dd3da28c9252eacff2` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/source-pdf17-v1.txt` | `164b4ca2261475aeadaf633ce67afbf8a221f612b8f4db801c36ea75081263e8` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/source-pdf18-v1.png` | `45588776738cd2b9f18f3dd6cbbb05535cd203a9c36351edcd2a310262874664` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/source-pdf18-v1.txt` | `bec2bd23e52551c2f353a7dec52c99582185e812f99a24f55983f209007eb484` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/source-pixel-review-v1.json` | `ad87743a1ab773fda78e020a3f5bfc8dbc4e85b49e75cd2c4b6af82bcbf99cfd` |
| `../research-online-ogd/tmp/pdfs/orabona-v10.pdf` | `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17` |
| `docs/contracts/online-ftl-state-v1/stabilized-native-proof-headers-v1.json` | `63de2ba68ab32121c1b05ef521d8b031c79c12bf0ceca639b156528ab2129f78` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/30_lower-ready-leaf-v1.md` | `7f2eeca7e8e0419e2235fb14b4ff57cd90ae2b34da25e3ce09d4e95efccc3764` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/all-axioms-v1-exit.json` | `f7706f8d8a684b8217438717e2b88d974ebd452aac8c5990df3e398d76d7e4ff` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/all-axioms-v1.log` | `641c18786fb9e7df982997792b83e89cba9b5e3281f39d726b2ecc18bb788fd7` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/all-exact-types-v1-exit.json` | `2e0f5f527dd709990d704fd50076ff032fdd422316d127a6a05fb13000b7e225` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/all-exact-types-v1.log` | `7c7b05458d4844bdbcba133cf3ddc095bbe9f787b89293842e63bba0e9970a32` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/all-exact-types-v2-exit.json` | `36b07dd0e0f24b12d5942119b8c579215bf02397565af99a6570833c2223c26e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/all-exact-types-v2.log` | `5c5921b704f66d721f5c4927a3bf135a424d8c1e547ed3b59ca69c15d322a700` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/all-public-types-v1-exit.json` | `a6af2e98df0c78832c888f251281ddbcf2ed839457f128f53e93486f2889c95f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/all-public-types-v1.log` | `731ebb7634d280c055e055db04683bff8d616182fd0c17f0e670f9311267eb00` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/blueprint-BODY-v1-exit.json` | `55fbe4a5e1999ad5b7086aac616c295baf5052faaa073fe164e71319e5aa05ff` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/blueprint-BODY-v1.log` | `5308035eb9513306433f2a704bd674e028ec453314f745bd2d33841e1e5fc776` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/body-bindings-v1.json` | `8eddf9da0732ff998b600705621345221ceb35c75a9159831c2bfb329c372ff4` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/body-review-packet-v1.md` | `6340c46b3cedf8549e8cb8111b3b6e94d3a98006d2e271286b9da980a6df1c6f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/canaries-compiled-v1.json` | `01572ca11299f6e79fcaa29d6952720e0edfff6f3df082e9c41b6fd691a02206` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/canaries-trial-v1-exit.json` | `b6079ad54e69a60ea8a7bb38e8be04779d00e7df79578ed9966724f5185c0e61` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/canaries-trial-v1.log` | `bb31d52ed584e4f94c225cb1cbab06f0e0d65a726a4af67efd3ceb709317fc18` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/candidate-event-v1-exit.json` | `1edf40026f81dc96016f9320f4a77f483e613ab9caf8fa0e7f665b3121ac6d42` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/candidate-event-v1.log` | `a753598ccea2506e4fc6352b3c7b80346399a7589c6be13541fa689c07adefa3` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/check-bodies-v1.py` | `cfe548f83575f2f0e0bc6c692c7a1d2d7152fe8eb47d47e2d3ed79445aa43651` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/compiled-value-graph-v1-exit.json` | `c5607940fd9f23ebe093ad1a2167aa4042054d51a6aa2f2a4617c66aa3bcec10` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/compiled-value-graph-v1.json` | `48e77d18039fcee716421d2e90428ebd7b1747d5ef8d1dca38afdf76939f2a7b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/compiled-value-graph-v1.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/compiled-worker-trial-v1-exit.json` | `5ed11c33ff75208b01decf2951c1f4e960bbab6e35b63da36ea36e755d380631` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/compiled-worker-trial-v1.log` | `0c63f838328e0345c24fb6c16736279b26d879fd04982da3801398df64264ada` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/continue-body-checks-v2.py` | `7fe13480ce4112c733594be1c2531b82e9a644fb654e54311617c95276660a5a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/continue-state-v3.py` | `97bb4d89dd30da0f5cad6a40d374164abc50c58c32c63314cb8eb11929c8b5ed` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/continue-state-v4.py` | `9e1721963918d7e3d1d2794d5b9658a2d7d24972012081f6c3555e945989639e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/definition-layout-failure-repair-v4.json` | `b1deea1c9ab35eeeac2b5f3eb8a1d0d6227f3821c74241cd653785083f4434af` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/exact-type-verification-repair-v2.json` | `cac5da4757aa167a4e54adeb9cdbc1316271dbab1c13a5f73c9b12bc11e1fa34` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/fence-ftlPredict_half-v1-exit.json` | `cf509042806859f037f655285cba0ab46946482cb2665e042301e418df666102` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/fence-ftlPredict_half-v1.log` | `df4dc7a20970b5ae95bc5f835df06a1e004e5da13b8ae23cbf951f8be455e815` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/fence-ftlPredict_mem-v1-exit.json` | `b47ecbbc4b54c7e6cd0fc5b153117ad7829209e0cd68cc0c802a0262a3ed3b02` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/fence-ftlPredict_mem-v1.log` | `3c083239459a8bec2a355204d943f7ab82576a21634877c83a705be08ba3f18c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/fence-ftlPredict_prefix-v1-exit.json` | `86a6d40d65e5554966f3b35c04161484906b15d5d94bb002e5b745669e6fefa1` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/fence-ftlPredict_prefix-v1.log` | `72a64752e6e5db6ad2b746adafffd172e7f56f54da3e7a8f031eeb9f3dd2e205` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/fence-ftlPredict_prefix-v2-exit.json` | `fdcc35914bdc95b92da3fa650da3b10365116cf013c9e62b93fa8aad84a663c7` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/fence-ftlPredict_prefix-v2.log` | `5d737caecd45b7a21e278fc3a0738422c0c26790a66883e8b5acac2facb772ec` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/fence-ftlState_eq_predict-v1-exit.json` | `5b7baceac1e600d123feb4f6a234832b7a974445fb49766236f745838f2eb2d5` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/fence-ftlState_eq_predict-v1.log` | `0a3ad06dae9425031dfcd221615f60e4204fb7997e959346720f4ef25c92a555` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/fence-ftlState_first-v1-exit.json` | `331ff5b119b0b8d7e60d30f59e33744840339976beb5eae68407a8e1ba0a7d4c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/fence-ftlState_first-v1.log` | `6c2d12f6f0367fbc472397c21e5266b6e09c78cb9875bd09582d19e86aff8fcf` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/fence-ftlState_half-v1-exit.json` | `5e1b35eecf586c7c55d5530cb0452649b0477a80b913631827c885901d01ec6c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/fence-ftlState_half-v1.log` | `d7dd022144cce45faac22b4d9e6d62612688e1d11e764b8dd1b9c5c834300be9` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/fence-ftlState_mem-v1-exit.json` | `3fb010c087a9def24e1c303209c95304fc838bbf979279e8e77b2611c184cb58` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/fence-ftlState_mem-v1.log` | `cf8a13346ecf742e7bbd869cd22b3891e09e685f63ba6fa6988f5515ea95b80b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/fence-ftlState_prefix-v1-exit.json` | `818bec4645a295b58aa54afe9f66b273f9aadd08bcc21081ee3e8e0adbbd5b5f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/fence-ftlState_prefix-v1.log` | `0f16cad4a28e1efd7a7e9fcb5d3ccd8b062a2fe386df569b595e2b057b145b41` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/focused-canaries-v1-exit.json` | `9fe57ff5b5cf9020f9fb38d6403ca62ffc86950b0928355b7777f870e78fd1cb` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/focused-canaries-v1.log` | `37585ac64862f834ce8c50766d71bbfb7607b2f94067a9867e3b6fba6c7801e0` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/focused-ftlPredict_half-v1-exit.json` | `c1eb0c3fa3f848524d1f46de7aa92a4f08d9602e50461c1b45d0066e556df85b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/focused-ftlPredict_half-v1.log` | `e8fc27f7dcbbfff46ad21bf1f5fcf5f410852bb08dc99a2fd0658bd22a8f5d38` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/focused-ftlPredict_mem-v1-exit.json` | `7a367175cb31ca22c8f9035764c300863e350ec8756768bf96ab1df902cad688` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/focused-ftlPredict_mem-v1.log` | `917738e4d6b21307edc4b114c3b4e4b8d26ed7d649be2fa13b9947b118d8bbf0` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/focused-ftlPredict_prefix-v1-exit.json` | `c95f719442de924869124b742f7285fc87ddf4c74928b793d25340759b155f2f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/focused-ftlPredict_prefix-v1.log` | `4a01efb573b5c7474653a92d64e1efeba4b7754a0d181840d3950b66c21a4f0d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/focused-ftlState_eq_predict-v1-exit.json` | `54a067ce1448a3bda60fe4d4689a9723f971ba84c3e922481a7fc8cd48720752` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/focused-ftlState_eq_predict-v1.log` | `5bd54845cb7663b5ea304ea85f29de3409e7a1b5d10727cc26c7c355f7d07524` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/focused-ftlState_first-v1-exit.json` | `f19b274bd22bac4357a44f45d01e380688e21b7d85f3c52600f7e6eff9ec0f83` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/focused-ftlState_first-v1.log` | `5bd54845cb7663b5ea304ea85f29de3409e7a1b5d10727cc26c7c355f7d07524` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/focused-ftlState_half-v1-exit.json` | `2b9c3f80505c01364bd13213a91b231964a4c8add483b27584abc35f4172a2ce` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/focused-ftlState_half-v1.log` | `372114d23d2875c16f6cacf8ebdf67c085c532b8fa10bc1ba8a481a6dbcdedbe` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/focused-ftlState_mem-v1-exit.json` | `f9384cf952349d1f765a823ab3d2aafa4aabb2fb5ee10cebbb8d28c28305f2a3` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/focused-ftlState_mem-v1.log` | `372114d23d2875c16f6cacf8ebdf67c085c532b8fa10bc1ba8a481a6dbcdedbe` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/focused-ftlState_prefix-v1-exit.json` | `aab8b9b53f681ae654d1013c83fe1340d324b7efdd79c531ae093da432025637` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/focused-ftlState_prefix-v1.log` | `4a01efb573b5c7474653a92d64e1efeba4b7754a0d181840d3950b66c21a4f0d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/focused-Mean-succ-v1-exit.json` | `c1011a0192ed6f70193fbcf7f6d36d3398a12ee984032d927b94ffff4d00235b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/focused-Mean-succ-v1.log` | `53dccdf94e796de1bfb4ac9b1b6d5f4c41553975df53294791383985889942eb` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/focused-state-definitions-v1-exit.json` | `804f81be5db00ebff26c864387b9048e2f57636ce8cd761f476539677eb9a638` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/focused-state-definitions-v1.log` | `837d381b5422a639da48d5c3814f4a1a3cacf61826aa3ba45385f21d3c36f754` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-fence-bindings-v1.json` | `fbf29c4a7b0cd41ee4acd829c40684d79024ae655a71f6f250af8e42137f18a1` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-fence-current_target_after_prediction-v1-exit.json` | `910221e23f3ef322960b583c464f43d898cf1f75b781f03d591adabd11716c3b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-fence-current_target_after_prediction-v1.log` | `6ead238cfce3e4b42bf7b8f74e938f284cb77bf5f203d3a83f364ec8a8257c6b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-fence-empiricalMean_decomposition-v1-exit.json` | `994ece73247eed52399e68984eef86f42530e72283b44f22fd64ef5d51c4c505` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-fence-empiricalMean_decomposition-v1.log` | `c6fdaee3479db9092186fcbfbfd7631e4fad949b84ea4e6cea4af2f2e75a502f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-fence-empiricalMean_mem-v1-exit.json` | `d36179fe4a43020ff946e3e0851ad06e587e51a3fd6c7ec93d937fdf065f7182` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-fence-empiricalMean_mem-v1.log` | `f15d921ba9a4d04781e5896e04da3c23a85f34ddc894988d4f0eadc452297f63` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-fence-empiricalMean_minimizes-v1-exit.json` | `a6637e6cacf6be5862263c6cd342eb787749881f1cac6620b9c18f7b717abc5b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-fence-empiricalMean_minimizes-v1.log` | `a6295a24eecb15fb21dac7a9d3c76f12538b0f47ba153cc7216ef02d8e2fcff3` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-fence-empiricalMean_succ-v1-exit.json` | `64bc118e1a25b816f70eab6b8fca3a9f60a4e4659e99e4ecb1e2e7702202b825` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-fence-empiricalMean_succ-v1.log` | `3cd330b75a552db13e6484a3fedcf6d3b7d4c044db89160021a50c9b7bce8116` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-fence-empiricalMean_unique-v1-exit.json` | `08b88402d34304236c545ad9e9ba0743bd86add8a59d185f807e9125186bcb30` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-fence-empiricalMean_unique-v1.log` | `30e8bddb623698df452c7c15f7b1f8eada6982bba101caa0ff4563a8b14ef09e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-fence-feasibility_and_outside-v1-exit.json` | `93450e00d6a7baa1cdef58999aeab133702046e087d757506fce85452e56b2d2` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-fence-feasibility_and_outside-v1.log` | `5da7ba6fb0ece6be89c06fc6de14ee81e512f71cd8aaf4e120a707c4720dbf1c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-fence-ftlPredict_half-v1-exit.json` | `68d96bff91d34daf98166e25b35f15e04654151df3a2353135ad53a74cdf02fb` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-fence-ftlPredict_half-v1.log` | `0cd60d6be47072989311f324be7f0204b1258f14ad151160d8f10131ba2d090c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-fence-ftlPredict_mem-v1-exit.json` | `9c3e8c7ec56259b6c4b0c6aa8e9fc7d64f04d198a1e01d368a4ed180b9a0441f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-fence-ftlPredict_mem-v1.log` | `d2fe3dddfd7bbbd98fa620aacb6a7ec1a0c32cdea8f3814fe142e3d5499fe9dd` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-fence-ftlPredict_prefix-v1-exit.json` | `3c57207987e1577f4cf7442fa6579b6ffb80469e3ea9a5f64c3e9a64d0be2bbb` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-fence-ftlPredict_prefix-v1.log` | `5495ca691822ed2b535e7e992b51c9d7511534b2e58d97b8b531d32b60011f97` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-fence-ftlState_eq_predict-v1-exit.json` | `7d80af95730dfaece47e5cd778f478fc9ab7ff8fcab923c4aa56947f233ed983` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-fence-ftlState_eq_predict-v1.log` | `51c3e61f085042c005ec28d083bc8ef95ee495035fe9713834c80bb43c63cbcf` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-fence-ftlState_first-v1-exit.json` | `67199d219accfcd767273739a76d3b7edaaf923e76cf79bb33c18e76e5746bae` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-fence-ftlState_first-v1.log` | `bf34c24b52bdcc789fa95052d82ff23a279a037313ad9576bc9f669379e80262` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-fence-ftlState_half-v1-exit.json` | `33c9846fa82abc9b5a21adc3af88135884a36dbfe067a41799517d885a48ad6c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-fence-ftlState_half-v1.log` | `ed86211b804973f5f9595bf9b747b4855d361f825e3bbd10693145d42ecfba07` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-fence-ftlState_mem-v1-exit.json` | `19cda5f3586f74b540a01f21c5c300d87c236a01aa7e7da25e7439dc0941e5b4` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-fence-ftlState_mem-v1.log` | `988ee6e45c3a556935c13d2e608bdebe7e2674e5406d40835cadb7fbecba9068` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-fence-ftlState_prefix-v1-exit.json` | `89b21d1470c340da6cfa98b1601d22dca91c5245ba938816ec7d7051bab494d4` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-fence-ftlState_prefix-v1.log` | `bf36503a9a5200fec2fc96ad142b298130e3a3e6ad3af87b3b343ed9da728404` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-fence-general_initial_not_quarter-v1-exit.json` | `f4df40eb3f6aa5177346a3cca657b69174b561c13b2f2e9805d6e16aa4f57463` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-fence-general_initial_not_quarter-v1.log` | `7e960dbf0f53c5ce7f78b7024f0fa2c29e03630b0c016ac4655cf4e3e8dd4dbd` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-fence-half_state_regret-v1-exit.json` | `24b57e879eaaec1b3bdc65524634fc537c21fcf66b3721b5b300c17e8caf293e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-fence-half_state_regret-v1.log` | `7fdb02eb49a0f328c84ab1ede21351ec8c5200d58689a7136cbffa14b2cce22a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-fence-initial_and_first-v1-exit.json` | `7d0c10fe611522c8eedd6a7e1413c11f4c357f20b62ff65a9b783188cb3828c9` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-fence-initial_and_first-v1.log` | `4d55aa2bc1fb12d41110b863c0b07d5cbd1dedf6416a0cf42225160ee0241981` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-fence-varying_updates-v1-exit.json` | `d1956afdb188517cbfe3b43732a707025dc9120abcf1f314676c203c854e4f83` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-fence-varying_updates-v1.log` | `871ceabe1b5d1eccb2369f9f714dc94baf9b160e34a2351212e0c66479f33acd` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-header-fences-v1/current_target_after_prediction.json` | `6ead238cfce3e4b42bf7b8f74e938f284cb77bf5f203d3a83f364ec8a8257c6b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-header-fences-v1/empiricalMean_decomposition.json` | `c6fdaee3479db9092186fcbfbfd7631e4fad949b84ea4e6cea4af2f2e75a502f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-header-fences-v1/empiricalMean_mem.json` | `f15d921ba9a4d04781e5896e04da3c23a85f34ddc894988d4f0eadc452297f63` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-header-fences-v1/empiricalMean_minimizes.json` | `a6295a24eecb15fb21dac7a9d3c76f12538b0f47ba153cc7216ef02d8e2fcff3` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-header-fences-v1/empiricalMean_succ.json` | `3cd330b75a552db13e6484a3fedcf6d3b7d4c044db89160021a50c9b7bce8116` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-header-fences-v1/empiricalMean_unique.json` | `30e8bddb623698df452c7c15f7b1f8eada6982bba101caa0ff4563a8b14ef09e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-header-fences-v1/feasibility_and_outside.json` | `5da7ba6fb0ece6be89c06fc6de14ee81e512f71cd8aaf4e120a707c4720dbf1c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-header-fences-v1/ftlPredict_half.json` | `0cd60d6be47072989311f324be7f0204b1258f14ad151160d8f10131ba2d090c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-header-fences-v1/ftlPredict_mem.json` | `d2fe3dddfd7bbbd98fa620aacb6a7ec1a0c32cdea8f3814fe142e3d5499fe9dd` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-header-fences-v1/ftlPredict_prefix.json` | `5495ca691822ed2b535e7e992b51c9d7511534b2e58d97b8b531d32b60011f97` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-header-fences-v1/ftlState_eq_predict.json` | `51c3e61f085042c005ec28d083bc8ef95ee495035fe9713834c80bb43c63cbcf` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-header-fences-v1/ftlState_first.json` | `bf34c24b52bdcc789fa95052d82ff23a279a037313ad9576bc9f669379e80262` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-header-fences-v1/ftlState_half.json` | `ed86211b804973f5f9595bf9b747b4855d361f825e3bbd10693145d42ecfba07` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-header-fences-v1/ftlState_mem.json` | `988ee6e45c3a556935c13d2e608bdebe7e2674e5406d40835cadb7fbecba9068` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-header-fences-v1/ftlState_prefix.json` | `bf36503a9a5200fec2fc96ad142b298130e3a3e6ad3af87b3b343ed9da728404` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-header-fences-v1/general_initial_not_quarter.json` | `7e960dbf0f53c5ce7f78b7024f0fa2c29e03630b0c016ac4655cf4e3e8dd4dbd` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-header-fences-v1/half_state_regret.json` | `7fdb02eb49a0f328c84ab1ede21351ec8c5200d58689a7136cbffa14b2cce22a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-header-fences-v1/initial_and_first.json` | `4d55aa2bc1fb12d41110b863c0b07d5cbd1dedf6416a0cf42225160ee0241981` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-header-fences-v1/varying_updates.json` | `871ceabe1b5d1eccb2369f9f714dc94baf9b160e34a2351212e0c66479f33acd` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-safe-current_target_after_prediction-v1-exit.json` | `e19decb70727ccfca093bcd4077a2492f44320b01c41cf9fd7a9a1f2098de53e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-safe-current_target_after_prediction-v1.log` | `f762f880af9bda94a373c17f7ee66fa9ca1d417bf42054e0e1045b704f833d27` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-safe-empiricalMean_decomposition-v1-exit.json` | `e6fef8bfb9d63ea4be098a7692be0ccfdaa4d8447689b3ffe9db3f6c0468597f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-safe-empiricalMean_decomposition-v1.log` | `5b0faed580c2e3195ac46b2951610f357c3ea42e2052710196da4400bc5f1e42` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-safe-empiricalMean_mem-v1-exit.json` | `e42c40d77119e55b1723da5592bb6387d3a8517da239961440e6c2e693814711` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-safe-empiricalMean_mem-v1.log` | `fe7c98748aa9a59ad3a51ac58daab2eeff538e779d42253ddf174f4a1167484e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-safe-empiricalMean_minimizes-v1-exit.json` | `c8938629f13ddd2f2f694e756e9718b267f7f776f1cb9187259ab29e396e11ef` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-safe-empiricalMean_minimizes-v1.log` | `927711e8d720c5c655f7ed2998313a096f4af4c29e05b1652aebdd614b8e3438` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-safe-empiricalMean_succ-v1-exit.json` | `f65991de695af7d8f76c8dc830da2a6cfc008c699aef370d63bb87431a89ea8b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-safe-empiricalMean_succ-v1.log` | `a418c2e09384fe02908bbf3dfd7c3535ce2f84c468b7a1e987fa9f3c413c81eb` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-safe-empiricalMean_unique-v1-exit.json` | `03e2331c6d012697d8ae7eb56bb0e415312ee03d7e13af0a79066746c2dce2cb` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-safe-empiricalMean_unique-v1.log` | `4d6322abc2aa85e430a536ee454a3fce20660c4bde03fb9a707caa4ae287f910` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-safe-feasibility_and_outside-v1-exit.json` | `40e11dccc7dce55a1cb034704014b3e889456c84652f8b5e0eed037b1dcd5b7a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-safe-feasibility_and_outside-v1.log` | `cea6b8d09285fd617ae8f02bef37611bd48d0903a0a08598f875b957934bff5e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-safe-ftlPredict_half-v1-exit.json` | `d8e0bdc20914d250e14d312dca0d30635966b10e0af7ef93b098f22a7fff3f68` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-safe-ftlPredict_half-v1.log` | `2511e738c874c9ecec14c339fc7623f17e388af4ff2263e48c8466ea719fa632` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-safe-ftlPredict_mem-v1-exit.json` | `9df9e135171cedee0d2e0741ef4a885b6a14e8b120e475945cd3e457d15e9fe0` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-safe-ftlPredict_mem-v1.log` | `b150aa724e91d386c1e6d930d341f503d4d151e0f6887c155f81263ba7a34c53` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-safe-ftlPredict_prefix-v1-exit.json` | `2326ea325e1a38db02d47c0e112a776de3375dc5465dbe17075d68d658b90de3` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-safe-ftlPredict_prefix-v1.log` | `ffcf438449af0c850c6ce14fc90e919068599cb5198fcca8b767766f1ab57c4b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-safe-ftlState_eq_predict-v1-exit.json` | `ff74ac2a55a7e2a8dd6956247590c7633a6311dc3e1bd87e6a280bdd416dc57b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-safe-ftlState_eq_predict-v1.log` | `a505d6252f8143e8730eec11bbc0f6abafb1a40e2e294f1e76d2a4352f9c361a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-safe-ftlState_first-v1-exit.json` | `1ad8f49bf3e82bd87939085a87f88743f0cbcdfb8d50032d3a00d9444cba4ab7` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-safe-ftlState_first-v1.log` | `3b296a3fa89bd357b5cccf3735c77d42bc91cb7655241fa402d34da1a8fb800f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-safe-ftlState_half-v1-exit.json` | `6f3afcbe997f37af3b3cc6543f0dee3b9658146f438b88784a60aebee2541743` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-safe-ftlState_half-v1.log` | `0f5cfee8ff369646c8bce6529e18c9365209a90584a31f0399c4e9d3a37c2607` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-safe-ftlState_mem-v1-exit.json` | `6897c20feed7d27879ffabce62f5b1c061a383a629cb0d9f2dd7e8184482c7fd` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-safe-ftlState_mem-v1.log` | `2943fda236657de6fc487b84044c4f6a0e7c012a6f4036951ea82b23d0f712ef` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-safe-ftlState_prefix-v1-exit.json` | `e817258c3a103a49e48b8f2c032fea689f7e8e8261e8feda6f1a407d957ae2d9` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-safe-ftlState_prefix-v1.log` | `3d5680fd645d3f07369deaa2ec9e7926bbf6ea6601214ede8ac7bc9287782c02` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-safe-general_initial_not_quarter-v1-exit.json` | `b7e222be36b75cc2841e90492cb35ec9ac4fa0fc0af78b6f5aefdcccc8073111` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-safe-general_initial_not_quarter-v1.log` | `4ad58bdbfa9e2987869bf9b3c4092cb002df0335b72581dd5880e724af61ab92` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-safe-half_state_regret-v1-exit.json` | `6ccdbb89a9be7f9ab79a6cc8ea355204c94684be35db59799cb9f71cccfcdd49` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-safe-half_state_regret-v1.log` | `ec9192d5c2ec16e493bdbc0564cc093fea6a1379205a3be1c5452a2ba4da89b6` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-safe-initial_and_first-v1-exit.json` | `28c81374f7f1b6d4bdf37ad67f0f5af785c37c046cf56195e78fd8f7229b79fc` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-safe-initial_and_first-v1.log` | `3808c3092439c125f15d1cb31710948ef35321fa820d58481f8dd91cc8aeece2` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-safe-varying_updates-v1-exit.json` | `93601c596415422a287c3a972e8bc40ee26f7f802ee00c951bbcbbe77e8afdb8` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-safe-varying_updates-v1.log` | `d0dd9d771df8c30c498f943f7deb768664be19f5edda566fd31335508ffbce89` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/leaves/all-axioms-v1.lean` | `28210cdc53f0ef27a8b7f21428d4b1477af178a86504e5a870a4ba4a075d5cc7` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/leaves/all-exact-types-v1.lean` | `a8b498f40836f6444f2c91c29256e3658e58fdb9896d4002a8f4b1ccd0bdff26` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/leaves/all-exact-types-v2.lean` | `c154d1b2e4f9710d71567e855a237bb8016cbcfee3f795d5a9c6429dbb7a43a9` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/leaves/all-public-types-v1.lean` | `de90832e9da78debe7677be69de856c3a5dc9544df04d534fd7a69ef9e422ae7` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/leaves/canary-bodies-v1.txt` | `f3b7883f5e1333c2138f4a4bca6e98eb0d601242952884d41010973ffdeaec05` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/leaves/empiricalMean-succ-proof-v1.txt` | `bed0f735021cbf68eb907712fe7499a9b226ee2bacddda76ef6b0e3acc17deca` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/leaves/export-actual-dependencies-v1.lean` | `c747d6c3120ee7bae18aa7281b6f77a71ab5136177f9185617507d45cae00ff5` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/leaves/ftlPredict_half-proof-v1.txt` | `abffc4f90d1becc6a861f36e7d54fdb8646be36d59d5bf584808ea9c618aa1f6` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/leaves/ftlPredict_mem-proof-v1.txt` | `3450464d32b58b0d4af7e047810d34afbef2a54bef0a9a735296c36a0b59c5d7` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/leaves/ftlPredict_prefix-proof-v1.txt` | `ae827521ae1a815d6388441f5d764ea04bd63d535d6a82fb930378c698bd3cac` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/leaves/ftlState_eq_predict-proof-v1.txt` | `008ac045911b4fd46b1c4f8e2875326f10e34833784ce4e8b760e3cc57e9c402` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/leaves/ftlState_first-proof-v1.txt` | `32e31f0cdbbb1c72d9d93eb1f35ef6cee3192b85bcb383d6ec1b37fadf134502` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/leaves/ftlState_half-proof-v1.txt` | `a9fe2b1d3b4831c0a4dae0ed7782d285cc2c019d18e0cd773a2bc817e75e9c40` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/leaves/ftlState_mem-proof-v1.txt` | `548ec2377e665fb8749b4f36a5f1dd968bd1e19203787b25882915cec452f015` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/leaves/ftlState_prefix-proof-v1.txt` | `2bd7f094a87093a298ff5d16f4ff7d672dd9f6090ca6fd1b734612b38457bf1c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/leaves/Mean-succ-named-v1.lean` | `52731d8dfda919a8c959ede7659672d5b64e909c58310f402fb0fbd9904cc74f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/leaves/state-definition-identities-v1.lean` | `83432461d31a0bbbfb1f567de44246b11b6aabe9f59c8db6ae0f353fa3780ba0` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/leaves/state-definition-identities-v2.lean` | `d5f9130b46c1eb9fe5b58ba68c6d7f42279adef1594c2f45709f4e34cddf8cb9` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/leaves/state-definitions-frozen-v1.txt` | `f6bc418664c9c6589096446de5fb3b4da241d2e28b7d98feb7852dd28a5840f3` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/Mean-native-guard-repair-v2.json` | `94152b090fcaa04e12a083017980867226c1013b175a34d5563320fa84f50550` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/Mean-succ-fence-v1-exit.json` | `a727146ca807aef386de19d82bae396c76b02fa653d1d13bf57e8608d4314027` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/Mean-succ-fence-v1.log` | `931cb9d2b56229d9e42133fbba80e007eaad1371f5ba73b56cb34bc295530b4f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/Mean-succ-fence-v2-exit.json` | `9e74fb53e402325df44a938b673007f644f721f4c9adff98f7d10fec6f8daa4c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/Mean-succ-fence-v2.log` | `97bc8c747f747097a1ed93b6533c966636c4aa8aa3b401e29b06558d24c96f6a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/mean-succ-leaf-compiled-v1.json` | `6613a1a3cce35a49a0aa6944200bf9ed5a058c7d22e07187d35241e6a2f4c413` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/Mean-succ-named-v1-exit.json` | `3741ee447be46b0632295cd203d6284f469f03ba9da9e812386405b720882fdc` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/Mean-succ-named-v1.log` | `c990d378bd5192a1c5b61346d7d3cd46b1463700efcb1ac48eb08147e67f2af7` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/Mean-succ-safe-v1-exit.json` | `4d4c098c496e01c08a64173a980e3746a22851b2781ef292ec55eb10ff86f49f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/Mean-succ-safe-v1.log` | `9d287a646f625f79fc505cafc8a05388b2f7dc031febbc96ea543370b5445df9` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/Mean-succ-safe-v2-exit.json` | `73cc75c878d824a1e5bfe686bbe6872d93f0b60a7543c0d0f3af0bf2ad732b49` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/Mean-succ-safe-v2.log` | `a418c2e09384fe02908bbf3dfd7c3535ce2f84c468b7a1e987fa9f3c413c81eb` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/Mean-succ-trial-v2-exit.json` | `a75044561af0745a111d40d247c36e40893e4815a36107fcbcdf1ed54ff68bd0` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/Mean-succ-trial-v2.log` | `ab3bd6b43bd4c0621af01bd74b9d47a08fedde3a09eff96baeca92638207f790` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/memory-digest-candidate-v1.md` | `fefaf4525fa10966ee79489fbdb275edd545e9d9df33e5a31528b841b072aec9` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/native-public-fences/empiricalMean_succ-v1.json` | `931cb9d2b56229d9e42133fbba80e007eaad1371f5ba73b56cb34bc295530b4f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/native-public-fences/empiricalMean_succ-v2.json` | `97bc8c747f747097a1ed93b6533c966636c4aa8aa3b401e29b06558d24c96f6a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/native-public-fences/ftlPredict_half-v1.json` | `df4dc7a20970b5ae95bc5f835df06a1e004e5da13b8ae23cbf951f8be455e815` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/native-public-fences/ftlPredict_mem-v1.json` | `3c083239459a8bec2a355204d943f7ab82576a21634877c83a705be08ba3f18c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/native-public-fences/ftlPredict_prefix-v1.json` | `72a64752e6e5db6ad2b746adafffd172e7f56f54da3e7a8f031eeb9f3dd2e205` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/native-public-fences/ftlPredict_prefix-v2.json` | `5d737caecd45b7a21e278fc3a0738422c0c26790a66883e8b5acac2facb772ec` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/native-public-fences/ftlState_eq_predict-v1.json` | `0a3ad06dae9425031dfcd221615f60e4204fb7997e959346720f4ef25c92a555` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/native-public-fences/ftlState_first-v1.json` | `6c2d12f6f0367fbc472397c21e5266b6e09c78cb9875bd09582d19e86aff8fcf` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/native-public-fences/ftlState_half-v1.json` | `d7dd022144cce45faac22b4d9e6d62612688e1d11e764b8dd1b9c5c834300be9` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/native-public-fences/ftlState_mem-v1.json` | `cf8a13346ecf742e7bbd869cd22b3891e09e685f63ba6fa6988f5515ea95b80b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/native-public-fences/ftlState_prefix-v1.json` | `0f16cad4a28e1efd7a7e9fcb5d3ccd8b062a2fe386df569b595e2b057b145b41` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/prepare-body-review-v1.py` | `ea59976ac8536f1099ed62b52e60844fe7ca9288ba962eaa69ae91dbe8aeab57` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/proof-obligations-candidate-v1.json` | `07caa60fc3d842b7bedabccafd89205ba30815ac64966c52b3542fd8ed55c7ad` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/prove-canaries-v1.py` | `0ce7b11f54c94476c9440c9f077d37a9ab16317dc9ca9b26f7014719e969f254` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/prove-mean-succ-v1.py` | `3e30b40fe62137a55f5c5b1a5ee0aa9b097ca8c3a02bd9f2745611b70a413919` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/prove-state-v1.py` | `75daa0127397dcf3acc41646bb9da00b5ca980bba5b3c1299b0fd895214b9080` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/prove-state-v2.py` | `e20e9e0b70a14ec792236241a63a6fd67c5042c2fa12243247ed09fc17feecd7` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/proving-event-v1-exit.json` | `ed7cd0b620bc2748ffa00d59fcf028c2f5a7d596308fc722471ac396810ad893` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/proving-event-v1.log` | `9c2ed7c3a9b800bba0098b01b78a9bde3c033809b0f6690c3d21a77a4356d746` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/public-named-declarations-v1.json` | `3fe0b1cf280dae4f201e43c76c0386fa116256143422a5bc0dd3c269fece9d80` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/repair-definition-snapshot-layout-v4.py` | `e0c49365b586204fdccd726671421d6e4fda960c5d1f1cd2197ac199666482e3` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/repair-Mean-native-guard-v2.py` | `e14943619fa6598e99a5c97c2e4d57316f4fd5512d55e6cbf16d84728c8eaede` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/repair-state-definition-identity-v3.py` | `f4ed41c4fe2158e090e6c03e0573fe98e4277da281152a1cfa9e6966c183966d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/repair-state-definition-identity-v4.py` | `7c7c2fc6e6fe70de49b80d4855005e731dcd5fd53bceb699bbddd1326026be83` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/repair-state-header-guards-v4.py` | `72b815847a6b3b3751ba91811c7fa97a76b64525c596cd4885314bf2b5fffced` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/repair-type-identity-verification-v2.py` | `5ea19aae2e3ca8b5494f05324064b6c5a24b157201eb7a747a91e7100e6a329f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/retrieval-index-candidate-v1.md` | `fefaf4525fa10966ee79489fbdb275edd545e9d9df33e5a31528b841b072aec9` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/safe-ftlPredict_half-v1-exit.json` | `4c676f3ad4a8d88368912572b15949ef8ccf1b92f5fb2caac2f8a91edda030af` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/safe-ftlPredict_half-v1.log` | `2511e738c874c9ecec14c339fc7623f17e388af4ff2263e48c8466ea719fa632` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/safe-ftlPredict_mem-v1-exit.json` | `87f01227cdb742da53612c79fdd27db60b70892422a2a1fc866e88d4e5b46060` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/safe-ftlPredict_mem-v1.log` | `b150aa724e91d386c1e6d930d341f503d4d151e0f6887c155f81263ba7a34c53` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/safe-ftlPredict_prefix-v1-exit.json` | `0e5a9e31ec08632cd0e92abbb7dc47b6c6ab2d1846d93c11bf2288fc2938d52e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/safe-ftlPredict_prefix-v1.log` | `646e01b382bcb15151a31d3f71d9c25c63363e8d9cc33a01bca6a8f9ea492722` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/safe-ftlPredict_prefix-v2-exit.json` | `920b53c9996f6d3362e9f3f83b959e8ba7f8c38f06eb1633e5da15b449c627e2` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/safe-ftlPredict_prefix-v2.log` | `ffcf438449af0c850c6ce14fc90e919068599cb5198fcca8b767766f1ab57c4b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/safe-ftlState_eq_predict-v1-exit.json` | `b4408090e927fb92ae3da388248e7f4010f647943a120b73dbcbf1fe48c90b32` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/safe-ftlState_eq_predict-v1.log` | `a505d6252f8143e8730eec11bbc0f6abafb1a40e2e294f1e76d2a4352f9c361a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/safe-ftlState_first-v1-exit.json` | `a3f985abb622f3113609d0772379dfa15a80d41f536f0a1c78ce3d4649a2fcd4` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/safe-ftlState_first-v1.log` | `3b296a3fa89bd357b5cccf3735c77d42bc91cb7655241fa402d34da1a8fb800f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/safe-ftlState_half-v1-exit.json` | `9771345b48ec459646170334a9019041ae5a2cc80bf7fc32f3bbbb4afd233bd7` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/safe-ftlState_half-v1.log` | `0f5cfee8ff369646c8bce6529e18c9365209a90584a31f0399c4e9d3a37c2607` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/safe-ftlState_mem-v1-exit.json` | `82d9617ee3d49abbddb0f28befbfd4f6127d5e1e92e9723d32aa57d3ec5d31c2` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/safe-ftlState_mem-v1.log` | `2943fda236657de6fc487b84044c4f6a0e7c012a6f4036951ea82b23d0f712ef` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/safe-ftlState_prefix-v1-exit.json` | `42728925086260fc6f587785a4c0726273c4b1d98f3609d666c8f772e1d95afb` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/safe-ftlState_prefix-v1.log` | `3d5680fd645d3f07369deaa2ec9e7926bbf6ea6601214ede8ac7bc9287782c02` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/snapshots/BODY-review-conversion-windows--ONLINE-FTL-STATE-20261007.md.raw` | `190f7e8b6b6c1503d1bb9bd94e535cf6bb22d70eefd715f1ddc87a66f02178eb` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/snapshots/BODY-review-proof-blueprints--ONLINE-FTL-STATE-20261007.md.raw` | `cadd895336aada43f0640b1e9558508732427af2a89fb8b8244ac47640b15c6a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/snapshots/BODY-review-proof-obligations--ONLINE-FTL-STATE-20261007.md.raw` | `190f7e8b6b6c1503d1bb9bd94e535cf6bb22d70eefd715f1ddc87a66f02178eb` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/snapshots/BODY-review-research-wiki--retrieval-index--ONLINE-FTL-STATE-20261007.md.raw` | `190f7e8b6b6c1503d1bb9bd94e535cf6bb22d70eefd715f1ddc87a66f02178eb` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/snapshots/BODY-review-tasks--ONLINE-FTL-STATE-20261007.md.raw` | `190f7e8b6b6c1503d1bb9bd94e535cf6bb22d70eefd715f1ddc87a66f02178eb` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/source-contract-inputs-v1.json` | `20468f80cc431359a08b0a621a2427f47fd427c838267a7cea6222e5e9402211` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/source-contract-receipt-v1.json` | `47bb60e34e90f9763573e3f623dad609ffbd12810a23e87cdd67bea050cc5c68` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/source-contract-review-v1.md` | `684dd604b21b07f62e1370b33bfe3ee12be069912f61b8a69fc4ee1a4e904c28` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/stabilize-v1.py` | `e7800722a81cc1a492979acc1bec052ac1a98ddd2376ecc9a39ceb13cab02961` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/stabilized-contract-v1.json` | `84c5bbd7430d1c5d10585dd5a2acf294098ec1708adb9a400bc63bdd5248a941` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/stabilized-event-v1-exit.json` | `a44ea34f1008c91cc352a86a0b45870dc95c2585b21c8a6dc268a5c35e9ca753` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/stabilized-event-v1.log` | `27b66eaa8459b10c6fbf8e8d3e56026dbf40e0d9799f48d2664e41b952d56162` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/state-body-leaves-compiled-v1.json` | `29c673373deda048e344a3ec0611090a3b116fdaa2d4749552dd3049ee5e64c4` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/state-definition-bindings-v1.json` | `256e677334791f50c0f8d1e918cb092a3d2e35897240412266774ca3b16e9743` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/state-definition-identities-v1-exit.json` | `40e48b7f29fe98d42816eb65ee9bcb83a15e9a8c032f73c4864127f89460ec1e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/state-definition-identities-v1.log` | `ad2c0a5ce7c861a92de3f5af51e1fedf0eee2358ddef0a77738008a3cf332791` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/state-definition-identities-v2-exit.json` | `f9695c0b9fefb14ab706fa3e10e02b3a5f5cb5b3af43760dda7c6ccffddd4ccf` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/state-definition-identities-v2.log` | `33e01593e6e82beb17d1b7a8e5a2eb08ea280c003a690d9a3de2ba134e5461a0` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/state-definition-identity-failure-repair-v3.json` | `0d8448ee55110e9ffac922b4b7acd4ffd74dd2258614047747da05c2ccec9084` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/state-header-guard-repair-v4.json` | `a8f1dc0ff46489d1323da47c1ab2c226cabe1b381abc46da6010460c8e23da2c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/trial-ftlPredict_half-v1-exit.json` | `e9fea138292561dcc779ad9019e1cfab99ab2eecaf46e223d333d7137eff5398` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/trial-ftlPredict_half-v1.log` | `efb4dafdce92a252c87320f0598153b128e2e8e19d62cb8485f2bf9a2ef2b954` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/trial-ftlPredict_mem-v1-exit.json` | `a78304feef6386ba7a4faefa29febee682ba159f28dfb119294120951569fbfa` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/trial-ftlPredict_mem-v1.log` | `8e7daf278c39eba46c8e0e907b040206553d643dfa6383edc3108f6ffbf7e8e8` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/trial-ftlPredict_prefix-v2-exit.json` | `5af0fbc3a86bdd5fa206452ebc554cd5ea6cb75e6ea144c4033adc00553081d0` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/trial-ftlPredict_prefix-v2.log` | `684977b5892026a966891120064f12e17222a3c086ad8037c684e02df51d6e39` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/trial-ftlState_eq_predict-v1-exit.json` | `549779b0c63ef7c678b7a6660c79db648c2bdb0a1122adf6a8c6d5cd41096915` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/trial-ftlState_eq_predict-v1.log` | `61ba66e42788c87bde849f7d5d255d139558ca3c52431f04740c6b3dd1c24792` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/trial-ftlState_first-v1-exit.json` | `d1265da74ba2481b78c2dc8fcce61c7b471b56426588f446bae3b280972ceecf` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/trial-ftlState_first-v1.log` | `9549ebfd80eed98eb115d032c1a6f1f01414a9f76f56c1b75abadd2860cb54e5` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/trial-ftlState_half-v1-exit.json` | `e75880b0e6a87ecce0ea433dc04c24f6e2b12fc7094e46c103b546d52e1b630a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/trial-ftlState_half-v1.log` | `a61887d1d3dabe7c3a791314d9eb8627b12b8d1e2c0695394d92b27f4723bf8b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/trial-ftlState_mem-v1-exit.json` | `f53c4c61c7034b2eb0554ba68d654440ee6f00680b25d4057624905507598b0c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/trial-ftlState_mem-v1.log` | `1d662c1e3ace7ba54aea22deca2874cd4999e019e96db4fb3c44c1000d57da97` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/trial-ftlState_prefix-v1-exit.json` | `189bcae55c9d4b592bffb681123da2704ada209becf265ee840f2149899a03e1` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/trial-ftlState_prefix-v1.log` | `c821a1fd19c7eaa8939e12ac968f7072a6947f1dad9a33db440739fc9baf662d` |
| `BanditRLProof/OnlineLearningMean.lean` | `811dcf3741e3d6dee19b2c4a9f43f4b266808b89843a1719e00f239a4687258b` |
| `BanditRLProof/OnlineLearningFTLState.lean` | `fa33c10252eb5cd51b3ea4cdffb10fa95c37416f3098ceb76d9d58f465ff1765` |
| `Tests/OnlineLearningFTLStateCanary.lean` | `f3b7883f5e1333c2138f4a4bca6e98eb0d601242952884d41010973ffdeaec05` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/algorithm-v3.png` | `8f723b3864f1caefc3761f2ad5acc20a380f7f3965f38cddac899732d99390c1` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/algorithm-v4.png` | `8f723b3864f1caefc3761f2ad5acc20a380f7f3965f38cddac899732d99390c1` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/audit-committed-raw-v1.py` | `654a77dac011bb9dfce70639e66ec427cf8f37b0a7a803dcd6a190773e8f20e3` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/audit-scope-v1.py` | `9369cbc20fe97161a47b14960fd345c9b2f8336552466b608095502256ec0de1` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/audit-scope-v2.py` | `931f8e38c659e98a8a4c6bf7e40fa63e370df3bf1f855638f7d5ebb8d8edd7cc` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/audit-scope-v3.py` | `37b105562dc1fe692f351000d27affd8d035f6f6c1fd44faf257f2f9fca7bd72` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/body-review-inputs-v1.json` | `1e417f29ea861faded5416244530846f8041b0951db107500c1f5ec9d87cf8ac` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/candidate-frontier-refresh-v1-exit.json` | `5db2b2359cefdb49d98c18c10ae7d176e5a927e631b4dc1d1c47db4cb8267666` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/candidate-frontier-refresh-v1.log` | `b038f6bfb27321f9a24cb9dfeb9a4a44f9a933fb3e9ab68bcb2b911bb89647d9` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/candidate-frontier-shadow-v1-exit.json` | `df5de5d90eb6f19a10b4661bb9c237f95b51d5362b05f3b47d082a4f258147f6` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/candidate-frontier-shadow-v1.log` | `7c8ce905430801746debfaafbc8b08ff5f95c26c6ced70390ee12581292f1d77` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/candidate-frontier-v1.json` | `b038f6bfb27321f9a24cb9dfeb9a4a44f9a933fb3e9ab68bcb2b911bb89647d9` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/candidate-scoped-trials-v1.jsonl` | `6a70279d77f1037e2bee28073fffb422dd0d0248f9bf22e6a625d7cb51a94136` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/capture-reader-v1.cjs` | `e392a4a77f642516de226023e7415f0590651edd715a30f8f0f1b4123df20966` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/capture-reader-v1.py` | `8825fc7c25fcbdd9c66dc77bb18747688d3d6a3e236a1e111aa5c20bfcf5e622` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/capture-reader-v2.cjs` | `cc09ced501b8dc4a4bcea7a7efe54420cdee55b81d0c4c3f0b0f2bccd486d3b3` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/capture-reader-v2.py` | `34f710213c4af8aeac3c810dbe929c75a889f1ed15fe6b89c967cda1e5d8f3d6` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/capture-reader-v3.cjs` | `a1cae24887dbaaa1ee780004c242ff6f1e8569fdd215b58ad805de8d49ad7260` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/capture-reader-v3.py` | `747c9da2dce7c08d0f1775df27f1c48feb0ecdff56620c022e4da7e8e8ba204f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/capture-reader-v4.cjs` | `d37a8a22c24db853b6fc0e216bd2d885fe28cf879b679c80d691fa3beb48ec5c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/capture-reader-v4.py` | `f9a285c0c9c53d1bebce3936f930714d5b648d1f69b3486293eba5a9dab6b73d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/capture-reader-v5.py` | `459249cc9316c07cf00cc4c4d4e1f2cd659b353d31c9f0c4844a163a3b56acc8` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/catalog-boundaries-proposed-v6.json` | `6806d5fc69f3ebd42814f502f27afc1295369a80d3c0fbb6f7c59f6c57fdbbe9` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/catalog-boundary-impact-probe-v5.json` | `e32986fce966b5d3d743aef12c8b325ef518d6913adf83d01f0e314f36123518` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/catalog-boundary-proposed-function-v5.py` | `63c3f128342d7f44e609e9da6b547fe70aa64c72f39c341fff2987b1a80195cb` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/catalog-focused-tests-v7-exit.json` | `705b080ea0f2c51b34b6f39350b69ef89e1691b3aa7ccec5c23a8b4bb4963443` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/catalog-focused-tests-v7.log` | `a680696b6144e01a8277d1288f12e54444d8f7667c528fbed9d1d65d566b2d33` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/catalog-implementation-bindings-v7.json` | `846009d85e3a45250e34aecbe4fd84cc43e3e52e2d2246233660f4b053c653d1` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/catalog-implementation-invocation-failure-v7.json` | `99762a6b0fc3296246a28638f795079d9e62cbdf130fef25ee838710f3b1cd03` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/catalog-probe-runtime-repair-v5.json` | `38ac58c91aa9cc52a9f4da2694384aa179292fb4d2270954a950ab61b8f5c118` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/catalog-scope-contract-v6.md` | `8ccdaabe0af19d545035b49d34f9b47c42cceb8becdd33d244ce5a3193c500f0` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/catalog-scope-receipt-v6.json` | `5fec830183dc27084ee73416568e3be23613ee4e3cebe99bbc5cfd2cfb8e6a01` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/catalog-scope-review-inputs-v6.json` | `cfd2065e2376e8a30f5e2568bda07f9ae17a0d6cd09c9d1e20bf84b5f4d990db` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/catalog-scope-review-packet-v6.md` | `24e3640773cc1204ee7086a2b38a4373f350caa32b84521398b8fd9039ce4650` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/catalog-scope-review-v6.md` | `16b86bd73d4214201b106e8ed23ee2c86c14235fd75e41b562f024c29b2c48cc` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/catalog-scope-reviewed-source-resolution-v6.json` | `741c2e6a0bcd2dc29f5f949d69d2da1efb3a9ad38f9d74bfa44a0618b72a4a77` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/catalog-scope-stabilized-v6-exit.json` | `888147b0510e24db7309a868af04bd7fe5fbb8fb32b8e9d14ab0b479796247d1` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/catalog-scope-stabilized-v6.json` | `7d68f874918bfa4975657e0a87023e96752167c62708d68c156c5536ec3f4e63` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/catalog-scope-stabilized-v6.log` | `139e32a71453302d54632188b0bdf1c669a4fdc5278f77e77e9a76fdc0869b61` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/catalog-source-comparison-v7.json` | `fbb078dcad2ebdca96456f6fd3440d789797cb88cb5b2fd0460c6064be4b3eaf` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/check-scoped-diff-v1.py` | `ac80ccc2b3a9ab382713b8df89c2822b53bfd885a267b392f03e435f52f54f8e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/check-scoped-diff-v2.py` | `da9fb25b7a19ed658e7aa6941772785629f611f71204cd4102b4002532e5fa21` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/combined-gates-reader-v2.json` | `a3f649d6e8584f26dc83aafeca44544585774d5e0b769ab312851ba9ab38aef5` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/combined-gates-reader-v3.json` | `e2a1c67bda585aa86c60a72e2a057e1d7eb47c64f105817df890bd29faef9ef6` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/combined-gates-reader-v4.json` | `32f38ebb90a186f24c427cf22257103c38ad5c1f907d1bfaeff054b84a131f71` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/combined-gates-reader-v5.json` | `cd74fb8807bd48c9c9dfb16a8da66641389f8c25e618fb8d332c11a1dc2314c9` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/combined-gates-v1.json` | `d865ab222322b351e87660ff078c3d81cb12383f7174aeea78b806a24e109c7f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/combined-root-v1-exit.json` | `9ace7ee60a7197172165298bb6165c55f90fd23264c3e87cdf5516facacb56e2` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/combined-root-v1.log` | `62c09f0f6d0bbb5824636a931ddb3fee9437bcbe325ee4dda82c4412edd78a88` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/combined-Tests-v1-exit.json` | `2ad36044ef7c8c9cbcf133d0d8dd6b7e3dd216af7c7b6d40d5af549e17ba4cb3` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/combined-Tests-v1.log` | `0ba87fdbfaa645de78039b2c67e0927f27323c476bab581f00c74e44aacc390e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/commit-owned-v1.py` | `681f459ab2a0d79d501c9d66b5164380ca814e0663a9aca4f9c8fb609bed08fb` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/commit-owned-v2.py` | `23a4622c2932a7c5be7df118a4ad7e8a77bb69631db51b46fa98531be7ec384f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/complete-publication-v1.py` | `b1a4139216cbd0f13dacc7e2a66b0f8a777bd66541d56a73577450c1ea2e824e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/complete-publication-v2.py` | `6947011afb86f751866852d7f3cc9d6bebb0cce56aecff99442dd63462b80be7` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/complete-publication-v3.py` | `87c00c40dd8834d61a1b37a947d25c1a4aeba54beff2a6ba3e5f695a7d9a7895` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/complete-publication-v4.py` | `32ad701884628b849264f51853b0cfd8186bcda140825ccf285bc7d409b638a4` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/complete-publication-v5.py` | `72ed9828fcb1f00804be47b1e0588c856cc8f5b774d21b7335dbbad1a27ac7a9` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/continue-catalog-site-v8.py` | `9aca1c0eb7fb3f13bbdd6c7507b93ffd99457684fccbff03aff05c9f0ac88288` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/continue-reader-site-v3.py` | `d8d2b2ffa14f3e2b40b73e089877969544e70aec21f78aa42e3206205d205ed6` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/continue-source-layout-site-v4.py` | `6ef2f4f036828c754d5effbeb0d309d9f0a9d015bcf0bc2925e3571df4472fd4` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/continue-source-site-v2.py` | `46299f10cb0104f4ffb7474af4fe3785557b997f093413e02004a992bfa180e9` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/contributor-exact-v1-exit.json` | `41503de56f9b5cddf130b60ef9172926fb11b697a7ce27b9671971b72080685a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/contributor-exact-v1.log` | `eb3d3720f7fb13832374365746e80f240350d50e9e0d0b49921839a289ed9660` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/contributor-reader-v2-exit.json` | `ec7329b7360755613c29bad1354a4884072ddd52d78ee56ac8b868af6fa8bb4e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/contributor-reader-v2.log` | `540000ea64efe1f221f930c4da616c365398570edf6d69b6cac87e51bf51d386` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/contributor-reader-v3-exit.json` | `a4edd355d97a72ae595131c982f6ac5f989606720b5aa0a10dc4df6721b2237b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/contributor-reader-v3.log` | `cc763654fa5ef164ac478ee93f1e9e7b95e4967ba69848ef664bd5d630e19d16` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/contributor-reader-v4-exit.json` | `6f88e99958431a1c2a7732643da1b4ec1d41f17a310c6f46e26993bf5b04c847` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/contributor-reader-v4.log` | `af28ba94ef90a681edd66328fb2ed0c15088201e534ea4e28171c67f6c138151` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/contributor-reader-v5-exit.json` | `3baf6d2a058384e666836560944c6ee9545f32829cbd886150cc7670be72c129` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/contributor-reader-v5.log` | `415b7f6f9d464739770fcaabb7f1ec90e5628e71af1412662d864fc88c29078c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/create-pr-v1.py` | `ee72339972f7e3616df7f13101c48e8b7370d55a9005eb319a55cc0040f670ed` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/current-final-plan-v11.json` | `5550f34054debad602d68838af22a73eea7151d9c28603c1b01652417191950a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/final-reader-packet-v1.md` | `6e708aad81a4b1f766d80085d20d9d35f68ab40546c8f08c0ee24af42fabf728` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/formula-render-v2-exit.json` | `2266bbd664c39fd435bcc4797b4abaf6a9f08b9bca0791e74162b549d5d1e4b0` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/formula-render-v2-node.log` | `46abad7012a0af1675187911ccdd4b9b026645df184fc08d5a6f935ec33382ac` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/formula-render-v2-server.log` | `77d89ab537fc8f6d11a9f57dab6190c4773bc1641bee3cad5a8b9c270b6ebab8` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/formula-render-v2.log` | `11a9042eabb489ef1b3f4886743210f032e3e12dd33805874e33c7340dbcd039` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/formula-render-v3-browser.json` | `a661c3292702546aa1763a82c58ccb42703c85a9f74507a315a501cf97a01b4b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/formula-render-v3-dom.html` | `bd2fc221fd9a579813d24831950d57922b05373debeb91781087dce8b820d773` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/formula-render-v3-exit.json` | `d00c4d18ce68273f532a8762a047d993cbd403478579f6602f8d48c94f826639` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/formula-render-v3-node.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/formula-render-v3-server.log` | `3540f107fa2100ab90bcaa860f972e1fb96d2580d63c9938b571418ca113249c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/formula-render-v3.json` | `4691a5385fce960f5aa586ad6a7ccc80b0b61db8104f9f8150a5169b9888584f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/formula-render-v3.log` | `087033637dc67c5c7d7115878466dbf2a474397a88723370b5ede19735710c84` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/formula-render-v4-browser.json` | `a13d80d965b763fa29ad98f35b20543f0e6b6a80fc81a13cf2873ea3a8ed77cf` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/formula-render-v4-dom.html` | `819286c67d999f3ae709ccc123b8a06be6ee1d265bdc12f4d4cdcb6425c6a897` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/formula-render-v4-exit.json` | `1f08e9c9048f0615f31fecb94f68cab8e02958b411d4f07dade5a6c395835d1d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/formula-render-v4-node.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/formula-render-v4-server.log` | `3540f107fa2100ab90bcaa860f972e1fb96d2580d63c9938b571418ca113249c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/formula-render-v4.json` | `fb1b2353402877701c9db25fe838d50c19011a76b87f150e9d3184ec6ec474a8` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/formula-render-v4.log` | `087033637dc67c5c7d7115878466dbf2a474397a88723370b5ede19735710c84` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-harness-reader-v2-exit.json` | `277ea3c58fee7ec39c94bc7a60a45f9d9b9db7fe3595db86ee60fdd065f3aadc` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-harness-reader-v2.log` | `42ab3ccf0d9a8dbbd59ace626be5222fd0b90d5d603d44f18468e4a81c64e41a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-harness-reader-v3-exit.json` | `1a2a5c78ebb571e3715f3490f1e9c5fdbafe3e17a0b50c7192bc268289350b86` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-harness-reader-v3.log` | `5c89044496066cbd747cbf50a11229fdb0aa62436b2dac1bb6b3907c1e904897` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-harness-reader-v4-exit.json` | `8022fac313fa26b858210edaa62b6ca2013ed9f3f36c2869bbf66886ec1e1950` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-harness-reader-v4.log` | `ec4c5941cf8cf88aea204238c308961e78dcc976a953c4096dbdb833d2cfa2e3` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-harness-reader-v5-exit.json` | `55d0cfb3027beb2b3157aa07e42222d30edc319065941bd6f9fc6485da3e717c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-harness-reader-v5.log` | `a28d789bcaaf1f8c84c32bb9b595247907b1ee119ead13630c9e15b5dea140dc` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-harness-v1-exit.json` | `18d48765377c412b4b9b498d6c444f613baf1a707783589da4009896ae749b60` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/full-harness-v1.log` | `1289fd45278562f80a881168fc52f76f6b00070b569e8d0b39e349cb9876eff2` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/help-contributor-v1-exit.json` | `beb6d05c097f75475d4b1a988b6c7423723ee1a7decab07d4ba1510e575edd50` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/help-contributor-v1.log` | `16f3356ce372e996cafe1692459a55836be2ea0649dc5f66d545296d5b1d7622` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/help-site-build-v1-exit.json` | `0dad4ff61cc69fd909545a21646858229d87e29c147a9d21b5d56eb5bbd58ec9` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/help-site-build-v1.log` | `53ff0425f725c9e473c6a0a4b60e24189416ff73bf591c4f5f6528c2b9f375fc` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/help-site-check-v1-exit.json` | `3bc17d29b8473c73a92ae7f77e328b266e4ee1aefd4d30aa3bdc31568a284bd3` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/help-site-check-v1.log` | `54ca1a124d1bbf5f4583883ff1ba0052b8a52ee1fadfb2287db84b02b12ac01b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/implement-catalog-repair-v7.py` | `e37d66bc14fa84cadd58c6f358649314eb6dc7cc843c945e8185cf68beacc67c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/implement-catalog-repair-v8.py` | `0ff5615ae6dc5a221f4aa557725a18a2b16497dbdf2b9690039e2208cab29eea` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/integrate-reader-v1.py` | `37258ec661995f8d0d8dfc6c00392afd267d2ff27505b7a3790601b2f562c4e1` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/integrated-gates-overlay-v1.json` | `8f7f41d8a38daf6f85c24909df6969685073cb77c04b435339ca1b14528bb732` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/main-diagnostic-parser-repair-v2.json` | `3b6b74bdfbe106b0a96c0d2699d722bb66792fad972251f12a1f86ba32f15172` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/main-parser-candidate-event-v2-exit.json` | `9d0f9b996115b548dd934470b53401bca724c9672e9145735a870003cf0aa1b0` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/main-parser-candidate-event-v2.log` | `3b31f30fca334e34a728a7fff8cbabcf70a6c61f0fe9e469b0df9977bc858953` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/main-parser-repair-event-v2-exit.json` | `54f2c1323b639e0270a1b0ee48c9d67c00e9a4add97f7e15b91f266a2e92d256` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/main-parser-repair-event-v2.log` | `db4d680a49360fad1d1b026ac824988f13376da03ef0ac24c10eb07434052a58` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/main-relative-diagnostic-v1-exit.json` | `fb49760241d3e8cc8c13f9501fa5c58a181fe451c61b3ebfee5f5f820734aa7e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/main-relative-diagnostic-v1.json` | `0dab9022bac6fa6330c5e1c6c94454acdcf2810468278501b40626a02896b904` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/main-relative-diagnostic-v1.log` | `5456702cc61cdc41a5cb32aaba5b760fa9a4c3878e6b573fa366868b0619ae2b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/memory-digest-candidate-v2.md` | `69d203ed65c15e0883441279df909b6aba20a442a211dd5fd464d71d534dd19a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/module-new-declaration-01-v3.png` | `3cfede9eda6139762ea42afc6ccf99d8d2a595b3aa0ec3584a57e573cb0b2b6a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/module-new-declaration-01-v4.png` | `3cfede9eda6139762ea42afc6ccf99d8d2a595b3aa0ec3584a57e573cb0b2b6a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/module-new-declaration-02-v3.png` | `92b9b7d8a7e3391494e3b970483b8082c691777c5fb407d7b1588fd7fae7009f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/module-new-declaration-02-v4.png` | `92b9b7d8a7e3391494e3b970483b8082c691777c5fb407d7b1588fd7fae7009f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/module-new-declaration-03-v3.png` | `1d13a39642a49f810d6d7800dfd61d879dd58deaae8e2830cea82dcc663e4e18` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/module-new-declaration-03-v4.png` | `1d13a39642a49f810d6d7800dfd61d879dd58deaae8e2830cea82dcc663e4e18` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/module-new-declaration-04-v3.png` | `2d7fa30f3e0f9261bdcf4787524b32c9bea64ebdf90d90e6321e6b04cdb25ad0` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/module-new-declaration-04-v4.png` | `2d7fa30f3e0f9261bdcf4787524b32c9bea64ebdf90d90e6321e6b04cdb25ad0` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/module-new-declaration-05-v3.png` | `b15a2ca357d77feefbc9f954b67577c4bdd0151feddcc8cb0e93a0896904da00` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/module-new-declaration-05-v4.png` | `b15a2ca357d77feefbc9f954b67577c4bdd0151feddcc8cb0e93a0896904da00` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/module-new-declaration-06-v3.png` | `4798f2ed5f3ed1357ac58f63cdf5de571b032bcaf209b582a480fbeee9ff83aa` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/module-new-declaration-06-v4.png` | `4798f2ed5f3ed1357ac58f63cdf5de571b032bcaf209b582a480fbeee9ff83aa` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/module-new-declaration-07-v3.png` | `0859c43c43cf4a853b1a6677ba05edcbd2d5ba03b2da17c5906f3890960985e2` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/module-new-declaration-07-v4.png` | `0859c43c43cf4a853b1a6677ba05edcbd2d5ba03b2da17c5906f3890960985e2` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/module-new-declaration-08-v3.png` | `ebaec057fe3e4fa3001805be59b0527d07a8ed943d2dc4f198033b18f9d28bee` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/module-new-declaration-08-v4.png` | `ebaec057fe3e4fa3001805be59b0527d07a8ed943d2dc4f198033b18f9d28bee` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/module-new-declaration-09-v3.png` | `0fb8a15e5231caa1cadb1ce6b38b3c35b1b14cae580d881190ddba79bd3ae179` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/module-new-declaration-09-v4.png` | `0fb8a15e5231caa1cadb1ce6b38b3c35b1b14cae580d881190ddba79bd3ae179` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/module-new-declaration-10-v3.png` | `cfc549666f0c1d3bdec7caeafe0825ab3f343efcde948361aa1bba2b65bce911` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/module-new-declaration-10-v4.png` | `cfc549666f0c1d3bdec7caeafe0825ab3f343efcde948361aa1bba2b65bce911` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/module-new-declaration-11-v3.png` | `3045a46e9fb3ac6a5f85ba548597c3c710ffca2b6dc484dc1b84c5936b14c29e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/module-new-declaration-11-v4.png` | `3045a46e9fb3ac6a5f85ba548597c3c710ffca2b6dc484dc1b84c5936b14c29e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/module-new-declaration-12-v3.png` | `44718e853e2fe3bb64b65dac2df9becc50aa56effed49d82d62d48726150c0a6` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/module-new-declaration-12-v4.png` | `2d8e601db23365cdaea35b77a9b6be8badde5b06872e8fcc94cf6646ce3ea7fc` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/owned-commit-paths-v2.json` | `8f962b594a1291b215571c141f010e41d55d5593fe8213bac8f5421d28ab3c6a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/pixel-review-v4.json` | `fb3fb7aa36a0406327643f91b7deae15e37e371dc90db14b5c342451579c14df` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/prepare-catalog-gates-v8.py` | `1012487f70032327a0e2925322466328aa01c82254721090a90978927ceb8f8d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/prepare-catalog-scope-review-v6.py` | `962aaab39f958a5451d60ff3df2b1cba2b84b6a6356cfed8fa59b7f6bb7f37f1` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/prepare-current-final-v11.py` | `41b7df28cbcd1a91c261c1545169f05b5d5404b83a1126bf4cc2dcd34887026b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/prepare-delivery-v1.py` | `e937ec60632f8a467cd933225280738d861e6861f3d57d94988fa047a3ce7c4f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/prepare-delivery-v2.py` | `efe527f84b74f819a5783321e3b77cf587205d6c09ab12158cbc7e8fc6872fc3` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/prepare-delivery-v3.py` | `a58c98d1f584bd08f9e6dd0f1aa2c339a72ad3bcb2b16316a8223964092fc505` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/prepare-delivery-v4.py` | `8839c854919c2424b4aa687caedf62b4b32de423b19055884d8d7149714a2ebc` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/prepare-delivery-v5.py` | `8ae3787e7d88df49ae4c0f52e1cefdd3342f704f56e52903c8cbd175a933698c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/prepare-final-review-v1.py` | `300b689a471fed509dcf037fb754556250e44d523cd2768b35a7582d20d677a1` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/prepare-final-review-v2.py` | `d297e81297fde5a071a25ba8774031748ee8ccc192aad017889ca5e67f59f8ed` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/prepare-final-review-v3.py` | `5ab6395f872fa4198179aea619a7002fd100229f9810dbb7d349bd6e30768f5f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/prepare-final-review-v4.py` | `67c8e4a572a91f449557e4c782ef305e88eb54404e98690cf916184cf7a47370` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/prepare-final-review-v5.py` | `6e422e62453818ce7be24181fb2209741a6071327ff30ea745b47f1e031dc7be` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/prepare-final-review-v6.py` | `48a894e47de6a5bc97a63d88d8444cbb8937030f4e987a64b5d15ea82d813274` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/prepare-final-review-v7.py` | `0b03f36368a12af0205150b54949e6ee8282ef370fff637655c444da1ebf4b84` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/prepare-final-tools-v9.py` | `18fbcabf705d310f3dbfcec6df6021cff870a5adf80d981c5a963b89927a33fd` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/prepare-integrated-gates-v1.py` | `b226aac54f3fc51b8a6f94f0bae0e86cfe7fd502e80abda27d5c4881a25381cc` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/prepare-pipeline-clarification-v3.py` | `efd172c0def96a11e0f1696cb7790432e3e8e20328b5719d7a857cc216edd943` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/prepare-publication-tools-v1.py` | `b729eb495797d6801220c16dac3f7fea17b39131805f83dc56df937b5f68cc5f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/prepare-publication-v1.py` | `340e1d3e834890b63223b3a2f995f6e47397beea2a8f846bba2e998557e1a64b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/prepare-publication-v2.py` | `d287670bfc2f8526f3d6fd9fe4f29b4ddc95e4d1b44dff018b6e23727b588d19` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/prepare-publication-v3.py` | `1212fa935ed8c296c0dc9b1bdb9acf0932c758c09ee057a49491316ba62695ca` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/prepare-publication-v4.py` | `5c6745e94612f1cb4a35a5fdbea3e27db0db2849d17cb3ceb9df993fa7dd6c4c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/prepare-publication-v5.py` | `b0c2a284fb20cf1b8073852f044c32d803c535ee32c5c3cb6905beb0d82f6f43` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/probe-catalog-equation-boundary-v4.py` | `05b93ba4c909e8349e926ed7c61a99d5cf48dca16a044eff0fb4e6588f340815` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/probe-catalog-equation-boundary-v5.py` | `4be2ecd8470579286a21dc203b4edb712ecca7a498b58dc37ffdbd777774ac47` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/project-gates-v1.py` | `81b8e3d810fcc5d61c2ab261cec293741bcc77ba45551cf6be03315115fd73a7` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/public-body-receipt-v1.json` | `dad8259ecffb1a1192b7f60d0c3741fa817919d6d6c9fa54145c311fc3eeec0c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/public-body-review-v1.md` | `8d97e011c56161714bd7d84bc64b0d30c79df6cf4fe93b8be039a13bce1c30ec` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/public-note-01-v3.png` | `4e908ef15a715d9fe69af4946b87d2394db2ad0358bc3781891ad1961db2c23e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/public-note-01-v4.png` | `4e908ef15a715d9fe69af4946b87d2394db2ad0358bc3781891ad1961db2c23e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/public-note-02-v3.png` | `3026d2a90b42254a19d3df6700edac696eb50ff19a4ce58ecedf132434397aa0` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/public-note-02-v4.png` | `3026d2a90b42254a19d3df6700edac696eb50ff19a4ce58ecedf132434397aa0` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/public-note-03-v3.png` | `4c891caafbc7e9e59bae327946c1056242bbea60929adb8f2421f00c56a04453` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/public-note-03-v4.png` | `4c891caafbc7e9e59bae327946c1056242bbea60929adb8f2421f00c56a04453` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/public-note-04-v3.png` | `16cc0ef48e5027da1af2755f8a87c686494e3bc307d098f447f4a20f416e523e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/public-note-04-v4.png` | `16cc0ef48e5027da1af2755f8a87c686494e3bc307d098f447f4a20f416e523e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/public-note-05-v3.png` | `fd75d5ba4722f6d4ee12ed374e1da018da4328d4d176da102c40e86f5e8061da` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/public-note-05-v4.png` | `fd75d5ba4722f6d4ee12ed374e1da018da4328d4d176da102c40e86f5e8061da` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/public-note-06-v3.png` | `f41ded80fe2f91a1e53b806d9d72f49f8b8a3c387c7fbf8e4eecd3e8110d2a32` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/public-note-06-v4.png` | `f41ded80fe2f91a1e53b806d9d72f49f8b8a3c387c7fbf8e4eecd3e8110d2a32` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/public-note-07-v3.png` | `b5cf76737a5aa32ad1cc8e960cd800919babc6ac2d635d47b6ebec5d292fad0f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/public-note-07-v4.png` | `b5cf76737a5aa32ad1cc8e960cd800919babc6ac2d635d47b6ebec5d292fad0f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/public-note-08-v3.png` | `d8b8f00acb6727795d30281b821684f5a8a7eaa2adb6b3116ea2c4f869e6a29e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/public-note-08-v4.png` | `d8b8f00acb6727795d30281b821684f5a8a7eaa2adb6b3116ea2c4f869e6a29e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/public-note-09-v3.png` | `9da6a7b6ba503972774d158276bb826ff3c53b7e2e46b95c0bacbe3e5525b571` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/public-note-09-v4.png` | `9da6a7b6ba503972774d158276bb826ff3c53b7e2e46b95c0bacbe3e5525b571` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/publication-tools-before-FINAL-v1.json` | `230fd0539068687af827165ceb8ab4db12eb22a24ae897a17bab5ae31ded9376` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/publication-tools-before-FINAL-v2.json` | `72ad445c1e8b2b164d7eeb4eacede2f123a2eab713c7c551347b0da346bbbbbc` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/publication-tools-before-FINAL-v3.json` | `81f9c76a5516b6e4dc81cfc0a8ecb782454eba7869042a82b7cad4b7d8268e40` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/publication-tools-before-FINAL-v4.json` | `70e40d17ea5e82e436119349ba44388e1412d3d6efe893a05c23f2225b14233b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/publication-tools-before-FINAL-v5.json` | `7befe7037254e987fef274873a69683f67da73ccdb6c7e443d875f94c6c24494` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/publication-tools-before-FINAL-v6.json` | `471283101856f7dc98e04d07b22ab8977a43a688a048f7fb7cda90a9aeee45be` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/read-only-retrieval-error-v3.json` | `8ef998ebb86dfab4be64ad8b9d5e734f7087f26149633e39be2deb2c432235c1` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/read-only-retrieval-errors-v2.json` | `ccd34f75ab70cdc6bed39e106b34aaf2eae534cbfb80f677e23f25047ccef73f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/read-only-retrieval-errors-v4.json` | `670774d3045826e58dd5bacbd6542d81c02826ed6b48278bff112eda5d66a50c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/reader-feature-candidate-event-v2-exit.json` | `640c743677ca4df016fbc78920dd235c418e0c1183d5db82546445f1f1202e95` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/reader-feature-candidate-event-v2.log` | `0951e34ea482aea4485eba6345024074f230931c6b5e6c3f9e7e1b9ffe3110b3` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/reader-feature-repair-event-v2-exit.json` | `795f99f8e6e6aba2b34fa171845ca7d9bf040e6acbb5bd9dbe681550b275f65d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/reader-feature-repair-event-v2.log` | `902139c084d04551f89cf26a18c3e30e939ed43da026a55912dfdb09ea334d69` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/reader-feature-repair-v2.json` | `9e94f56591ebdf69f1be687993fb2387101770723e4007429f1807fe6f864db6` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/reader-first-viewport-v2.png` | `07186e11be0ba1f21cbb6cb82ec9c6818f9ecaee8e2c10678a4aae3d4b20cd45` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/reader-first-viewport-v3.png` | `07186e11be0ba1f21cbb6cb82ec9c6818f9ecaee8e2c10678a4aae3d4b20cd45` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/reader-first-viewport-v4.png` | `07186e11be0ba1f21cbb6cb82ec9c6818f9ecaee8e2c10678a4aae3d4b20cd45` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/reader-integration-v1.json` | `221bf045aeccdb0dc48475d03ee6e718f8a7a4d05347faa6c2f5c0b0b265011a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/record-acceptance-v1.py` | `e1ae884deb8dad9a7d942b39b84d5e2954c210ad2fb056d2b622e860ab07230e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/record-acceptance-v2.py` | `e1ae884deb8dad9a7d942b39b84d5e2954c210ad2fb056d2b622e860ab07230e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/record-acceptance-v3.py` | `e1ae884deb8dad9a7d942b39b84d5e2954c210ad2fb056d2b622e860ab07230e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/record-acceptance-v4.py` | `9d0126fc2e05ba8cd3900894b3cc409220a369502631f6853c6e1caa6f98bed4` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/record-acceptance-v5.py` | `a8d7475219478293fdf460d6d438dc85fa497232159e14caf0202693c25d67d6` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/record-retrieval-invocations-v2.py` | `95601cfbe5c037acc59807791ad35e62fc1a420d6d1b07828ae420e5cadfa517` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/registry-base-snapshot-v1.json` | `960eafc716c17c1dcfb25ac7c2d0730dc2ed5d3be0d227fd2a2c1e604e1d409b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/registry-boundary-repair-v5.json` | `385fdf0b83d93f83ccca3cd6fc63c69b600dbb17b9b7a8c4ae496c2ccf28893d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/registry-path-repair-v10.json` | `65d960d5d5330b0416eb41f90f71402ef8f65afd980a1a97d31f1bd0fca795fd` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/registry-v2-exit.json` | `3f7ade4930730f73d02b6525d69ddc1dd959bc2e45394fbd158497f80b5eb374` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/registry-v2.json` | `5988f21316c6c44d7b5a744d5b592780801822bf249a529e777d5df760ab686e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/registry-v2.log` | `7bb09fff6ed44f7671e98113c6a33a8fad2d1a04cf0969e16783a851ac37b55b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/registry-v3-exit.json` | `8704da850d8c46da66bfc3f2b1847bf07eb4f92c2f23c1a793bfff3933305631` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/registry-v3.json` | `7dbcabf69a34c0dda72121d9d91bdec2cf97925ecbfbab456d76ccfb97b29170` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/registry-v3.log` | `7bb09fff6ed44f7671e98113c6a33a8fad2d1a04cf0969e16783a851ac37b55b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/registry-v4-exit.json` | `9bb1852427c431b383abefbe746b75a7c454097e51e85896105eb2b1e49a2c26` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/registry-v4.json` | `542d66340b069cb880c885f4ea89b430aa22282a2d1fa4dcaede36665ab9995e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/registry-v4.log` | `a5c76543e6ee3058ab0e06c18f86e805291c8b565ef1b780db5979fce81caea9` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/registry-v5-exit.json` | `1a5216973af8906c3bf9ea1e29bab1eca2bf378bfe3d4304b433b2155e3a5bf5` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/registry-v5.json` | `542d66340b069cb880c885f4ea89b430aa22282a2d1fa4dcaede36665ab9995e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/registry-v5.log` | `2c7ef82725f2f18f57a0b914c82c561652308948e42c7d5b24ab8819522da56a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/repair-catalog-module-import-v8.py` | `15f100a6dd6a18778fed756aadbc88087ae8cdf8eafb24b4ee81654c6c4081f2` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/repair-catalog-probe-runtime-v5.py` | `08e62859c2bad779989f621492f1a277a6c9168ac9b4f61e62ca1a246e79c1e1` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/repair-main-diagnostic-parser-v2.py` | `f3cbd4c7182f0b600289e4bc80731d41128c94ec56b67bd661af21f76affd31a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/repair-reader-feature-metadata-v2.py` | `3613d935b4ded8fe43f35ad471147d6cf3cfb0fa31331e3b39b96bd23e6ab12c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/repair-registry-path-and-bindings-v10.py` | `1524f951feaecae6ba6f0c58b0b1d752505a48dda7fd6af090da001fa6dd7459` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/repair-shadow-digest-version-v2.py` | `b1706aee0dd285c877b915692452d2c9d0970549ec610302da20f324922608e9` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/repair-source-formula-layout-v3.py` | `d4963d8c59a47706f3248ebf2f7dcef10726dd1e09183b9e78f9df6eaeb5210b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/retrieval-invocation-failure-v1.json` | `3eaa6ffcb5d712f5c9a82db89ad744dbd56c1a5b334222fe9fb38d42271a1f87` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/scoped-diff-audit-reader-v2.json` | `5c7146daf7c343cc290626881cb715776764e9bf23f9650ef8c27b9bbf8a34e6` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/scoped-diff-audit-reader-v3.json` | `3ec0cbf1251ee1e764a75a061f71f4652be1248d09f815a7a7476af10c64c11f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/scoped-diff-audit-reader-v4.json` | `9467aae6d639b130266a251cec3bd2f6c3e51a012e87caddd0690e604dda0740` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/scoped-diff-audit-reader-v5.json` | `a2f4eacfcdd7aef8dc9f504fb003f6dc5be8f2f2506c835703ac125d5a6e8b2a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/scoped-diff-audit-v1.json` | `6723aea8571ba75842d3d3f979036ee05cd52df40cd3aed52f89d079f3439f75` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/scoped-diff-reader-v2-exit.json` | `87419a2c7849e8fcbe6a32afc99206f122002797558514b6a0b79a5910dd21df` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/scoped-diff-reader-v2.log` | `cbb0b7d04452d072d24183c7fed834b31c87a685adb156ba339ce9a5573edf1f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/scoped-diff-reader-v3-exit.json` | `377330707e8172cdfd08d1d813d519d2b634079cadf11f2dc19ce048337c9b54` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/scoped-diff-reader-v3.log` | `02cd0bc55587e7eb53dfd3bdded8550d8bb83ae237cf258dfa421b3c599151a7` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/scoped-diff-reader-v4-exit.json` | `74be3a770c972de35a33b983be420ab4dfafe6314957da7eaf8c3489be579708` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/scoped-diff-reader-v4.log` | `37b945d7d3145087bbb4a6381ee5d3b32e5832c56f648e9f500686bfbd64c986` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/scoped-diff-reader-v5-exit.json` | `ad953c7638329200a896a6263c304da7099d23db49ba4df6622050cca7b22ee1` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/scoped-diff-reader-v5.log` | `213a9418b595d55ea71b059282ee73faa46c8d40b284bf2ceee873067e5db67d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/scoped-diff-v1-exit.json` | `8800ff7029dff4993ab779931e720e2d5601d4946577fdeb215896b4ec9d3f20` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/scoped-diff-v1.log` | `de4566e4dcfc62dcc21cf9cc785f77542db08cb50fe269995c62adaa1731212f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/shadow-digest-candidate-event-v2-exit.json` | `a0aa6a2c64a1acc9444558c8a537169b39ff0cf43e65cfff8737fa50c25f3b48` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/shadow-digest-candidate-event-v2.log` | `802bd569a3794a385ff85f1512e1052993346a3fa728dfb31fc8fb6c19b892b8` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/shadow-digest-repair-event-v2-exit.json` | `4c9ef68d91c1ab7f1723d7c04bce2afac41bc14e04088ac263619c0be50bc9f6` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/shadow-digest-repair-event-v2.log` | `41008568598dda1bdfe2ca9031c8272aa6bfe112cc1d7748ab87b80dd9a03104` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/shadow-digest-version-repair-v2.json` | `587f318c4355a2998311828557e20c3cc25f95800f66262a29f4872e6c68152f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/site-build-v1-exit.json` | `a29ad0841a1734bc158238bb6ba0baa06a4ff37a187d18f0184c7603bb708996` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/site-build-v1.log` | `824214503e5cd407b28f922ca1bcc6a6ad318f7722d83999004012f70c771914` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/site-build-v2-exit.json` | `024296de549e9e05b2c43ee5375250f30098b9cd74d6a774cd5f8784aa872e40` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/site-build-v2.log` | `9fc5a0417826757f163837056b54fd578abd1ef0f0dbe60464478889d38cff5e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/site-build-v3-exit.json` | `4ab75e0dc204e465488f9a872af11be5b86c401c4fecb53b1670ea0774287776` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/site-build-v3.log` | `8829ceb9c9959e39cc0314cb14de60f8e3ba0ccf10380982e6588704008f7249` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/site-build-v4-exit.json` | `30b53766bec0a29f0d7778421a6dd01f07e11313a02a67c200cf3441e561dc3e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/site-build-v4.log` | `b8b2f8a2d3800611c5cf9f8564e610e4ac9c62fb5288928673c1b8e6447fe8f4` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/site-check-v1-exit.json` | `cb2e9c946a9690b82c5d37562558a26134da17c6b6ebae9ef7eb76818ce0464b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/site-check-v1.log` | `de7552b0a9abf4db9ff51cb55d6d67aea8b7a05a6de597232affca41b86ef673` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/site-check-v2-exit.json` | `9be6fd506f5209db80d13953805baf98025d7636db1592bde24c75f1e31d0de2` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/site-check-v2.log` | `67af8b9fec6355c191f4b969b25a90bb4f31f56cd9d6416709a82035cc6a4f1f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/site-check-v3-exit.json` | `e84189ab1d0d41db73928674184f334bd1d4e545e6700a4945a4f5f6aa7d5dec` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/site-check-v3.log` | `67af8b9fec6355c191f4b969b25a90bb4f31f56cd9d6416709a82035cc6a4f1f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/site-check-v4-exit.json` | `4a39c0b4117b9a69c487ea58ecc35dad15c987f3b2522f0061d5837db4f6ff99` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/site-check-v4.log` | `67af8b9fec6355c191f4b969b25a90bb4f31f56cd9d6416709a82035cc6a4f1f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/site-tools-before-first-use-v1.json` | `dedca88f7efd1e564f00980d38970520359747a14f8bf294af16db6eadd13043` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/snapshots/catalog-scope-v6-build_site.py.raw` | `f6cface76e1393fef186ab63ae521c14af11878a0b892b8acfbef390ae380a4f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/snapshots/contribution-before-catalog-v6.raw` | `6fdd72389db42fe44a08419c3fc93dd812796a3a04b3cfe6e94f569e1a66fa2d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/snapshots/reader-feature-before-v2-highlights.raw` | `503f8b26c966582a5775cfaf62ccc998de18451cce64e8577b37ed90abcbbe16` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/snapshots/source-card07-before-layout-v3.json` | `8b403292c868d2254dc63be869a5f0084aed8832ccda5b051dfaacfa0064cc76` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/source-card-01-v2.png` | `09d3eede08e197369fdcf321b7def8669dd8f51a332fc36ffd534feeaa62dfa6` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/source-card-01-v3.png` | `09d3eede08e197369fdcf321b7def8669dd8f51a332fc36ffd534feeaa62dfa6` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/source-card-01-v4.png` | `09d3eede08e197369fdcf321b7def8669dd8f51a332fc36ffd534feeaa62dfa6` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/source-card-02-v2.png` | `f5ccfd05694afce833033dc62184c86b002538f5af2e92f26d3dcc271a379ac7` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/source-card-02-v3.png` | `f5ccfd05694afce833033dc62184c86b002538f5af2e92f26d3dcc271a379ac7` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/source-card-02-v4.png` | `f5ccfd05694afce833033dc62184c86b002538f5af2e92f26d3dcc271a379ac7` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/source-card-03-v2.png` | `6515e57728082e8c526ce1ac2b651a006ebe2a4a3d4f58c748f1dce3a473a14e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/source-card-03-v3.png` | `6515e57728082e8c526ce1ac2b651a006ebe2a4a3d4f58c748f1dce3a473a14e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/source-card-03-v4.png` | `6515e57728082e8c526ce1ac2b651a006ebe2a4a3d4f58c748f1dce3a473a14e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/source-card-04-v2.png` | `e42bcda140bf7419f14d139a15aefdbc39bcddb8503c319c79b0e7ba246341cb` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/source-card-04-v3.png` | `e42bcda140bf7419f14d139a15aefdbc39bcddb8503c319c79b0e7ba246341cb` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/source-card-04-v4.png` | `e42bcda140bf7419f14d139a15aefdbc39bcddb8503c319c79b0e7ba246341cb` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/source-card-05-v2.png` | `eb153766ab9d023aa84305416cee11d66f2b13a2c60bfe3ba51d978f311aae94` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/source-card-05-v3.png` | `eb153766ab9d023aa84305416cee11d66f2b13a2c60bfe3ba51d978f311aae94` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/source-card-05-v4.png` | `eb153766ab9d023aa84305416cee11d66f2b13a2c60bfe3ba51d978f311aae94` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/source-card-06-v2.png` | `e7443398735f003f824306a003a090b5bdb00c56322f8aad8ac6a0f1a414471c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/source-card-06-v3.png` | `e7443398735f003f824306a003a090b5bdb00c56322f8aad8ac6a0f1a414471c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/source-card-06-v4.png` | `e7443398735f003f824306a003a090b5bdb00c56322f8aad8ac6a0f1a414471c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/source-card-07-v3.png` | `5a8343d6548b1cade7eca40d2edf5f2a5f535edd7647c535ddb4ae54d1e9ac5e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/source-card-07-v4.png` | `5a8343d6548b1cade7eca40d2edf5f2a5f535edd7647c535ddb4ae54d1e9ac5e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/source-formula-layout-repair-v3.json` | `f959b7027e53d0931b66e9b1e70be0f29e6d6485d41568e00ff2b29e2490e692` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/source-layout-candidate-event-v3-exit.json` | `6ffefe764fe8408ad1a8fad52686d62156e5112e689c799dfd8be8484a6bfd2f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/source-layout-candidate-event-v3.log` | `bced31299a3bbf8384a0711f8bff03be3978192866e36c0f1541251ef8e3fc8b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/source-layout-repair-event-v3-exit.json` | `9484bebd0f4073ae86f2ad8c022f7dc954e4f20ff7a639a8a33f8249fa8e10ed` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/source-layout-repair-event-v3.log` | `0b112412eab8a03b452d451676ee7357318ccd6c7de9d154d078380125e9d7f8` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/source-obligations-BODY-overlay-v1.json` | `faedc15dcfadb585e25985b075f2ac3ccdada87148ad0c2584ed6ff7d660b761` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/source-scope-audit-reader-v2.json` | `c56c0183d8e10a38558fa84ce60bae26dc49fb87022dfa99e3f4853f7bed038d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/source-scope-audit-reader-v3.json` | `214c007b9964921afa001d7b224638c87aa5627f08b7e386214c301375f86a6a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/source-scope-audit-reader-v4.json` | `eea2635577a896de1dbc7297319b8ad6b65de7095f45f5495a28b0ed66288afd` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/source-scope-audit-reader-v5.json` | `c2abd6d420d701a7d71912d52cce27d1242341cbe32a049129b2341e9b071376` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/source-scope-audit-v1.json` | `0d4bb19dd24940eb435deca5d665b2489071a7675d28f6e06ef87d14e453ec8e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/source-scope-reader-v2-exit.json` | `14271559ca034529571177dfe6e8d02ac36bf092264872bbc34929f62d64f80a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/source-scope-reader-v2.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/source-scope-reader-v3-exit.json` | `90c4c37e1559192a0a4012bccc3426e8862ee73b67637b518962dd478cf9c209` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/source-scope-reader-v3.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/source-scope-reader-v4-exit.json` | `4ff9a9f7e70b4985c42199daa0c11cef99650d6dcaa2df12c5a62b3e6bf26a15` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/source-scope-reader-v4.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/source-scope-reader-v5-exit.json` | `52318a42036c51e69603c3884547f171b03e98e70a9357d8b7d6f5bc06990e16` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/source-scope-reader-v5.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/source-scope-v1-exit.json` | `8d994713753f63b9e831296f1707f5196f50598ea57f95ce52d88bf8272536c7` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/source-scope-v1.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/source-site-gates-v1.py` | `1cbcecdf35f822b9216910311ed255d18fa2cf73416d213d56fd99b22e922bca` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/stabilize-catalog-scope-v6.py` | `1c79e10f8f9cf989be5207c3ca1f355d1e5d656eda72e0c8a1304ff95bce17b2` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/task-shadow-v1.py` | `65a1383af35e1ba8753f852ebc1b6bfb99ffc392ac9a1c16cd1df5e31a53c4ac` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/task-shadow-v2.py` | `2335a84eeb817df00bff59507d2436bc81567843b488dfd80859b4c871147d71` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/verify-registry-v1.py` | `f2416020085e808700c804a0199b42625cdaa06e7fd2fa40a67d60e75515f3fd` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/verify-registry-v2.py` | `1a52ec5940a6c2339786f6e80361cb5ea1bd04cf818009a9d299ad691b80d897` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/verify-registry-v3.py` | `408eebac8683c3b7c105377f72ce9f418800def9f20540f3f3baba4e7d2c548b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/verify-registry-v4.py` | `9f87ac4651ca47bacf104990b07e579fc91b5d20748e9fc2646f9e06c8b90e99` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/verify-registry-v5.py` | `425ecdee57908f5c7531eef27cf57f58ae8ccd2445a9dc87d016aa161e930409` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/worked-example-v3.png` | `5dc1cbc7f9e87375b8fc9784dbb7d31ae5714cb9d7e0608ede78229b34d2e197` |
| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-state-20261007/worked-example-v4.png` | `5dc1cbc7f9e87375b8fc9784dbb7d31ae5714cb9d7e0608ede78229b34d2e197` |
| `BanditRLProof.lean` | `55cfcdaf2b28f0e55ef4326060c861919e9dc3f69fbaac31c6563e4d16135e67` |
| `Tests.lean` | `9424c8414e33b800b2442f8662dda46eee1d9734d78334db61aa937f69f0b614` |
| `website/content/readings.json` | `5bce96f6df03b9fe28444951145778272a37aea9b73251e29d149e12c4798c82` |
| `website/content/highlights.json` | `7d2351d5eecd66ff9440eac11b00f65affcf8fa322d259db112f310da60a4472` |
| `website/content/chapters.json` | `7698a62f73c6741e08d033aea3a583d3db0e52f2c23e75ea8c33f79d9dbe77b4` |
| `research-wiki/contribution-contracts/online-ftl-state-20261007.json` | `737d031685a90761a4e49db64e738ecba707dc731dd3e122880c1b1af25f02b5` |
| `website/scripts/build_site.py` | `4fe18b8b9a543ff5256a278f49d160424b30ba2185c946f3d6081ad5460ccaff` |
| `website/content/declaration-boundaries.json` | `6806d5fc69f3ebd42814f502f27afc1295369a80d3c0fbb6f7c59f6c57fdbbe9` |
| `tools/test_source_declaration_boundaries.py` | `f9a5e29e6cc4c509b748903ae9b3b5f6c5f4b602598adedb3db5ae9c45731478` |
| `runs\online-ftl-state-20261007\final-reader-inputs-v1.json` | `a7fa15c8a6651c532fd506170fcae9c0dbee6b6956bdb46943fdbf6ab0955e1b` |
| `runs\online-ftl-state-20261007\final-reader-packet-v1.md` | `6e708aad81a4b1f766d80085d20d9d35f68ab40546c8f08c0ee24af42fabf728` |
| `tmp/online-ftl-state-site-v4/books/registry.json` | `55cb2e7315b5d156687a64cbecff84c6114ad8e1338654f4ef1a6541681a6116` |
| `tmp/online-ftl-state-site-v4/chapters/online-foundations/index.html` | `5f14d9493cbe6e32444288eec03f903c1820ff9b29cf1074739722af0bdb98d3` |
| `tmp/online-ftl-state-site-v4/modules/banditrlproof-onlinelearningftlstate/index.html` | `c91b933fd094017ee4a72b5ae7c7de8c010d85904f4e28a5a541da347ae81585` |
