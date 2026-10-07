# FTL state: distinct CONTRACT review

Verdict: **accepted-with-explicit-delta**, restricted to contract stabilization. Actor `/root/source_reviewer`; requested GPT-6 Astra / medium, runtime settings not independently attested. I have prior staged source-review history and am not a blind decoder, external reviewer or human reviewer.

All 157 fixed raw rows were independently hashed without mismatch, including the pinned PDF. Original printed p3/PDF15 and p6/PDF18 images were directly viewed; p4/p5 source text was also read. The source permits any feasible first prediction, whereas its stated regret theorem fixes one half. The recursive count/value implementation is a faithful sufficient-statistic refinement; no executable or fixed-bit complexity claim follows.

The four existing Mean proofs use actual square decomposition/nonnegative residual, finite-sum feasibility and positive-count uniqueness. Their inspection here is for contract consistency. The nineteen neutral propositions elaborate and four existing type identities compile; this does not prove the nine new production targets or six new tests.

No blocking mathematical or metadata repair identified. Source extensions and evidence boundaries are explicit below. The inherited enumeration-pending sentence is historical conservative metadata, not evidence of current closure; future reader status must distinguish it from the separately accepted prior repair.

Native API boundary: `lean_declaration_header` searches for a top-level `:=` and does not recognize equation-style recursive clauses. It must not be used to claim a valid recursive ftlState definition fence. Preserve its complete raw definition and require actual compiled definition identities/types/kernel checks. Supported theorem headers can retain native fences. This is an evidence requirement, not a change to the definition.

## Per-target seven-slot comparison

### N01 — BanditRL.OnlineLearning.empiricalMean_decomposition
Verdict: accepted-with-explicit-delta
- **objects**: Real empirical mean and squared prefix loss
- **quantifiers**: Every real stream, positive n, real u
- **assumptions**: n>0; no interval premise
- **conclusion**: Exact loss decomposition around mean
- **constants_indices**: Residual n*(u-mean)^2; range n
- **information_order**: Hindsight prefix including all n observations
- **source_delta_boundary**: Algebraic producer generalizes interval source; not causal action

### N02 — BanditRL.OnlineLearning.empiricalMean_minimizes
Verdict: accepted-with-explicit-delta
- **objects**: Same prefix squared losses
- **quantifiers**: Every stream, n>0, real comparator
- **assumptions**: Positive n only
- **conclusion**: Mean minimizes over all real comparators
- **constants_indices**: No additive error or rate
- **information_order**: Hindsight minimizer
- **source_delta_boundary**: Stronger ambient comparison; interval membership supplied separately

### N03 — BanditRL.OnlineLearning.empiricalMean_mem
Verdict: accepted-with-explicit-delta
- **objects**: Real empirical mean
- **quantifiers**: Every stream and positive n
- **assumptions**: All i<n labels in closed [0,1]
- **conclusion**: Mean belongs to closed [0,1]
- **constants_indices**: Both endpoints admitted; n=0 excluded
- **information_order**: Only observed prefix needed
- **source_delta_boundary**: Source feasibility producer, not a global stream restriction

### N04 — BanditRL.OnlineLearning.empiricalMean_unique
Verdict: accepted-with-explicit-delta
- **objects**: Mean and arbitrary real u
- **quantifiers**: Every stream,n>0,u
- **assumptions**: Loss(u)<=loss(mean)
- **conclusion**: u=mean
- **constants_indices**: Positive n essential for uniqueness
- **information_order**: Hindsight prefix
- **source_delta_boundary**: Uniqueness refinement, not extra source assumption

### N05 — BanditRL.OnlineLearning.empiricalMean_succ
Verdict: accepted-with-explicit-delta
- **objects**: Real prefix means
- **quantifiers**: Every real stream and natural t
- **assumptions**: None
- **conclusion**: Exact successor update
- **constants_indices**: Denominator real t+1>0; includes t=0
- **information_order**: Uses prefix mean and current y(t)
- **source_delta_boundary**: All-real all-time recurrence; empty mean is 0, not arbitrary initial

### N06 — BanditRL.OnlineLearning.ftlPredict_prefix
Verdict: accepted-with-explicit-delta
- **objects**: ftlPredict for two streams
- **quantifiers**: Every initial,y,z,t
- **assumptions**: Equal labels for every i<t; same initial
- **conclusion**: Equal predictions
- **constants_indices**: Includes t=0
- **information_order**: Strict past, no current/future dependence
- **source_delta_boundary**: Fixed exogenous initial; not a guarantee for future-dependent external parameter choice

### N07 — BanditRL.OnlineLearning.ftlPredict_mem
Verdict: accepted-with-explicit-delta
- **objects**: ftlPredict interval membership
- **quantifiers**: Every initial,y,t
- **assumptions**: Initial in [0,1] and all i<t labels in [0,1]
- **conclusion**: Prediction feasible
- **constants_indices**: t=0 retains initial; positive t uses mean
- **information_order**: Strict past only
- **source_delta_boundary**: Source-admissible general initialization; no current label premise

### N08 — BanditRL.OnlineLearning.ftlPredict_half
Verdict: accepted-with-explicit-delta
- **objects**: General predictor and old meanPredict
- **quantifiers**: Every real stream,t
- **assumptions**: Initial specialized to 1/2
- **conclusion**: Exact predictor equality
- **constants_indices**: All t including zero
- **information_order**: Same stream and time
- **source_delta_boundary**: Bridge to existing half-initial source theorem, not new regret rate

### N09 — BanditRL.OnlineLearning.ftlState_first
Verdict: accepted-with-explicit-delta
- **objects**: Whole recursive count/value state
- **quantifiers**: Every real initial and stream
- **assumptions**: None
- **conclusion**: State at 1=(1,y(0))
- **constants_indices**: First denominator 1 cancels initial
- **information_order**: One observed label
- **source_delta_boundary**: Arbitrary-real structural identity, not admissibility for outside initial

### N10 — BanditRL.OnlineLearning.ftlState_eq_predict
Verdict: accepted-with-explicit-delta
- **objects**: Whole state and predictor
- **quantifiers**: Every real initial,stream,t
- **assumptions**: None
- **conclusion**: State=(t,ftlPredict initial y t)
- **constants_indices**: t=0=(0,initial)
- **information_order**: Actual recurrence must produce identity
- **source_delta_boundary**: Sufficient-statistic implementation theorem; no supplied state oracle

### N11 — BanditRL.OnlineLearning.ftlState_prefix
Verdict: accepted-with-explicit-delta
- **objects**: Two whole count/value states
- **quantifiers**: Every initial,y,z,t
- **assumptions**: Same strict prefix and same initial
- **conclusion**: Whole states equal
- **constants_indices**: Zero horizon included
- **information_order**: Strict past for count and value
- **source_delta_boundary**: Causal structural refinement, not only equality of displayed mean

### N12 — BanditRL.OnlineLearning.ftlState_mem
Verdict: accepted-with-explicit-delta
- **objects**: State value coordinate
- **quantifiers**: Every initial,stream,t
- **assumptions**: Feasible initial and strict-past labels
- **conclusion**: Second coordinate in [0,1]
- **constants_indices**: Count not constrained to interval; zero included
- **information_order**: No current/future label hypothesis
- **source_delta_boundary**: Source feasibility follows actual state identity

### N13 — BanditRL.OnlineLearning.ftlState_half
Verdict: accepted-with-explicit-delta
- **objects**: State and old half predictor
- **quantifiers**: Every stream,t
- **assumptions**: Initial=1/2
- **conclusion**: Whole state=(t,meanPredict y t)
- **constants_indices**: All times
- **information_order**: Same actual stream
- **source_delta_boundary**: Exact specialization, no general-initial quarter guarantee

### N14 — FTLStateProbe.initial_and_first
Verdict: accepted-with-explicit-delta
- **objects**: Two endpoint initial states, constant-one stream
- **quantifiers**: Closed test proposition
- **assumptions**: Specified initial 0 and 1
- **conclusion**: Distinct zero states; same (1,1) first state
- **constants_indices**: Times 0 and 1
- **information_order**: First observation overwrites initial
- **source_delta_boundary**: Validation only; no new source theorem

### N15 — FTLStateProbe.varying_updates
Verdict: accepted-with-explicit-delta
- **objects**: Probe stream 0,1,1,... and initial 3/4
- **quantifiers**: Closed test proposition
- **assumptions**: Specified data
- **conclusion**: States (2,1/2) and (3,2/3)
- **constants_indices**: Counts 2 and 3
- **information_order**: Initial is not an extra observation
- **source_delta_boundary**: Nonconstant validation of genuine running mean

### N16 — FTLStateProbe.current_target_after_prediction
Verdict: accepted-with-explicit-delta
- **objects**: Constant-zero and probe streams
- **quantifiers**: Closed test proposition
- **assumptions**: Same initial 0 and same prefix at t=1
- **conclusion**: Same prediction state before differing current target, unequal next states
- **constants_indices**: Times 1 and 2
- **information_order**: Current target acts only after prediction
- **source_delta_boundary**: Validation of causal order, not current-input invariance after update

### N17 — FTLStateProbe.feasibility_and_outside
Verdict: accepted-with-explicit-delta
- **objects**: Feasible and outside initial states
- **quantifiers**: Closed test proposition
- **assumptions**: Specified initial 1 or 2, probe labels
- **conclusion**: Feasible later value; outside value at zero; first updated value 0
- **constants_indices**: Initial 2 outside [0,1]
- **information_order**: First observation restores value in this fixture
- **source_delta_boundary**: Outside initialization is ambient validation, not source-admissible learner

### N18 — FTLStateProbe.half_state_regret
Verdict: accepted-with-explicit-delta
- **objects**: Half state cumulative loss and final mean comparison
- **quantifiers**: Closed two-round test proposition
- **assumptions**: Specified probe and half initialization
- **conclusion**: Actual regret 3/4 and refined upper bound
- **constants_indices**: T=2; quarter plus later harmonic term
- **information_order**: Same trajectory and hindsight comparator
- **source_delta_boundary**: Must later invoke actual old refined producer; no general-initial rate

### N19 — FTLStateProbe.general_initial_not_quarter
Verdict: accepted-with-explicit-delta
- **objects**: Initial-one zero-label first-round loss
- **quantifiers**: Closed test proposition
- **assumptions**: Feasible initial 1 and label 0
- **conclusion**: First loss 1>1/4
- **constants_indices**: First round only
- **information_order**: Prediction before label
- **source_delta_boundary**: Source-admissible counterexample to extending half-only quarter bound

## Complete owned definitions

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

## Stable future reader requirements

R1: Attribute arbitrary feasible initialization to printed p3 and the running-summary construction to p6; distinguish the p4/p5 half-initial theorem. Nine new proof declarations are not nine printed source results.
R2: Show the complete predictor, local count/value step and recursive state definitions. Distinguish all-real algebraic extensions from source feasibility requiring initial and strict-past labels in [0,1].
R3: Explain state(0)=(0,initial), empty empirical mean=0, and the first update cancelling initial. Preserve all-time successor identity with positive real denominator t+1 and all zero/one-time boundaries.
R4: Explain whole-state strict-prefix equality with the same fixed initial parameter; prediction precedes current-label update. Do not infer causality for an externally future-dependent choice of initial.
R5: Connect the actual state identity to existing empirical-mean decomposition, minimization, feasibility and uniqueness producers. Separate hindsight prefix argmins from causal predictions; no supplied argmin/state/regret oracle.
R6: State exact half specialization and retain the half-only quarter bound. Explain all six validation fixtures, including changing means, current-target perturbation, outside-initial ambient test and feasible initial-one counterexample.
R7: Limit running-summary claims to mathematical noncomputable exact-real count/value state. No fixed-bit memory, executable implementation or runtime certificate. Validate complete formulas, current HTML and actual pixels at FINAL; preserve shared definitions and registry ownership.
R8: Keep stages and counts explicit: four retained Mean proofs, nine planned new public proofs, three definitions and six validation proofs; no current BODY acceptance. Sixteen source items are not a proof total (null); W/V mapping, logarithmic lower-bound audit, eight main gaps and remaining chapters/appendices remain required. Distinguish inherited historical ledger pending labels from current decisions. For equation-style ftlState use complete raw-definition hashes and actual compiled definition identities/types/kernel evidence, not an unsupported native := header-extractor claim.

## Scope and remaining work
Only two source subobligations are addressed: general initialization and actual recursive summary. Sixteen required source items remain distinct from a null proof-leaf total. The W/V domain mapping and logarithmic-unavoidability source/lower-bound audit remain required, as do other maintext, appendices and chapters. PR188 is an unmerged stacked dependency, not main integration. BODY, actual producer VALUE checks, combined root/Tests/harness, reader/site/pixels, immutable acceptance and delivery remain future gates. No Chapter or whole Goal acceptance.

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
| `runs\online-ftl-state-20261007\source-contract-inputs-v1.json` | `20468f80cc431359a08b0a621a2427f47fd427c838267a7cea6222e5e9402211` |
| `tools/abrl_lifecycle.py` | `7615541e66a372e939ea2d18684ce78a8f3d8f1202894840ef7fdfdc703c4310` |
| `runs\online-ftl-state-20261007\source-contract-packet-v1.md` | `a4ef3dda8370dcd60a48d7899ee98a61ae248d41be243d9f7dcf4814b9157b5b` |
