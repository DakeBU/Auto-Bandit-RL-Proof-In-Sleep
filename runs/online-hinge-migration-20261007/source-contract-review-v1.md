# Example2.27 hinge CONTRACT source review v1

**Verdict: accepted-with-explicit-delta — contract stabilization only.** No mathematical/header repair required. Nine future reader obligations below remain; this is not BODY or package acceptance.

{"task": "/root/source_reviewer", "role": "distinct automated source reviewer", "requested_model": "GPT-6 Astra", "requested_reasoning": "medium", "runtime_model_attested": false, "human_review": false, "external_model_review": false, "history": "This actor has prior staged source reviews, including historical hinge-related work. No claim of erased history or source blindness. Current restricted decoder is /root/neutral_two_function_decoder."}

## Independent source and integrity checks

Rehashed every one of 211 fixed raw inputs; all matched. Added the manifest itself for 212 reviewed-file rows. Verified all 15 actual declaration-header hashes, two complete owned-definition hashes and seven exact borrowed definition bodies/owner hashes. Independently checked all 23 required actual value-dependency pairs in the selected 15-node graph (13 proofs, two definitions; 1367 direct type/value occurrences). This graph and retained focused build (3319 jobs, with replay/linter notice) are readiness evidence, not fresh BODY/kernel/combined acceptance. No compiler was run by this reviewer.

Pinned PDF independently read via pypdf page29 (physical30/printed18) and the bound actual page PNG viewed. Raw PDF SHA256: `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17`. The original gives one Example2.27 with three cases and exactly the inclusive alpha interval. The source does not exclude zero z or positive-dimension-zero boundary. No algorithm, rate or selection semantics is present.

Current neutral reconstruction and actual compiled types agree: only L06/L13 require finite dimension. P/D/Q accept arbitrary carriers; C requires AddCommGroup and real Module; M arbitrary E with finite nonempty index; S/U retain real inner structure. Generic S is wider than the proper-function source convention, but actual hinge/affine finite embeddings make that delta harmless for this source instance.

Existing public bodies were read for contradictions and route feasibility only. The affine test at x+g-a produces uniqueness, properness has an actual finite witness, and maximum qualifications are produced; no claimed conclusion is a supplied premise. Bool activity and ordinary pair hull plausibly discharge the frozen terminal. This does not substitute for the separately required BODY review. Whole five scalar canary bodies read: full strict sets, full [-1,0], genuine -1/2 outside active union, rejection +1 and all-x zero z; no 2D case.

## Per-proof seven-slot comparisons

### BanditRL.OnlineConvex.affine_subdifferential

accepted-with-explicit-delta; supporting library refinement, not a separately printed source result.

`theorem affine_subdifferential (a : E) (b : ℝ) (x : E) : SourceSubdifferential (fun y => ((inner ℝ a y + b : ℝ) : EReal)) x = {a}`

- **objects_spaces**: E with NormedAddCommGroup and InnerProductSpace over real; EReal values and ambient support vectors. Finite dimension only when listed in assumptions.
- **quantifiers**: all a:E,b:real,x:E; membership tests every ambient y
- **assumptions**: none beyond intrinsic real inner structure
- **conclusion**: S(y -> coe(inner a y+b),x) = {a}
- **constants_normalization**: unit inner coefficient; arbitrary real intercept b
- **information_probability**: Deterministic convex analysis; no algorithm, regret, feedback, measurable/computable selection or probabilistic claim.
- **boundaries**: Zero slope, zero dimension and every query included; no FD or completeness premise.

### BanditRL.OnlineConvex.affine_proper

accepted-with-explicit-delta; supporting library refinement, not a separately printed source result.

`theorem affine_proper (a : E) (b : ℝ) : SourceProper (fun y => ((inner ℝ a y + b : ℝ) : EReal))`

- **objects_spaces**: E with NormedAddCommGroup and InnerProductSpace over real; EReal values and ambient support vectors. Finite dimension only when listed in assumptions.
- **quantifiers**: all a:E,b:real
- **assumptions**: none beyond intrinsic real inner structure
- **conclusion**: affine expression has no bottom anywhere and has an actual finite real witness
- **constants_normalization**: arbitrary b, witness can be y=0 and value b
- **information_probability**: Deterministic convex analysis; no algorithm, regret, feedback, measurable/computable selection or probabilistic claim.
- **boundaries**: E has zero and is inhabited; SourceProper itself is a predicate on arbitrary carriers. Not a convexity assertion.

### BanditRL.OnlineConvex.affine_convex

accepted-with-explicit-delta; supporting library refinement, not a separately printed source result.

`theorem affine_convex (a : E) (b : ℝ) : IsConvexExtended (fun y => ((inner ℝ a y + b : ℝ) : EReal))`

- **objects_spaces**: E with NormedAddCommGroup and InnerProductSpace over real; EReal values and ambient support vectors. Finite dimension only when listed in assumptions.
- **quantifiers**: all a:E,b:real
- **assumptions**: none beyond intrinsic real inner structure
- **conclusion**: real-height epigraph of embedded affine expression is convex
- **constants_normalization**: nonnegative weights, including endpoints, sum to one
- **information_probability**: Deterministic convex analysis; no algorithm, regret, feedback, measurable/computable selection or probabilistic claim.
- **boundaries**: No FD, strict convexity, closedness or loss differentiability premise.

### BanditRL.OnlineConvex.affine_continuous

accepted-with-explicit-delta; supporting library refinement, not a separately printed source result.

`theorem affine_continuous (a : E) (b : ℝ) (x : E) : ContinuousAt (fun y => ((inner ℝ a y + b : ℝ) : EReal)) x`

- **objects_spaces**: E with NormedAddCommGroup and InnerProductSpace over real; EReal values and ambient support vectors. Finite dimension only when listed in assumptions.
- **quantifiers**: all a:E,b:real,x:E
- **assumptions**: none beyond intrinsic real inner structure
- **conclusion**: ContinuousAt of EReal-embedded affine expression at x
- **constants_normalization**: no modulus or bound
- **information_probability**: Deterministic convex analysis; no algorithm, regret, feedback, measurable/computable selection or probabilistic claim.
- **boundaries**: Ambient EReal continuity at every query; no FD or derivative premise.

### BanditRL.OnlineConvex.hinge_max_identity

accepted-with-explicit-delta; supporting library refinement, not a separately printed source result.

`theorem hinge_max_identity (z : E) : SourceFiniteMax (hingeFamily z) = sourceHinge z`

- **objects_spaces**: E with NormedAddCommGroup and InnerProductSpace over real; EReal values and ambient support vectors. Finite dimension only when listed in assumptions.
- **quantifiers**: all z:E; equality of functions therefore every evaluation x
- **assumptions**: none beyond intrinsic real inner structure
- **conclusion**: SourceFiniteMax (hingeFamily z) = sourceHinge z
- **constants_normalization**: Bool false=0; true=1-inner z x
- **information_probability**: Deterministic convex analysis; no algorithm, regret, feedback, measurable/computable selection or probabilistic claim.
- **boundaries**: Both sign regimes and tie; actual finite nonempty Bool family. Not arbitrary empty maximum.

### BanditRL.OnlineConvex.hinge_subdifferential_hull

accepted-with-explicit-delta; supporting library refinement, not a separately printed source result.

`theorem hinge_subdifferential_hull [FiniteDimensional ℝ E] (z x : E) : SourceSubdifferential (sourceHinge z) x = convexHull ℝ (SourceActiveSubgradientUnion (hingeFamily z) x)`

- **objects_spaces**: E with NormedAddCommGroup and InnerProductSpace over real; EReal values and ambient support vectors. Finite dimension only when listed in assumptions.
- **quantifiers**: all z,x:E; entire support set equality
- **assumptions**: FiniteDimensional real E in addition to intrinsic inner structure
- **conclusion**: S(sourceHinge z,x) = ordinary convexHull real (active component support union)
- **constants_normalization**: exact attaining equality, unweighted maximum
- **information_probability**: Deterministic convex analysis; no algorithm, regret, feedback, measurable/computable selection or probabilistic claim.
- **boundaries**: All queries finite. Properness, convexity and ambient continuity of components are conclusions of affine facts, not extra supplied assumptions. No closed-hull replacement.

### BanditRL.OnlineConvex.hinge_family_support

accepted-with-explicit-delta; supporting library refinement, not a separately printed source result.

`theorem hinge_family_support (z : E) (i : Bool) (x : E) : SourceSubdifferential (hingeFamily z i) x = {if i then -z else 0}`

- **objects_spaces**: E with NormedAddCommGroup and InnerProductSpace over real; EReal values and ambient support vectors. Finite dimension only when listed in assumptions.
- **quantifiers**: all z:E,i:Bool,x:E; support tests every ambient y
- **assumptions**: none beyond intrinsic real inner structure
- **conclusion**: S(hingeFamily z i,x) = {if i then -z else 0}
- **constants_normalization**: Boolean true slope -z, false slope 0
- **information_probability**: Deterministic convex analysis; no algorithm, regret, feedback, measurable/computable selection or probabilistic claim.
- **boundaries**: Valid for inactive as well as active components; no activity premise, FD or choice oracle.

### BanditRL.OnlineConvex.hinge_family_false

accepted-with-explicit-delta; supporting library refinement, not a separately printed source result.

`theorem hinge_family_false (z x : E) : hingeFamily z false x = ((0 : ℝ) : EReal)`

- **objects_spaces**: E with NormedAddCommGroup and InnerProductSpace over real; EReal values and ambient support vectors. Finite dimension only when listed in assumptions.
- **quantifiers**: all z,x:E
- **assumptions**: none beyond intrinsic real inner structure
- **conclusion**: hingeFamily z false x = coe(0:real)
- **constants_normalization**: embedded zero, not bottom
- **information_probability**: Deterministic convex analysis; no algorithm, regret, feedback, measurable/computable selection or probabilistic claim.
- **boundaries**: No claim that this index is always active.

### BanditRL.OnlineConvex.hinge_family_true

accepted-with-explicit-delta; supporting library refinement, not a separately printed source result.

`theorem hinge_family_true (z x : E) : hingeFamily z true x = ((1 - inner ℝ z x : ℝ) : EReal)`

- **objects_spaces**: E with NormedAddCommGroup and InnerProductSpace over real; EReal values and ambient support vectors. Finite dimension only when listed in assumptions.
- **quantifiers**: all z,x:E
- **assumptions**: none beyond intrinsic real inner structure
- **conclusion**: hingeFamily z true x = coe(1-inner z x)
- **constants_normalization**: intercept one and negative sign
- **information_probability**: Deterministic convex analysis; no algorithm, regret, feedback, measurable/computable selection or probabilistic claim.
- **boundaries**: Expression may be negative, zero or positive; this component is not clipped.

### BanditRL.OnlineConvex.hinge_active_negative

accepted-with-explicit-delta; supporting library refinement, not a separately printed source result.

`theorem hinge_active_negative (z x : E) (h : 1 - inner ℝ z x < 0) : SourceActiveSubgradientUnion (hingeFamily z) x = {(0 : E)}`

- **objects_spaces**: E with NormedAddCommGroup and InnerProductSpace over real; EReal values and ambient support vectors. Finite dimension only when listed in assumptions.
- **quantifiers**: all z,x:E followed by negative-margin premise
- **assumptions**: 1-inner z x < 0
- **conclusion**: active support union = {0}
- **constants_normalization**: threshold 1; strict comparison with 0
- **information_probability**: Deterministic convex analysis; no algorithm, regret, feedback, measurable/computable selection or probabilistic claim.
- **boundaries**: Tie excluded; union itself, not a hull or selected vector. No FD.

### BanditRL.OnlineConvex.hinge_active_positive

accepted-with-explicit-delta; supporting library refinement, not a separately printed source result.

`theorem hinge_active_positive (z x : E) (h : 0 < 1 - inner ℝ z x) : SourceActiveSubgradientUnion (hingeFamily z) x = {-z}`

- **objects_spaces**: E with NormedAddCommGroup and InnerProductSpace over real; EReal values and ambient support vectors. Finite dimension only when listed in assumptions.
- **quantifiers**: all z,x:E followed by positive-margin premise
- **assumptions**: 0 < 1-inner z x
- **conclusion**: active support union = {-z}
- **constants_normalization**: negative vector, not margin-scaled vector
- **information_probability**: Deterministic convex analysis; no algorithm, regret, feedback, measurable/computable selection or probabilistic claim.
- **boundaries**: At z=0 this premise holds and the singleton is {0}; no FD.

### BanditRL.OnlineConvex.hinge_active_zero

accepted-with-explicit-delta; supporting library refinement, not a separately printed source result.

`theorem hinge_active_zero (z x : E) (h : 1 - inner ℝ z x = 0) : SourceActiveSubgradientUnion (hingeFamily z) x = {(0 : E), -z}`

- **objects_spaces**: E with NormedAddCommGroup and InnerProductSpace over real; EReal values and ambient support vectors. Finite dimension only when listed in assumptions.
- **quantifiers**: all z,x:E followed by exact tie premise
- **assumptions**: 1-inner z x = 0
- **conclusion**: active support union = {0,-z}
- **constants_normalization**: two endpoints before taking hull
- **information_probability**: Deterministic convex analysis; no algorithm, regret, feedback, measurable/computable selection or probabilistic claim.
- **boundaries**: Premise impossible at z=0; this union omits nontrivial mixtures, so is not the terminal support set. No FD.

### BanditRL.OnlineConvex.example_2_27

accepted-with-explicit-delta; one printed Example2.27 terminal.

`theorem example_2_27 [FiniteDimensional ℝ E] (z x : E) : SourceSubdifferential (sourceHinge z) x = if 1 - inner ℝ z x < 0 then {0} else if 1 - inner ℝ z x = 0 then {g | ∃ α ∈ Icc (0 : ℝ) 1, g = -(α • z)} else {-z}`

- **objects_spaces**: E with NormedAddCommGroup and InnerProductSpace over real; EReal values and ambient support vectors. Finite dimension only when listed in assumptions.
- **quantifiers**: all z,x:E, every candidate g; middle branch exists alpha in closed Icc 0 1; supports quantify all ambient y
- **assumptions**: FiniteDimensional real E; no premise on z,x
- **conclusion**: full S equals {0} for negative margin, all -(alpha smul z) for zero margin, {-z} otherwise
- **constants_normalization**: margin exactly 1-inner z x; alpha includes 0 and 1; else is positive by real trichotomy
- **information_probability**: Deterministic convex analysis; no algorithm, regret, feedback, measurable/computable selection or probabilistic claim.
- **boundaries**: Zero z gives constant loss 1 and positive margin, hence {0}; zero dimension allowed. No nonzero-z, norm bound, supplied support/hull formula or selected-support shortcut.

## Complete owned definitions

### BanditRL.OnlineConvex.sourceHinge

```lean
def sourceHinge (z x : E) : EReal := ((max (1 - inner ℝ z x) 0 : ℝ) : EReal)
```

Full body SHA256: `4b833d1d6228d3101d78955b5a723bbcb57238c4c517aea6d2f767e80886e89f`.
- **objects_spaces**: Intrinsic NormedAddCommGroup E and InnerProductSpace real E; codomain EReal; no FD.
- **quantifiers**: every z,x:E
- **assumptions**: No properness, convexity, continuity, dimension or side condition is a definition parameter.
- **conclusion**: Embedded real max(1-inner z x,0)
- **constants_normalization**: Actual threshold/intercept 1, zero baseline; Bool true is negative slope with intercept one.
- **information_probability**: Pure mathematical construction, no oracle or procedure guarantee.
- **boundaries**: Everywhere finite including z=0; sourceHinge 0 x=1. No empty-domain or improper-input case in these actual definitions.

### BanditRL.OnlineConvex.hingeFamily

```lean
def hingeFamily (z : E) (i : Bool) (y : E) : EReal :=
  ((inner ℝ (if i then -z else 0) y + (if i then 1 else 0) : ℝ) : EReal)
```

Full body SHA256: `59c20a1b48b67c51b5fcd43330322f9e18ef1c835a321809db910cc0ead2e5f0`.
- **objects_spaces**: Intrinsic NormedAddCommGroup E and InnerProductSpace real E; codomain EReal; no FD.
- **quantifiers**: every z:E, i:Bool, y:E
- **assumptions**: No properness, convexity, continuity, dimension or side condition is a definition parameter.
- **conclusion**: Embedded affine inner(if i then -z else 0,y)+(if i then 1 else 0)
- **constants_normalization**: Actual threshold/intercept 1, zero baseline; Bool true is negative slope with intercept one.
- **information_probability**: Pure mathematical construction, no oracle or procedure guarantee.
- **boundaries**: Everywhere finite including z=0; sourceHinge 0 x=1. No empty-domain or improper-input case in these actual definitions.

## Required future reader corrections

- R1: Clarify source-card guarantee and boundary notation: z=0 is allowed by the full result but has margin 1 and constant loss 1; it never belongs to the zero-margin branch. Current worked example gets this right; remove the ambiguous trailing phrase boundary segment, including z=0.
- R2: Give the sourceHinge definition highlight its own construction and exact intrinsic norm/inner binders, with no FD or theorem proof flow attributed to the definition. Describe the second complete owned Bool-family definition in the reader/module route without adding invented premises.
- R3: Make helper versus source scopes explicit: only hull and terminal carry FD; affine/support/activity helpers retain intrinsic real inner structure. Coordinate-free source specialization is not a separately certified isometry/functor.
- R4: Disclose generic SourceSubdifferential admits arbitrary EReal inputs whereas source Definition2.20 uses proper functions; both actual affine components and hinge are globally finite/proper so this instance has no outside-domain query. Keep borrowed P/D/Q, C, M, S/U binder distinctions.
- R5: Attribute one printed Example2.27 with three cases; twelve helper proofs and two definitions are library constructions, not thirteen source results. Make each existing highlight declaration-specific rather than reuse terminal proof prose.
- R6: Preserve full both-directions equality, global all-y support, ordinary hull, alpha endpoints and genuine mixture. Show branch conditions with the terminal highlight/formula, and verify actual expanded rendered source formula during FINAL rather than infer correct pixels from JSON.
- R7: Preserve producer explanation: affine uniqueness via y=x+g-a, actual proper/convex/finite/continuous components, actual Bool maximum, exact active cases and pair hull. Distinguish curated four-link route from 23 selected proof-value checks/full registry.
- R8: State exact five scalar canaries: three full branch equalities, mixture-and-rejection conjunction, and all-x zero-vector case. Do not claim 2D certification, new tests, or a z=0 boundary instance.
- R9: Update current-stage gate/status and remaining scope at integration using actual new evidence. Historical focused/root/Tests claims are not this migration CONTRACT acceptance. Preserve four highlights/four curated links/three notation entries/one source card/fifteen shared declarations and other Book subtrees; next2.28, nine Chapter1 gaps, Chapter2 and whole Goal remain required.

## Repairs and boundary

Required mathematical repairs: none. Required metadata repairs to frozen contract: none. Reader issues above are explicit integration obligations, not authorization to silently change frozen mathematics. Unused API v1 and pre-use namespace qualification v2 plus read-only lookup diagnostics remain historical evidence; missing-file outputs are not gate passes. Existing bodies, old contracts and old reviews do not confer current acceptance.

Read scope: all listed raw inputs were read and hashed for integrity; semantic examination focused on the actual source page, public full module, complete five-canary file, frozen headers/contexts, actual types/APIs, neutral reconstruction, selected graph and current hinge reader. Administrative scripts/journals/retrieval inventories are integrity/context evidence, not blanket independent acceptance of their contents or unrelated declarations.

Remaining: fresh BODY/kernel/native guards, combined root/Tests/harness, reader changes, generated site/expanded formulas, registry/pixels, FINAL, immutable package and real PR delivery. Chapter2 total remains null/incomplete, whole Goal active; no merge, deployment, live status or retirement accepted.

## Exact raw reviewed inventory

| Path | SHA256 |
|---|---|
| `.agents/skills/bandit-semantic-roundtrip/SKILL.md` | `7ee7b72b8a84ab954966dc13900952c3439bd8d4e97877b622c1ca0a7aa85477` |
| `BanditRLProof.lean` | `351d5238e97cf54ae4c5f65a7e82cabc40ac7eb6f18c9e64e89e27a6610cb9c6` |
| `BanditRLProof/OnlineClosedProper.lean` | `c66f00c33b45fb8a0e11583eeadf506e176c16166ce2af02f41f0674507cebe7` |
| `BanditRLProof/OnlineConvexExtended.lean` | `bd30bb95a46ccdc3f6d25f808c175af5fee71d075c2b46ffcf6508f15f1ed66a` |
| `BanditRLProof/OnlineHinge.lean` | `118d28177c11b0ff113fba5ab34a6bbd9190fee5fb05af644b7b2207c05b020b` |
| `BanditRLProof/OnlineSubgradientBasic.lean` | `af3d3f56e4a64cd8adbe47368caf5382e63b428f01da29a121c28c8014f352a5` |
| `BanditRLProof/OnlineSubgradientMax.lean` | `9efd6831768ce1cdf494ec051aeb14c9a35b87669fb203cdef031cafd94de9c2` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/00_context.md` | `32c8ab5a8ac8a2c3596a42b44b36e356a7dab609523f6ad98768393b8b8b41e9` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/10_upper_director-v1.md` | `1bc164212cdeb3c0818b6f8bf7521fecd8d07ae559bf3d51552e735625f5b462` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/20_architect-v1.md` | `e2b1e8c3fe8bfdb403bc73825ab2e4280a369ee89a05cb593cf066fcfb3b93f2` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/API-pre-use-qualification-v2.json` | `b4f95a0d5d22bc983351f3aaba91cda007262757fb6353d3ff3cedbff7eaeb52` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/actual-types-v1-01-exit.json` | `9ddce452a7eb742a7c2e19620fc7899bad4ca7b946d84b057acae3d68625f231` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/actual-types-v1-01.log` | `a63efa0dc3740764d64547e8121545955054e2d04e8280e90d2df37736027220` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/authoritative-private-workflow-binding-v1.json` | `2b9c630b81b9b524476e56fa8727edbdfa31404c8e396c6a8788a515f69fbe7e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/blind-generated-before-use-v1.json` | `d715958a825ba2fcb6912f0208d4a43921aac1fba628fc16a773beab0dcafc8d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/blind-packet-v1.md` | `6b1ceb7e8fe57c8eb88289caa20fb25a94628fb3dc14ef7419d60d8c0bc3784e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/blind-receipt-v1.json` | `fd5dda5793c653ce5a8441b3314f8b1c943bd5ff0249f4bc9eedd3abc18c5b85` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/blind-reconstruction-v1.md` | `026b70f4cca1ef86030360835cca00f3e1c4df3ef5ac0e7d7f8d6ab2d85c2c2f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/body-prefix-helpers-before-use-v1.json` | `abf78a50dec1aed480b34dd64f20f6d8f27213e9529b6e2e4f6d93906d09bcd4` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/bootstrap-before-use-v1.json` | `b14ae4c14438da1822e055b5409a1929e627c8096faff55bb418ee62057f054e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/bootstrap-v1.py` | `9c519feb17850e41785384fb5906f8da298bd53eb836f4b5cd2a63951ec73556` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/common_v2.py` | `bb90cae0fe035a60e7e2339aba12a5dca1fa0d69d98f30abd8fe9102c216cb0b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/compiled-ready-graph-v1-01-exit.json` | `2073f508da267d6ffcf8b46f5a0d66a07ec06fcce320c472e223788fe01e95c6` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/compiled-ready-graph-v1-01.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/compiled-ready-graph-v1.json` | `c95134e02278bd6d5594e3564b59d496f549b9da5b338b434dce4e28312b68cc` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/contract-helper-before-use-v1.json` | `20d8ec8a83abd59194525ff5dad69dc3fba7c97348006256940e3ac32b2d5428` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/current-reader-inventory-v1.json` | `2dedccaa4ba3ca75673b979b7e4142e4f710b3194858bd05b4892920d3434000` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/draft-fence-affine_continuous-v1-exit.json` | `89949819ee0cb61dbe867d3f8628b42b9c2eefc4b19b787bdbd5cad89bae4285` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/draft-fence-affine_continuous-v1.log` | `cd0385bfd44c65974af960060ff2715294692cd8fbedd9dafa56396bd700c72b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/draft-fence-affine_convex-v1-exit.json` | `90b7d2120a3cc63bb9fd43a8898affa86004d1b8215651d9f84662c1bea3d7c9` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/draft-fence-affine_convex-v1.log` | `0c60dd2642ccc8e91f69039023b6dffda2ba51cc5899e69d55943bae124b5bfa` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/draft-fence-affine_proper-v1-exit.json` | `a4cdda9cfdee14651c573015b9466edf3a081fb4ff9d6cb0c4e0ab9b3702d2ff` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/draft-fence-affine_proper-v1.log` | `3c002d01da71a9509ce87a639f4e6e7f2c264630375c9a7e7cd791284e7a69dd` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/draft-fence-affine_subdifferential-v1-exit.json` | `665408a0a6de174988ba7b8981a1935e3ee2cd6327208a621b1c17e902262dc2` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/draft-fence-affine_subdifferential-v1.log` | `66afbcbb82f3edd68a00ee5a73a1942d8a73ee95688746fff0bb6ee7a6d955b6` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/draft-fence-example_2_27-v1-exit.json` | `998ccaafaab0716e94629f90e54197d533c05ea7b7eaafea211be774b32af094` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/draft-fence-example_2_27-v1.log` | `48bf11c30106503604eb587b5c1ea54cac4e6517fa2ffbfd1ed7d305f7ad537a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/draft-fence-hingeFamily-v1-exit.json` | `cc30470ffdcb16191c7646a62b44fa76b96475d980e4cf46d70bda35f8315801` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/draft-fence-hingeFamily-v1.log` | `2c1602097cfb434098e4f9f656de731fe88b976746101b2f8ab5b6065651f513` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/draft-fence-hinge_active_negative-v1-exit.json` | `a5eb17ea1d3726e218999c6a3a3317cc08486149100250294b1c19d2607aa56a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/draft-fence-hinge_active_negative-v1.log` | `b11a43f439d81d2a2bc91c2488c4522f9a86c0f4512467277cad479e9c75e15a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/draft-fence-hinge_active_positive-v1-exit.json` | `71afa1518559506f11222ecc262a879b12a30948553869c9f1216863c014593f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/draft-fence-hinge_active_positive-v1.log` | `395851edc285ab44b73e73cd0ab6a1ed6e0b9a9d068ed109e5dcee7687c3759f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/draft-fence-hinge_active_zero-v1-exit.json` | `b165c4990601890bd5feb135a829b2789847854dcc300aa00ae47879ee7d646f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/draft-fence-hinge_active_zero-v1.log` | `605596bc9417d35086ec8e68dc959ff3cd8b229c67a12a4f3cb22a3dbec1ee1b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/draft-fence-hinge_family_false-v1-exit.json` | `2b4803e90cc02ca08aa127d91ece8391eaf4185cddbf94b350608b36ce525c24` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/draft-fence-hinge_family_false-v1.log` | `a5ccf55b6d4de4e54af0dd190f261a649c44eef618a1f843b8a39ff25a6f9cce` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/draft-fence-hinge_family_support-v1-exit.json` | `cb460273a26aa13176db718f660ab441d9ccb2826a4d072cc60bcef1038fff76` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/draft-fence-hinge_family_support-v1.log` | `b949933c99448168936877094591562ad03d9f69078a495253e7a15a91ee9372` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/draft-fence-hinge_family_true-v1-exit.json` | `a3cad712b571bc1d43eb704299f18f4cfce8a30e6e8fcb7e4353980f0e4dcfa1` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/draft-fence-hinge_family_true-v1.log` | `088f4565c69271d7d9d2f82b39dd8cbb28c085874310b96d5a43ef59b987bb71` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/draft-fence-hinge_max_identity-v1-exit.json` | `efacbdf73543657acc67db3d27e0d0d9f1e61b4e6639e3daa846f43c325edc91` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/draft-fence-hinge_max_identity-v1.log` | `f30e2ae80965715d625ebf4ecdb90fc7406db54e09e7d8b328ddc0b1ab6acd07` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/draft-fence-hinge_subdifferential_hull-v1-exit.json` | `0df1f77425319d55c0e9e16e99eb21e42b2414eac0e00e2d8327c1e4844236bd` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/draft-fence-hinge_subdifferential_hull-v1.log` | `865250aeee50ed2a831f1f6f4f448aeaeae480069b92483438711ee570ff912d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/draft-fence-sourceHinge-v1-exit.json` | `6ad0a8fc136feeab45ba05240ce867c81ca1795f8d176492f1e6541482d3f225` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/draft-fence-sourceHinge-v1.log` | `06020829023804a3789053f78dd69a25c88dc6028b6d5ad008389744808f2257` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/draft-freeze-v1.json` | `1345be45f0af84b7cefd9ea6112f793d2534bffcc3460c3742a022e26301d104` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/draft-generated-before-use-v1.json` | `af973a6dbefbac9ab2fd1435bac1d1c6b253c407d0d08443934ee79eba37e6ad` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/draft-lifecycle-v1-exit.json` | `68c1032fe6ce10c7ee6b671233ae9817a13afc8b0bf0eafb0432e3d6d991ce9d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/draft-lifecycle-v1.log` | `b865546e3061162388ce7e25eeb67ea8a176a9ca6c1fd25b6a59281784193d16` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/freeze-draft-v1-01-exit.json` | `c1a5d9106c776108edf50ca62cbb5aea9c0e693806fd59673c13fa504ba9bd0d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/freeze-draft-v1-01.log` | `0e9a8a3717f909865ee1e3e68f19b7959e258b5b2be19bb77a8b629adacf9ea1` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/frontier-refresh-help-v1-01-exit.json` | `7c481b5a35295a02f7346b291d2fb9f5760cece9fcd81255099d4b5ef063eca3` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/frontier-refresh-help-v1-01.log` | `bff73ff554907d7c5dd50b99f2491f5675e93afb29829e402ec383fb52fe3cdc` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/frontier-shadow-help-v1-01-exit.json` | `d356a37532a1913be835f78154f1630ccdbe1b4e2f6abcbd4d9408452be83882` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/frontier-shadow-help-v1-01.log` | `ad548f6e24b3214fbf5796c632caa24debbaa21c6622f7dab8abe268f521de7d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/historical-raw-supersession-v1.json` | `936e7bb419668db5aadf88230554dc517989f0dcec8c589723e47b68dda69cae` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/leaves/actual-types-v1.lean` | `0aca4c7ae084c506e55828d2ac272370bb906a7b17cddd907196ec802d180f81` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/leaves/export-public-dependencies-v1.lean` | `7b80e5bd30426297c98c2b58ae183e70282a0d1b939cdbd3f7569695048e1dea` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/leaves/export-ready-dependencies-v1.lean` | `7e0e58fc7eeccdff9d9d5dddd659e159a2035c7b28d0253b026621f0f50980af` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/leaves/pinned-APIs-v1.lean` | `c470661074773736912243b8b2abe5e3993777f5762f371585daad8f28cab089` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/leaves/pinned-APIs-v2.lean` | `b1e8cee84111561640a97775f94fca9740e9dd76655a019cd9256ae931679c71` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/leaves/public-all-axioms-v1.lean` | `826406b0f7fa737703848c44f09e2ba0231aeab8c28216b97aaf97e03499ddd2` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/lifecycle-event-help-v1-01-exit.json` | `3583d843dd25dd22bf16d25e250e9ed1a43b119891c60c3115be0ab4d628f096` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/lifecycle-event-help-v1-01.log` | `b1e8b438a9b725793b9888d206e98a971ace3df200ec90ed9cb63eab26b28507` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/list-lean-decls-help-v1-01-exit.json` | `2693e9c3b0b59c5153951d2e07bf0f6e0fc028a1c5cbf618058a289393b2908a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/list-lean-decls-help-v1-01.log` | `258218f16a12b1a530d85ae83e6c2449237af8a0a1153bb35de40245d665b131` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/list-mathlib-help-v1-01-exit.json` | `4eb40b8c0c1b7c8f8238bf73b84a23b90487aee0a6094e72734c8bcf9343e9c2` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/list-mathlib-help-v1-01.log` | `eedc3e9609fdc7a3bcf76443a33933477de80dcc4ec9906b64a691e29b207e9d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/list-mathlib-v1-exit.json` | `0110d3d09796f5bcbe83ffd87a22869e679fbaefe9d5aa5c716963ed6fb75187` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/list-mathlib-v1.log` | `884fab88619a3d1adcafe89eecddd2d98f4be5c6fa61262862134dde9e51d225` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/list-papers-help-v1-01-exit.json` | `f54d5d01d5d32f6bc5422697bbfe3ac14e3424a8f314bc200d70dd893b625aaa` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/list-papers-help-v1-01.log` | `57fdd9fadca031cddeec9da9c4ba947cccb3b1b155129de3a81b72b0c811a696` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/list-papers-v1-exit.json` | `8e382796db61f40926213c79b3a1af5942854e71cc83d127a5d6c4936b545c13` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/list-papers-v1.log` | `9acd333996a893a7b5ccad3e674ece26ef05c8b737e7816b33043b121583a619` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/list-weapons-help-v1-01-exit.json` | `be6de326089472ae28b0c41cb78dfb1d365f8aee27d9a5fc785b62d43ff1a55d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/list-weapons-help-v1-01.log` | `529fdc45da8d53249b6cea7712803e68cc0251026c7a66d1a067ac6413c9617d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/list-weapons-v1-exit.json` | `c47b1d52ff9d9769cf3bbac3224dee2ca51ea1deba0893f1aa6c3bd40a31ab08` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/list-weapons-v1.log` | `a6e4b78de1a30fcf5a0ee66b868eb3ac1bfa68d2250c713f61e690ae064f7ef6` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/local-declaration-search-v1-exit.json` | `f661ac8578e6c8e6a7e8e6a0de377692bcdfe4425d290d35bbc628b9399e0e31` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/local-declaration-search-v1.log` | `3712fd1cf10482a3677ae60f6fb3569f13d77763892fb474b7cf1a8b70c3f6e6` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/local-declaration-search-v2-exit.json` | `051e6f6dddc5422666e23e839feba8d27e141774e8bfd19cfbd5500763460faa` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/local-declaration-search-v2.log` | `9d08c33d4d4f145dcf4d3024da9cb0035b553159887d23c3d62b5e37a0bc3d07` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/local-memory-search-v1-exit.json` | `c77e05b3e88e3ad384e72a38071eef25786b062137323eabe0f9096a330ce7a5` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/local-memory-search-v1.log` | `11999fd2b01349cb48f47e2291dcbda3daeae233e4d63611c1bad6c59a86faae` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/memory-digest-draft-v1.md` | `15bc2f6d17ea76b1abc22c706ff33c57c8f3f2c545fbf6047b2209fdf97c4b15` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/native-draft-fences/affine_continuous.json` | `cd0385bfd44c65974af960060ff2715294692cd8fbedd9dafa56396bd700c72b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/native-draft-fences/affine_convex.json` | `0c60dd2642ccc8e91f69039023b6dffda2ba51cc5899e69d55943bae124b5bfa` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/native-draft-fences/affine_proper.json` | `3c002d01da71a9509ce87a639f4e6e7f2c264630375c9a7e7cd791284e7a69dd` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/native-draft-fences/affine_subdifferential.json` | `66afbcbb82f3edd68a00ee5a73a1942d8a73ee95688746fff0bb6ee7a6d955b6` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/native-draft-fences/example_2_27.json` | `48bf11c30106503604eb587b5c1ea54cac4e6517fa2ffbfd1ed7d305f7ad537a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/native-draft-fences/hingeFamily.json` | `2c1602097cfb434098e4f9f656de731fe88b976746101b2f8ab5b6065651f513` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/native-draft-fences/hinge_active_negative.json` | `b11a43f439d81d2a2bc91c2488c4522f9a86c0f4512467277cad479e9c75e15a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/native-draft-fences/hinge_active_positive.json` | `395851edc285ab44b73e73cd0ab6a1ed6e0b9a9d068ed109e5dcee7687c3759f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/native-draft-fences/hinge_active_zero.json` | `605596bc9417d35086ec8e68dc959ff3cd8b229c67a12a4f3cb22a3dbec1ee1b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/native-draft-fences/hinge_family_false.json` | `a5ccf55b6d4de4e54af0dd190f261a649c44eef618a1f843b8a39ff25a6f9cce` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/native-draft-fences/hinge_family_support.json` | `b949933c99448168936877094591562ad03d9f69078a495253e7a15a91ee9372` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/native-draft-fences/hinge_family_true.json` | `088f4565c69271d7d9d2f82b39dd8cbb28c085874310b96d5a43ef59b987bb71` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/native-draft-fences/hinge_max_identity.json` | `f30e2ae80965715d625ebf4ecdb90fc7406db54e09e7d8b328ddc0b1ab6acd07` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/native-draft-fences/hinge_subdifferential_hull.json` | `865250aeee50ed2a831f1f6f4f448aeaeae480069b92483438711ee570ff912d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/native-draft-fences/sourceHinge.json` | `06020829023804a3789053f78dd69a25c88dc6028b6d5ad008389744808f2257` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/pinned-APIs-v2-01-exit.json` | `0ee2feab4034d46acbf188b6c4f245a1b8cc358501a5cc4e7a9c3b8e4c0aea7d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/pinned-APIs-v2-01.log` | `eac6f600cc328e02001ffaa82ad007dfd9dd42b39617303908cb6c124fa1c7dd` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/prepare-contract-v1-01-exit.json` | `0243b899a639e6bf9442e334ddc737bb2cd495e768d93398b683fe596e3eda0a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/prepare-contract-v1-01.log` | `bbf24a6a2b21133995a20006977d783c6edd66851dbd326b1ea456fff73e7781` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/prepare-contract-v1.py` | `ffb4633cc6d27600c4d8a3aee0380731636ae2d5913dbf0cda278fdf9737d19f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/prepare-readiness-v1-01-exit.json` | `27a7895455e848d635ece64d6a7cf8601c0b9ca16a80d531a270d1291a06a6f6` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/prepare-readiness-v1-01.log` | `a92b72a7e47b415d1bfe78fd65c0608723457ab1443da002f1e09f8df6626a2a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/prepare-readiness-v1.py` | `f320f3ecb042d9e1e10d47447781bf151ae5b892b513e759e19feccef3844359` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/preserve-native-prefix-v1.py` | `f949ca2d8b461c51a23ed08858cbffd4222575a76cd534733969ab7daa9ae2f9` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/prior-delivery-raw-binding-v1.json` | `9c67ca86a3deb33975426372efb61efb9ae30eadf23e92674ead6b7555151535` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/proof-obligations-draft-v1.json` | `3f3c3ba24e43f11c02f8bf6e6dde19ecfd9c3c4ec2784ab1ab839621781ce21b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/public-named-declarations-v1.json` | `81c672ab36eaab01f913aeb21a20ef7e6629ba81a04d3f15be43d52f16e73bfd` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/readiness-helper-before-use-v1.json` | `43fd3dc271f6c4a7f4bbc7107bca6bae99d5e1ffffb5ba49dfd835d53a7341c4` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/readiness-probes-before-use-v1.json` | `c284933b093a4e5f6f397c47a140c8b1b738d23d7ff30fae13c9b40286872237` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/readonly-lookup-diagnostics-v1.json` | `8329264a7b8db8ce2e2dd8cee465db530e35575464f3a0f455af65e05fba8ff3` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/ready-dependencies-v1.json` | `9a5b3ee8e03af886b560e540a4c8aaa43c4b816184f389f0b85f6e85536ce1cc` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/reference-index-help-v1-01-exit.json` | `676a5e7240af8baa80b13dd94a65b853ec5e4c8f14a5d5b4519e4189a8d9b56e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/reference-index-help-v1-01.log` | `6943acba1d20272cfd239404bfaaa8457d0205a56876004e7c3fed2df97fc3d8` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/reference-index-manifest-v1.md` | `c02cad8b52909c3611466365fac8615d1b5888d610c821bf6f9fdbecafa47a2d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/reference-index-scope-v1.json` | `fea634e5bdedee780a6c8de90d77f53d80d8283bdbca007d2bde2746b13f6736` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/reference-index-scoped-v1-01-exit.json` | `956d22c088acdc541ad4ed43c59eb7e87d6d46a01fab75ab0998c61542406a14` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/reference-index-scoped-v1-01.log` | `6088540fe91064545f51b3b83c91c7e78e752e1b7af2dc52e79ec2fb1cf0d856` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/retained-focused-v1-01-exit.json` | `23f43c0fba7d7d73301918a7f775749e14b03d478deeccbdb1a9c4eea7b2bd4a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/retained-focused-v1-01.log` | `6fe08671397b526e966e120a81c0c467b29990aba8aaf84dd21b5402b51c7ba6` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/retrieval-index-draft-v1.md` | `282e6f681c4fffc039712b7695f97c1f0e94e577468f0ffc78016c92a310aa46` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/retrieval-record-help-v1-01-exit.json` | `3d2586caada15c87cff6c766fca91ac904867eab86d099c7512eb148b1f45d66` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/retrieval-record-help-v1-01.log` | `73ac93f120215511ff0370d7ce100a9d0e83598ad882bcc5773cd1dc889b5321` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/retrieval-record-v1-exit.json` | `0517e77b498f4c31d664b81c34d6d677218550f03c0969f4aecaba1943b12a03` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/retrieval-record-v1.json` | `7ac2876aea59859027822a217d9ef13f4c07b9b9629d1e682e7d52334e415f3c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/retrieval-record-v1.log` | `377eeccfca74460b7b182e0cf67d5d0899863b09157583a73f740a8060b950de` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/retrieval-review-helpers-before-use-v1.json` | `bc3566bf5b3af975a4195147ee5cebfef2a37ae88d512b7a89cad732a1d7d213` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/retrieval-snapshot-v1/bandit_paper_cards.json` | `cca81afe0d2629ea91b4106e9d9945d9e6bd701c2f9f2c7776d77e6bdc1e1a08` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/retrieval-snapshot-v1/bandit_scenario_cards.json` | `fd1b26f10cfced77debaa1c3d4174750a8daa499b3fff621420b9301d6f3343a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/retrieval-snapshot-v1/bandit_textbook_cards.json` | `7de8402851af5292aad26b03cd628afa16a5f5ca40726c714526a4f39750c9f5` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/retrieval-snapshot-v1/lml_bandit_cards.json` | `fa149c38753544dc8a45fc3f12e4b3116de2661798285d0eea6f5960c7bd1959` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/retrieval-snapshot-v1/local_leaf_cards.json` | `17e6693b5ebfe5cdc75ee2cc879122121be155362347bdaf2857d8fd145899b5` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/retrieval-snapshot-v1/local_lean_declarations.json` | `fe21e43f8718ade5bee2bb36359a4394399895fdfeb5c8ac0206ba1dcc82fa7f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/retrieval-snapshot-v1/mathlib_bandit_cards.json` | `824faf3db7ceeea04f8dfc39a72f308d5bef6bafe67751f6c1ac66da13fa39ae` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/retrieval-snapshot-v1/proof_weapon_cards.json` | `d5b5e88ecdd6b73a928cf6bcdf7bbdfd747583741872bca555ca9ba3d75f3f83` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/revalidate-bodies-v1.py` | `21c11e8512a18f94941db71cd38f9423597aff08be515248279be028d0deef65` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/review-packets-v1.py` | `4ae42d87cf14d54710cc376748df65727337e47a4a0df870a2e052f4c8044644` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/run-command.py` | `cb0e98401a104a6f0ad87f684a69a4e776e1de9de7d5b2a7848a394cad0a5db1` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/safe-verify-help-v1-01-exit.json` | `8a47adc33dabf75af9e5519fb7f2a5023fd74cf7f750abc08e6ef9fc678da76d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/safe-verify-help-v1-01.log` | `1773541c625f225e5a9abc61985c3ad19e871cf31aa0cf89cc440b3d8398862c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/scoped-reference-index-v1.py` | `e8b2fe1a107ba7fc21c52b390c956d82af465293f37017104e5a141305878078` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/search-memory-help-v1-01-exit.json` | `4dba4bc191fb098298986ba5c8d675aa89a1726a572366155d3194bea807abbe` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/search-memory-help-v1-01.log` | `b2f23faf2d0ee17c305335680ebdb2b83ca61999d18021e355d22587d712b79c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/snapshots/before-BanditRLProof--OnlineClosedProper.lean.txt` | `c66f00c33b45fb8a0e11583eeadf506e176c16166ce2af02f41f0674507cebe7` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/snapshots/before-BanditRLProof--OnlineConvexExtended.lean.txt` | `bd30bb95a46ccdc3f6d25f808c175af5fee71d075c2b46ffcf6508f15f1ed66a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/snapshots/before-BanditRLProof--OnlineHinge.lean.txt` | `118d28177c11b0ff113fba5ab34a6bbd9190fee5fb05af644b7b2207c05b020b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/snapshots/before-BanditRLProof--OnlineSubgradientBasic.lean.txt` | `af3d3f56e4a64cd8adbe47368caf5382e63b428f01da29a121c28c8014f352a5` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/snapshots/before-BanditRLProof--OnlineSubgradientMax.lean.txt` | `9efd6831768ce1cdf494ec051aeb14c9a35b87669fb203cdef031cafd94de9c2` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/snapshots/before-BanditRLProof.lean.txt` | `351d5238e97cf54ae4c5f65a7e82cabc40ac7eb6f18c9e64e89e27a6610cb9c6` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/snapshots/before-MANIFEST.md.txt` | `f753dca006dc921d8a2119e44b9281ef2b71a8a5609fb607b3c04d67c045373e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/snapshots/before-Tests--OnlineHingeCanary.lean.txt` | `e60831daa708ba1013abe570deb5d360c91a120b4a34f3d1df230b4c2a94fdb4` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/snapshots/before-Tests.lean.txt` | `cd21ef4e7cea89c7d245eaf4dff14be8baa34f2d336e40d6f6bbb16011678340` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/snapshots/before-lake-manifest.json.txt` | `87c3e616f86244550ef39e7415186b11c1d4cf4bef20173196a619d9d4d48f48` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/snapshots/before-lakefile.lean.txt` | `0164f3b5b5bdcbb237ab15ae8b44da83e183f4b97d5f3832aa4a57f27dc69d45` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/snapshots/before-lean-toolchain.txt` | `b15a57f8ea4c890197465ce1156667ae13d9ed4ab8a9f263a920bf010d967d82` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/snapshots/before-runs--active_frontier.json.txt` | `567e5873aa2549a83f2820d758069213808da822a93087129877385a1addf7c3` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/snapshots/before-runs--lifecycle_sessions.jsonl.txt` | `c6d7d3c73a84ae1a981420dd455bd89b38a606fa16d287bd597fbb1ce16a8398` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/snapshots/before-runs--trials.jsonl.txt` | `382461a06e227b8fc2de3a6f61cb14579f138dbad1fab80a6b73f0bf845a3afd` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/snapshots/before-website--content--chapters.json.txt` | `6f09376f4d7621dd4b678602b25dfe5ada4144bf8b88dbed1dd5e881af7b3302` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/snapshots/before-website--content--highlights.json.txt` | `b661fddde803913ef1351a21dfe520c9949b515762a4b174ed387ef6e7787dac` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/snapshots/before-website--content--readings.json.txt` | `f563f9c38434f8bd7192c1dd83f3dd646ce1c48a2301beb352bd15ea2cd093f3` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/source-contract-packet-v1.md` | `cf698f8eadf4dc00c265e2b6505862253e9fc12fdd41ea6308c59fddd394ea39` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/source-printed18-pdf30.txt` | `79a3aacef74fc16fd80b21ef87043e0ff5999ff6cf540e4741f09ca6c6447edc` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/source-visual-read-v1.json` | `788452a98c1ff3dd942525b855d2886753bcb22b44088ed0fdf51ddc4b9fa37e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/statement-fence-help-v1-01-exit.json` | `bde4bb43667bbab98d89dfe53e527b74cb34c6e6cb72b64a3ec91cf6cffb7743` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/statement-fence-help-v1-01.log` | `4f4fca9dfaac7a7c3de8025d3d0f7c4ba58d1f4b33feb08d19e12229942dba75` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/trial-log-help-v1-01-exit.json` | `18ccb79d5a656b73b7daaef9bbaf62cf254c0e0e0e56b5105631dd8a6dbfd932` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/trial-log-help-v1-01.log` | `ea7bd7e4d64216b46f554a90e02a3d58b4fcbe72766c2f7b316b656b94d19b32` |
| `E:\ABRL\worktrees\research-online-book\tmp\online-subgradient-sum-source-pdf30-v1.png` | `c4354de7297923fd82f74645ddd50fdb582f90b6eeb9a7536fd9f33ec5489ebd` |
| `E:\ABRL\worktrees\research-online-ogd\tmp\pdfs\orabona-v10.pdf` | `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17` |
| `MANIFEST.md` | `f753dca006dc921d8a2119e44b9281ef2b71a8a5609fb607b3c04d67c045373e` |
| `Tests.lean` | `cd21ef4e7cea89c7d245eaf4dff14be8baa34f2d336e40d6f6bbb16011678340` |
| `Tests/OnlineHingeCanary.lean` | `e60831daa708ba1013abe570deb5d360c91a120b4a34f3d1df230b4c2a94fdb4` |
| `conversion-windows/ONLINE-HINGE-MIGRATION-20261007.md` | `3e67077c6507dcb51b627d82499630c878e378dee7c69b5708d966dba5656d5c` |
| `docs/contracts/online-book-v1/source-inventory.json` | `a2a504cf40d73f9c5e36f00fc1ef3b949ccaf5a558ab603c1c2a86007f30efa7` |
| `docs/contracts/online-hinge-migration-v1/contract.md` | `3e67077c6507dcb51b627d82499630c878e378dee7c69b5708d966dba5656d5c` |
| `docs/contracts/online-hinge-migration-v1/headers.json` | `75e042971faa39e19486d04f3e814c7adfcbd79f3f2dc21f9b1a3625403c867f` |
| `docs/contracts/online-hinge-migration-v1/initial-dependency-DAG.json` | `30200dea1b24c50aee74c3e70be11b7779083d528d65215fcb54ed7c6881e052` |
| `docs/contracts/online-hinge-migration-v1/scoped-contexts.json` | `29700f9157110f2b78eaa67be5482376b387a1d86f3962e7057dc40fb2ff6b49` |
| `docs/contracts/online-hinge-migration-v1/source-card.json` | `b6633b76a524200a481e25671033fd54993ad7ec61210ab750e1e1fabf65a78c` |
| `docs/contributor-codex-contract.md` | `d7dfa3406def35de292b202f45ff8303b9a550310bd00979be838e5a2348a498` |
| `docs/theorem-publication-protocol.md` | `b1e5ac73cfe0a90742567736b422787c90a51e6b6ff007cc1dc8d598948f687e` |
| `lake-manifest.json` | `87c3e616f86244550ef39e7415186b11c1d4cf4bef20173196a619d9d4d48f48` |
| `lakefile.lean` | `0164f3b5b5bdcbb237ab15ae8b44da83e183f4b97d5f3832aa4a57f27dc69d45` |
| `lean-toolchain` | `b15a57f8ea4c890197465ce1156667ae13d9ed4ab8a9f263a920bf010d967d82` |
| `proof-obligations/ONLINE-HINGE-MIGRATION-20261007.md` | `3e67077c6507dcb51b627d82499630c878e378dee7c69b5708d966dba5656d5c` |
| `research-wiki/mathlib-candidates/README.md` | `ea4ed80d4eed053d0eea0d315df86075a9445e6280e2a827e3841e5c05d7df37` |
| `research-wiki/mathlib/theorem-cards.md` | `4656c1a8ccd4b2d8523cf5cf48bd1f966e7ba2c2237e2e578d6b8c2ecc6fbd97` |
| `runs/active_frontier.json` | `567e5873aa2549a83f2820d758069213808da822a93087129877385a1addf7c3` |
| `runs/lifecycle_sessions.jsonl` | `67ade5cdfbca60516812e84472e01d21b97ccf314f11082dfe42f4d75da22c8e` |
| `runs/trials.jsonl` | `382461a06e227b8fc2de3a6f61cb14579f138dbad1fab80a6b73f0bf845a3afd` |
| `tasks/ONLINE-HINGE-MIGRATION-20261007.md` | `3e67077c6507dcb51b627d82499630c878e378dee7c69b5708d966dba5656d5c` |
| `website/content/chapters.json` | `6f09376f4d7621dd4b678602b25dfe5ada4144bf8b88dbed1dd5e881af7b3302` |
| `website/content/highlights.json` | `b661fddde803913ef1351a21dfe520c9949b515762a4b174ed387ef6e7787dac` |
| `website/content/readings.json` | `f563f9c38434f8bd7192c1dd83f3dd646ce1c48a2301beb352bd15ea2cd093f3` |
| `runs/online-hinge-migration-20261007/source-contract-inputs-v1.json` | `d3150738bec5ee58b40450d8bf6a3dd3c202d0cb8a1501715571d188e3ca41b0` |
