# Example2.27 hinge actual BODY review v1

**Verdict: accepted-with-explicit-delta, actual public body and canary recommendation only.** No mathematical or binding repair required; all nine reader obligations remain open.

{"task": "/root/source_reviewer", "role": "distinct automated source reviewer", "requested_model": "GPT-6 Astra", "requested_reasoning": "medium", "runtime_model_attested": false, "human_review": false, "external_model_review": false, "history": "Same distinct source reviewer with CONTRACT and earlier staged history; current BODY decision separately inspects actual producer terms and gates. No erased-history, human/external review or runtime-model attestation."}

## Raw and source checks

Independently hashed all 334 fixed BODY inputs, all matched. Rechecked 212 prior CONTRACT reviewed rows against immutable resolved raw bytes and original receipt membership. Only runs/lifecycle_sessions.jsonl and runs/trials.jsonl require their exact contract-reviewed prefix snapshots; current mutable append state was not substituted for old evidence. Original report/receipt remain unmodified. Current public module, full owned definitions, all 15 headers and whole old canary bytes match original frozen inputs.

Freshly verified pinned PDF SHA256 `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17`, extracted physical30/printed18 and actually viewed bound page PNG. Source has one Example2.27 and full three-way set equality. Coordinate-free finite-dimensional real inner formulation includes Euclidean source; generic support API permits improper functions beyond source proper convention, but actual hinge/components are everywhere finite. No source loss-domain/infinity ambiguity survives this specialization.

Actual compiled binder types and borrowed contexts remain as CONTRACT: P/D/Q arbitrary E, C AddCommGroup+real Module, M arbitrary E+finite nonempty index, S/U intrinsic inner. Both owned definitions and eleven helper proofs need intrinsic real norm/inner structure but not FD; only hull and terminal explicitly need FD. No supplied CompleteSpace, positive dimension, nonzero z, norm bound or support oracle.

## Per-proof seven slots and actual producer audits

### BanditRL.OnlineConvex.affine_subdifferential

accepted-with-explicit-delta; actual BODY scope.

`theorem affine_subdifferential (a : E) (b : ℝ) (x : E) : SourceSubdifferential (fun y => ((inner ℝ a y + b : ℝ) : EReal)) x = {a}`

- **objects_spaces**: E with NormedAddCommGroup and InnerProductSpace over real; EReal values and ambient support vectors. Finite dimension only when listed in assumptions.
- **quantifiers**: all a:E,b:real,x:E; membership tests every ambient y
- **assumptions**: none beyond intrinsic real inner structure
- **conclusion**: S(y -> coe(inner a y+b),x) = {a}
- **constants_normalization**: unit inner coefficient; arbitrary real intercept b
- **information_probability**: Deterministic convex analysis; no algorithm, regret, feedback, measurable/computable selection or probabilistic claim.
- **boundaries**: Zero slope, zero dimension and every query included; no FD or completeness premise.

Actual producer: Extensional iff: test every-y support at y=x+(g-a), convert finite real embeddings, derive inner(g-a,g-a)<=0 and combine inner positivity to obtain g=a. Reverse substitutes a and verifies the affine identity for every ambient y. No derivative or support singleton oracle.

### BanditRL.OnlineConvex.affine_proper

accepted-with-explicit-delta; actual BODY scope.

`theorem affine_proper (a : E) (b : ℝ) : SourceProper (fun y => ((inner ℝ a y + b : ℝ) : EReal))`

- **objects_spaces**: E with NormedAddCommGroup and InnerProductSpace over real; EReal values and ambient support vectors. Finite dimension only when listed in assumptions.
- **quantifiers**: all a:E,b:real
- **assumptions**: none beyond intrinsic real inner structure
- **conclusion**: affine expression has no bottom anywhere and has an actual finite real witness
- **constants_normalization**: arbitrary b, witness can be y=0 and value b
- **information_probability**: Deterministic convex analysis; no algorithm, regret, feedback, measurable/computable selection or probabilistic claim.
- **boundaries**: E has zero and is inhabited; SourceProper itself is a predicate on arbitrary carriers. Not a convexity assertion.

Actual producer: Constructs no-bottom from coe_ne_bot at every y and explicit finite witness y=0,value=b. Inner space supplies zero; no nonempty carrier premise silently lost.

### BanditRL.OnlineConvex.affine_convex

accepted-with-explicit-delta; actual BODY scope.

`theorem affine_convex (a : E) (b : ℝ) : IsConvexExtended (fun y => ((inner ℝ a y + b : ℝ) : EReal))`

- **objects_spaces**: E with NormedAddCommGroup and InnerProductSpace over real; EReal values and ambient support vectors. Finite dimension only when listed in assumptions.
- **quantifiers**: all a:E,b:real
- **assumptions**: none beyond intrinsic real inner structure
- **conclusion**: real-height epigraph of embedded affine expression is convex
- **constants_normalization**: nonnegative weights, including endpoints, sum to one
- **information_probability**: Deterministic convex analysis; no algorithm, regret, feedback, measurable/computable selection or probabilistic claim.
- **boundaries**: No FD, strict convexity, closedness or loss differentiability premise.

Actual producer: Uses actual affine_proper no-bottom to invoke convexExtended_iff_toReal; proves effectiveDomain=univ using coe_lt_top. Expands inner add/smul and uses p+q=1 for the intercept, including weight endpoints. No infinity-toReal shortcut.

### BanditRL.OnlineConvex.affine_continuous

accepted-with-explicit-delta; actual BODY scope.

`theorem affine_continuous (a : E) (b : ℝ) (x : E) : ContinuousAt (fun y => ((inner ℝ a y + b : ℝ) : EReal)) x`

- **objects_spaces**: E with NormedAddCommGroup and InnerProductSpace over real; EReal values and ambient support vectors. Finite dimension only when listed in assumptions.
- **quantifiers**: all a:E,b:real,x:E
- **assumptions**: none beyond intrinsic real inner structure
- **conclusion**: ContinuousAt of EReal-embedded affine expression at x
- **constants_normalization**: no modulus or bound
- **information_probability**: Deterministic convex analysis; no algorithm, regret, feedback, measurable/computable selection or probabilistic claim.
- **boundaries**: Ambient EReal continuity at every query; no FD or derivative premise.

Actual producer: Actual composition of continuous inner(a,y)+b with continuous real-to-EReal embedding; ambient ContinuousAt at every x.

### BanditRL.OnlineConvex.hinge_max_identity

accepted-with-explicit-delta; actual BODY scope.

`theorem hinge_max_identity (z : E) : SourceFiniteMax (hingeFamily z) = sourceHinge z`

- **objects_spaces**: E with NormedAddCommGroup and InnerProductSpace over real; EReal values and ambient support vectors. Finite dimension only when listed in assumptions.
- **quantifiers**: all z:E; equality of functions therefore every evaluation x
- **assumptions**: none beyond intrinsic real inner structure
- **conclusion**: SourceFiniteMax (hingeFamily z) = sourceHinge z
- **constants_normalization**: Bool false=0; true=1-inner z x
- **information_probability**: Deterministic convex analysis; no algorithm, regret, feedback, measurable/computable selection or probabilistic claim.
- **boundaries**: Both sign regimes and tie; actual finite nonempty Bool family. Not arbitrary empty maximum.

Actual producer: Both pointwise inequalities: every Boolean component bounded by real maximum; reverse uses actual true or false Finset.le_sup witness according to margin sign. Tie goes through nonnegative branch. Function equality for every x.

### BanditRL.OnlineConvex.hinge_subdifferential_hull

accepted-with-explicit-delta; actual BODY scope.

`theorem hinge_subdifferential_hull [FiniteDimensional ℝ E] (z x : E) : SourceSubdifferential (sourceHinge z) x = convexHull ℝ (SourceActiveSubgradientUnion (hingeFamily z) x)`

- **objects_spaces**: E with NormedAddCommGroup and InnerProductSpace over real; EReal values and ambient support vectors. Finite dimension only when listed in assumptions.
- **quantifiers**: all z,x:E; entire support set equality
- **assumptions**: FiniteDimensional real E in addition to intrinsic inner structure
- **conclusion**: S(sourceHinge z,x) = ordinary convexHull real (active component support union)
- **constants_normalization**: exact attaining equality, unweighted maximum
- **information_probability**: Deterministic convex analysis; no algorithm, regret, feedback, measurable/computable selection or probabilistic claim.
- **boundaries**: All queries finite. Properness, convexity and ambient continuity of components are conclusions of affine facts, not extra supplied assumptions. No closed-hull replacement.

Actual producer: Rewrites actual maximum identity and applies full theorem_2_26. Produces each component properness, convexity, finite-at-query via coe_lt_top and ambient continuity from actual affine bodies. Bool finite/nonempty is an instance, not an assumption on unknown family. Ordinary hull equality supplied by upstream theorem, not an assumed current conclusion.

### BanditRL.OnlineConvex.hinge_family_support

accepted-with-explicit-delta; actual BODY scope.

`theorem hinge_family_support (z : E) (i : Bool) (x : E) : SourceSubdifferential (hingeFamily z i) x = {if i then -z else 0}`

- **objects_spaces**: E with NormedAddCommGroup and InnerProductSpace over real; EReal values and ambient support vectors. Finite dimension only when listed in assumptions.
- **quantifiers**: all z:E,i:Bool,x:E; support tests every ambient y
- **assumptions**: none beyond intrinsic real inner structure
- **conclusion**: S(hingeFamily z i,x) = {if i then -z else 0}
- **constants_normalization**: Boolean true slope -z, false slope 0
- **information_probability**: Deterministic convex analysis; no algorithm, regret, feedback, measurable/computable selection or probabilistic claim.
- **boundaries**: Valid for inactive as well as active components; no activity premise, FD or choice oracle.

Actual producer: Unfolding actual affine coefficients is definitionally compatible with affine_subdifferential; works even for inactive i. No assumed active index.

### BanditRL.OnlineConvex.hinge_family_false

accepted-with-explicit-delta; actual BODY scope.

`theorem hinge_family_false (z x : E) : hingeFamily z false x = ((0 : ℝ) : EReal)`

- **objects_spaces**: E with NormedAddCommGroup and InnerProductSpace over real; EReal values and ambient support vectors. Finite dimension only when listed in assumptions.
- **quantifiers**: all z,x:E
- **assumptions**: none beyond intrinsic real inner structure
- **conclusion**: hingeFamily z false x = coe(0:real)
- **constants_normalization**: embedded zero, not bottom
- **information_probability**: Deterministic convex analysis; no algorithm, regret, feedback, measurable/computable selection or probabilistic claim.
- **boundaries**: No claim that this index is always active.

Actual producer: Unfolds actual false branch and inner zero; embedded real zero not EReal bottom.

### BanditRL.OnlineConvex.hinge_family_true

accepted-with-explicit-delta; actual BODY scope.

`theorem hinge_family_true (z x : E) : hingeFamily z true x = ((1 - inner ℝ z x : ℝ) : EReal)`

- **objects_spaces**: E with NormedAddCommGroup and InnerProductSpace over real; EReal values and ambient support vectors. Finite dimension only when listed in assumptions.
- **quantifiers**: all z,x:E
- **assumptions**: none beyond intrinsic real inner structure
- **conclusion**: hingeFamily z true x = coe(1-inner z x)
- **constants_normalization**: intercept one and negative sign
- **information_probability**: Deterministic convex analysis; no algorithm, regret, feedback, measurable/computable selection or probabilistic claim.
- **boundaries**: Expression may be negative, zero or positive; this component is not clipped.

Actual producer: Unfolds true branch, converts via congrArg of real embedding and inner_neg_left; ring establishes intercept-minus-inner exact sign.

### BanditRL.OnlineConvex.hinge_active_negative

accepted-with-explicit-delta; actual BODY scope.

`theorem hinge_active_negative (z x : E) (h : 1 - inner ℝ z x < 0) : SourceActiveSubgradientUnion (hingeFamily z) x = {(0 : E)}`

- **objects_spaces**: E with NormedAddCommGroup and InnerProductSpace over real; EReal values and ambient support vectors. Finite dimension only when listed in assumptions.
- **quantifiers**: all z,x:E followed by negative-margin premise
- **assumptions**: 1-inner z x < 0
- **conclusion**: active support union = {0}
- **constants_normalization**: threshold 1; strict comparison with 0
- **information_probability**: Deterministic convex analysis; no algorithm, regret, feedback, measurable/computable selection or probabilistic claim.
- **boundaries**: Tie excluded; union itself, not a hull or selected vector. No FD.

Actual producer: Extensional membership, exhausts Bool indices, rewrites actual max and full affine supports. Strict negative real margin gives unequal EReal values, excluding true; false attains and its support is zero. Both directions remain.

### BanditRL.OnlineConvex.hinge_active_positive

accepted-with-explicit-delta; actual BODY scope.

`theorem hinge_active_positive (z x : E) (h : 0 < 1 - inner ℝ z x) : SourceActiveSubgradientUnion (hingeFamily z) x = {-z}`

- **objects_spaces**: E with NormedAddCommGroup and InnerProductSpace over real; EReal values and ambient support vectors. Finite dimension only when listed in assumptions.
- **quantifiers**: all z,x:E followed by positive-margin premise
- **assumptions**: 0 < 1-inner z x
- **conclusion**: active support union = {-z}
- **constants_normalization**: negative vector, not margin-scaled vector
- **information_probability**: Deterministic convex analysis; no algorithm, regret, feedback, measurable/computable selection or probabilistic claim.
- **boundaries**: At z=0 this premise holds and the singleton is {0}; no FD.

Actual producer: Same actual Bool enumeration; strict positivity excludes false and true attains; complete active union equals {-z}. No FD needed.

### BanditRL.OnlineConvex.hinge_active_zero

accepted-with-explicit-delta; actual BODY scope.

`theorem hinge_active_zero (z x : E) (h : 1 - inner ℝ z x = 0) : SourceActiveSubgradientUnion (hingeFamily z) x = {(0 : E), -z}`

- **objects_spaces**: E with NormedAddCommGroup and InnerProductSpace over real; EReal values and ambient support vectors. Finite dimension only when listed in assumptions.
- **quantifiers**: all z,x:E followed by exact tie premise
- **assumptions**: 1-inner z x = 0
- **conclusion**: active support union = {0,-z}
- **constants_normalization**: two endpoints before taking hull
- **information_probability**: Deterministic convex analysis; no algorithm, regret, feedback, measurable/computable selection or probabilistic claim.
- **boundaries**: Premise impossible at z=0; this union omits nontrivial mixtures, so is not the terminal support set. No FD.

Actual producer: Actual zero margin makes both affine values equal actual maximum. Bool enumeration yields g=0 or g=-z, precisely endpoint union. Does not falsely identify union with segment.

### BanditRL.OnlineConvex.example_2_27

accepted-with-explicit-delta; actual BODY scope.

`theorem example_2_27 [FiniteDimensional ℝ E] (z x : E) : SourceSubdifferential (sourceHinge z) x = if 1 - inner ℝ z x < 0 then {0} else if 1 - inner ℝ z x = 0 then {g | ∃ α ∈ Icc (0 : ℝ) 1, g = -(α • z)} else {-z}`

- **objects_spaces**: E with NormedAddCommGroup and InnerProductSpace over real; EReal values and ambient support vectors. Finite dimension only when listed in assumptions.
- **quantifiers**: all z,x:E, every candidate g; middle branch exists alpha in closed Icc 0 1; supports quantify all ambient y
- **assumptions**: FiniteDimensional real E; no premise on z,x
- **conclusion**: full S equals {0} for negative margin, all -(alpha smul z) for zero margin, {-z} otherwise
- **constants_normalization**: margin exactly 1-inner z x; alpha includes 0 and 1; else is positive by real trichotomy
- **information_probability**: Deterministic convex analysis; no algorithm, regret, feedback, measurable/computable selection or probabilistic claim.
- **boundaries**: Zero z gives constant loss 1 and positive margin, hence {0}; zero dimension allowed. No nonzero-z, norm bound, supplied support/hull formula or selected-support shortcut.

Actual producer: Rewrites full hull equality and splits exact if conditions. Strict branches use actual active singleton and convexHull_singleton. Tie uses convexHull_pair and segment_eq_image, retains alpha in closed Icc and constructs both directions by reversing witness equality. Else positivity follows from not-negative/not-zero. No selected-support weakening or closure added.

## Two full owned definition bodies

### BanditRL.OnlineConvex.sourceHinge

```lean
def sourceHinge (z x : E) : EReal := ((max (1 - inner ℝ z x) 0 : ℝ) : EReal)
```

Full-body SHA256 `4b833d1d6228d3101d78955b5a723bbcb57238c4c517aea6d2f767e80886e89f`. Exact complete raw definition and compiled intrinsic binders preserved; no new definition or extra regularity parameter.
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

Full-body SHA256 `59c20a1b48b67c51b5fcd43330322f9e18ef1c835a321809db910cc0ead2e5f0`. Exact complete raw definition and compiled intrinsic binders preserved; no new definition or extra regularity parameter.
- **objects_spaces**: Intrinsic NormedAddCommGroup E and InnerProductSpace real E; codomain EReal; no FD.
- **quantifiers**: every z:E, i:Bool, y:E
- **assumptions**: No properness, convexity, continuity, dimension or side condition is a definition parameter.
- **conclusion**: Embedded affine inner(if i then -z else 0,y)+(if i then 1 else 0)
- **constants_normalization**: Actual threshold/intercept 1, zero baseline; Bool true is negative slope with intercept one.
- **information_probability**: Pure mathematical construction, no oracle or procedure guarantee.
- **boundaries**: Everywhere finite including z=0; sourceHinge 0 x=1. No empty-domain or improper-input case in these actual definitions.

## Whole canary nonvacuity

- **HingeProbe.strict_zero**: Actual z=1,x=2, inner=2; invokes full terminal to get entire singleton {0}.
- **HingeProbe.strict_slope**: Actual z=1,x=0, margin=1; invokes full terminal to get entire {-1}.
- **HingeProbe.boundary_interval**: Actual z=1,x=1; extensional forward/backward interval proof, converse chooses alpha=-g. Full closed [-1,0], not endpoints alone.
- **HingeProbe.actual_mixture_and_rejection**: Uses actual boundary equality and actual zero-margin active union to prove -1/2 in full support but outside {0,-1}, and +1 outside full support. Genuine hull enlargement and rejection.
- **HingeProbe.zero_vector**: For every scalar x, actual z=0 gives positive margin=1, constant loss=1 and full support {0}. Not a tie/2D test.

## Actual observed gate evidence

Public module directly re-elaborated by recorded lake env lean, exit0 in 10.407s; only unnecessarySimpa warning. Whole canary lake build exited0 in 2.234s, completed3319 jobs with replay warnings; this is not a claim that every job rebuilt. Actual axiom log independently parsed:20 unique names (13 production proofs+2 owned definitions+5 canary proofs), all exactly propext/Classical.choice/Quot.sound, no sorryAx. Fifteen actual unchanged statement fences and safe guards passed separately; they do not replace compilation. No fresh compilation was run by this reviewer.

Independently verified selected compiled graph20nodes=18proofs+2definitions,2161direct type/value occurrences; all29 required actual producer/canary value pairs exist. Original ready15nodes are exactly equal in name/type/value dependency lists;1367readyoccurrences/23readypairs are separate. Scoped graph is not the complete project registry.

## Remaining reader obligations

- R1: Clarify source-card guarantee and boundary notation: z=0 is allowed by the full result but has margin 1 and constant loss 1; it never belongs to the zero-margin branch. Current worked example gets this right; remove the ambiguous trailing phrase boundary segment, including z=0.
- R2: Give the sourceHinge definition highlight its own construction and exact intrinsic norm/inner binders, with no FD or theorem proof flow attributed to the definition. Describe the second complete owned Bool-family definition in the reader/module route without adding invented premises.
- R3: Make helper versus source scopes explicit: only hull and terminal carry FD; affine/support/activity helpers retain intrinsic real inner structure. Coordinate-free source specialization is not a separately certified isometry/functor.
- R4: Disclose generic SourceSubdifferential admits arbitrary EReal inputs whereas source Definition2.20 uses proper functions; both actual affine components and hinge are globally finite/proper so this instance has no outside-domain query. Keep borrowed P/D/Q, C, M, S/U binder distinctions.
- R5: Attribute one printed Example2.27 with three cases; twelve helper proofs and two definitions are library constructions, not thirteen source results. Make each existing highlight declaration-specific rather than reuse terminal proof prose.
- R6: Preserve full both-directions equality, global all-y support, ordinary hull, alpha endpoints and genuine mixture. Show branch conditions with the terminal highlight/formula, and verify actual expanded rendered source formula during FINAL rather than infer correct pixels from JSON.
- R7: Preserve producer explanation: affine uniqueness via y=x+g-a, actual proper/convex/finite/continuous components, actual Bool maximum, exact active cases and pair hull. Distinguish curated four-link route from 23 selected proof-value checks/full registry.
- R8: State exact five scalar canaries: three full branch equalities, mixture-and-rejection conjunction, and all-x zero-vector case. Do not claim 2D certification, new tests, or a z=0 boundary instance.
- R9: Update current-stage gate/status and remaining scope at integration using actual new evidence. Historical focused/root/Tests claims are not this migration CONTRACT acceptance. Preserve four highlights/four curated links/three notation entries/one source card/fifteen shared declarations and other Book subtrees; next2.28, nine Chapter1 gaps, Chapter2 and whole Goal remain required.

## Repairs and acceptance limits

Required mathematical repairs: none. Required metadata/binding repairs: none. Nine reader obligations are pending integration/FINAL, including ambiguous source/comment z=0 boundary wording; mathematical source terminal itself has no such error. Preserve unused API v1/pre-use qualifiedv2 and read-only lookup diagnostics; none is a hidden mathematical repair.

BODY acceptance does not approve combined root/Tests/harness, current reader text, site, registry, FINAL, immutable package, PR, Chapter2/book/Goal completion, merge, deployment or retirement. Next2.28 and remaining Chapter1/2 obligations persist. Exactly13 retained proofs+2 definitions+5 old canary proofs; zero new mathematics/TEST nodes.

All listed files were read as raw bytes for integrity. Semantic review examined source, actual full module/canary, frozen signatures/contexts, neutral reconstruction, actual types/APIs, observed logs/fences and graph. Administrative inventory/history files are checked only for relevant provenance and integrity, not blanket recertification of unrelated contents.

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
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/30_lower_worker-v1.md` | `82b10200edf3e86cdbc861a18a957dde9bbfa3d169d9b44135dece4b8b94c15d` |
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
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/check-scoped-diff-v1.py` | `fd5a7cc374d0d995bee7be3bf0198cb7b0f0b2726ad1e5849a3f69ab4dcd55e8` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/commit-owned-v1.py` | `483778b8d545c2f25556fc3bbba92a6c43669a2037e512e4166e16f97666da8a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/common_v2.py` | `bb90cae0fe035a60e7e2339aba12a5dca1fa0d69d98f30abd8fe9102c216cb0b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/compiled-dependencies-v1.json` | `bf2dc7ee2483295b55525d5a0b2a73dc8dc66a9a568926843410bb1a6543cd8c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/compiled-public-graph-v1-01-exit.json` | `e43155d5f91451407a0d26bed88f9a0824bf9ea96fce539accf1e676a6c9ccee` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/compiled-public-graph-v1-01.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/compiled-public-graph-v1.json` | `31a1d42e876fe3474f6d58bff55e5181072f35ce874c0aee11c09305d3e0851f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/compiled-ready-graph-v1-01-exit.json` | `2073f508da267d6ffcf8b46f5a0d66a07ec06fcce320c472e223788fe01e95c6` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/compiled-ready-graph-v1-01.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/compiled-ready-graph-v1.json` | `c95134e02278bd6d5594e3564b59d496f549b9da5b338b434dce4e28312b68cc` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/contract-binding-audit-v1.json` | `ece59a03f392fcf267d15ee64e15f6084c3e7548b2cd36a5eb7d801c5df2427c` |
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
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/historical-raw-supersession-contract-v1.json` | `8ed01c2363cce75f2d7f2240a0e13dc1eabb75509eaa2c07a1eecb19553cba4a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/historical-raw-supersession-v1.json` | `936e7bb419668db5aadf88230554dc517989f0dcec8c589723e47b68dda69cae` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/history-site-helpers-before-use-v1.json` | `849fb600035cb8fbbaa783ef40f46ae6bfb9859720f75c68763cd2d0e1d7f2da` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/integrate-reader-v1.py` | `909177882dc34bd60db7b1f8aa3a51241efadeb21e74e797465e731f68cb3c94` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/integrate-reader-v2.py` | `af1313435bf4321b25c02f00cfa6f64a21d390c52ae8de5a578720c0d11923d1` |
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
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/native-public-fences/affine_continuous.json` | `a17dde42d08a88cf52c45d93935d9054f6a9c466389fa8dfb25a2869c46c765d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/native-public-fences/affine_convex.json` | `adab90b5989e826bede023fc0175ae9de9953dfb86bbdbd8fe95377548162f17` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/native-public-fences/affine_proper.json` | `1f3dabdbc09444073aa32bae67ebdf11656c317f14fd80e0942641684ea66a52` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/native-public-fences/affine_subdifferential.json` | `d7f58fef6737dc7c2f2799f3c47f9e755e0810f62aee2947fc0506b6b10f3152` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/native-public-fences/example_2_27.json` | `fe1632f513f65844092f15f0f1c84fbc4dd8ca95086fefbbc49812fb5c205e53` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/native-public-fences/hingeFamily.json` | `3bb0879d312389412e5485f602eb38a08e3958e179e8cba43605f7425d3c73b3` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/native-public-fences/hinge_active_negative.json` | `11b0dd830d1fe6bef6c701e9a50cd6a1eb93731e8c1b659431edb85685537552` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/native-public-fences/hinge_active_positive.json` | `7567cda34f0ae353a08b702e84384dcb3636f139ee63f71ec0225611f8a74122` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/native-public-fences/hinge_active_zero.json` | `1fb47d3265f21d30144cb5a735555a1476191001fa7d7841f8202c4f779763d9` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/native-public-fences/hinge_family_false.json` | `8ddc9f02ab7a41a56f0978cfa44fa5bb12da59d1c8eb820e1f4facf4a39e8a27` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/native-public-fences/hinge_family_support.json` | `dd8e8354c57b0358973c1d4e25c63dd1cdba32d2db4b257436f98a0e9b667de3` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/native-public-fences/hinge_family_true.json` | `cbc849e25f01798b1f0d864274df6b0bcbf1e2841a5cb21a03538827a89a696b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/native-public-fences/hinge_max_identity.json` | `9b55852fc1fa8483a2e01aa0538672340f649f327792c4e2928b9e926d674536` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/native-public-fences/hinge_subdifferential_hull.json` | `2911ce357d99eac65f871bb1a1a6387541f7ce89c99c139d8061557b5382a745` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/native-public-fences/sourceHinge.json` | `df112515924fe42259b178c776b61a751d05e240e6fa7489c6da6082c4e44baa` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/pinned-APIs-v2-01-exit.json` | `0ee2feab4034d46acbf188b6c4f245a1b8cc358501a5cc4e7a9c3b8e4c0aea7d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/pinned-APIs-v2-01.log` | `eac6f600cc328e02001ffaa82ad007dfd9dd42b39617303908cb6c124fa1c7dd` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/prepare-contract-review-v1-01-exit.json` | `9ac753e45591f50e9c5411c92b7e94bdb877a9dd0789ff7558bb521a5a0a0967` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/prepare-contract-review-v1-01.log` | `c6ed16deca51b76b7be6c447984be8669b52cbedbfc3050b3f37b7b958d260f2` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/prepare-contract-v1-01-exit.json` | `0243b899a639e6bf9442e334ddc737bb2cd495e768d93398b683fe596e3eda0a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/prepare-contract-v1-01.log` | `bbf24a6a2b21133995a20006977d783c6edd66851dbd326b1ea456fff73e7781` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/prepare-contract-v1.py` | `ffb4633cc6d27600c4d8a3aee0380731636ae2d5913dbf0cda278fdf9737d19f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/prepare-readiness-v1-01-exit.json` | `27a7895455e848d635ece64d6a7cf8601c0b9ca16a80d531a270d1291a06a6f6` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/prepare-readiness-v1-01.log` | `a92b72a7e47b415d1bfe78fd65c0608723457ab1443da002f1e09f8df6626a2a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/prepare-readiness-v1.py` | `f320f3ecb042d9e1e10d47447781bf151ae5b892b513e759e19feccef3844359` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/prepare-site-CLI-v1.py` | `1752c325383677bd5f07317f4faf6f04bc4d3cdc1032d6b8fc74fb0d28e10fe6` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/preserve-contract-native-v1-01-exit.json` | `3ef1ee1205660e118b00210fe007ce9cb4ce97a0bea89c5d688e336bee705a0c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/preserve-contract-native-v1-01.log` | `2593ab45223abe18c8e98ebd794ca1be801a29e92159a78231439872a5100491` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/preserve-native-prefix-v1.py` | `f949ca2d8b461c51a23ed08858cbffd4222575a76cd534733969ab7daa9ae2f9` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/prior-contract-binding-v1.json` | `8edaf0708c89b1eaa4fd8fa6148f14dc60b36679f93e044f91a40086bada2abb` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/prior-delivery-raw-binding-v1.json` | `9c67ca86a3deb33975426372efb61efb9ae30eadf23e92674ead6b7555151535` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/project-gates-v1.py` | `ed0a25b15bbb98d98b8f893e72cc6470e3eaad716893cd2165d53f29dacb88d9` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/project-helper-before-use-v1.json` | `189e8a137c9c5ca9b3b719522c94a36d0b02f98e10bd4d0a67ae59dd1b1fa24d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/proof-obligations-draft-v1.json` | `3f3c3ba24e43f11c02f8bf6e6dde19ecfd9c3c4ec2784ab1ab839621781ce21b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/proof-obligations-proving-v1.json` | `b3501a69daaf69fc385f7b7ca4fe45fb99a7e4e61fcdd6aa95112ad9f10ee04b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/proving-lifecycle-v1-exit.json` | `61d8148568c1fd6b23f9f33cc03ef4d1f4f0ae4383f0ba8ce0c8ce5e8e5fd7bc` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/proving-lifecycle-v1.log` | `7385ef46b72371712548b49a946234a93288bd3e85eec855d977c627747d75f1` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/public-actual-bindings-v1.json` | `086f8a544e4b7d4d31a77447df742a404aec0f64d2e33d0f32cc42f628b05794` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/public-all-axioms-v1-01-exit.json` | `fb96ab518d957158524373224563c2261c314062ae239a2d26662bc7cbe78b91` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/public-all-axioms-v1-01.log` | `806bf7b2e4297436c7b2a59825b74ee9fe2231300188757ab3bd0df1f333dbdb` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/public-body-packet-v1.md` | `9c40887f46708296da549916cd25c3d05975decb08cf004053ea43e5ecfe7dbd` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/public-body-v1-01-exit.json` | `e2f2ddd901be0abce1eee0b43675b047e5f3222ebf03cb2e76e1a1c54ba8d649` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/public-body-v1-01.log` | `84db561e04b0804227f611fe7a8ed4af794f9a992a5d0b3db90d5ac483de0c0a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/public-canary-focused-v1-01-exit.json` | `f009dee19920945afe225557b0503b890766cc90248677e2509f32f255e12611` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/public-canary-focused-v1-01.log` | `46a832623c4190eb077453e2b5c767fdf3ac0331894da797515890fac2f6eb66` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/public-fence-affine_continuous-v1-exit.json` | `8c2c8df91d1e1edd42fa8d2531f9d95373a98dde37baeab9b6c5367981b25f4b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/public-fence-affine_continuous-v1.log` | `a17dde42d08a88cf52c45d93935d9054f6a9c466389fa8dfb25a2869c46c765d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/public-fence-affine_convex-v1-exit.json` | `fff1dbcd9960fda7d1666be97d82118665b994a484fd91de0d678a5e026647d7` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/public-fence-affine_convex-v1.log` | `adab90b5989e826bede023fc0175ae9de9953dfb86bbdbd8fe95377548162f17` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/public-fence-affine_proper-v1-exit.json` | `a83a2c12d9c760ab9d459ed7bef5defaddc866bbc50323d3ba3a8d8982d08507` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/public-fence-affine_proper-v1.log` | `1f3dabdbc09444073aa32bae67ebdf11656c317f14fd80e0942641684ea66a52` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/public-fence-affine_subdifferential-v1-exit.json` | `c43c83070862bdcd362fb348cbb3ca5e9d833b2ec96233ed77c4c4a9a9724509` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/public-fence-affine_subdifferential-v1.log` | `d7f58fef6737dc7c2f2799f3c47f9e755e0810f62aee2947fc0506b6b10f3152` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/public-fence-example_2_27-v1-exit.json` | `9d9105f981df02b9397b40fb8ae08907b2e67e56694c9aea833aa3bf9219a808` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/public-fence-example_2_27-v1.log` | `fe1632f513f65844092f15f0f1c84fbc4dd8ca95086fefbbc49812fb5c205e53` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/public-fence-hingeFamily-v1-exit.json` | `1752a69571caf48d1f4cffbab7343b59aa2507f9243ec0c05fef8e5a095e343e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/public-fence-hingeFamily-v1.log` | `3bb0879d312389412e5485f602eb38a08e3958e179e8cba43605f7425d3c73b3` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/public-fence-hinge_active_negative-v1-exit.json` | `c710a2aec916f961fd9258e7bf615df0219ee6edca5b67604312d4a558e558df` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/public-fence-hinge_active_negative-v1.log` | `11b0dd830d1fe6bef6c701e9a50cd6a1eb93731e8c1b659431edb85685537552` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/public-fence-hinge_active_positive-v1-exit.json` | `6c84ecde25a09c627f1fc25ee0a9df429b1b640ce04348444a66d31bfb719d37` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/public-fence-hinge_active_positive-v1.log` | `7567cda34f0ae353a08b702e84384dcb3636f139ee63f71ec0225611f8a74122` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/public-fence-hinge_active_zero-v1-exit.json` | `395b2d821e4165f58377528f94baab28f1092bcc744647302b396d0492616f57` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/public-fence-hinge_active_zero-v1.log` | `1fb47d3265f21d30144cb5a735555a1476191001fa7d7841f8202c4f779763d9` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/public-fence-hinge_family_false-v1-exit.json` | `321135182467ab9f57655ac2e1e534662d79bda907559cf63a488659b830d846` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/public-fence-hinge_family_false-v1.log` | `8ddc9f02ab7a41a56f0978cfa44fa5bb12da59d1c8eb820e1f4facf4a39e8a27` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/public-fence-hinge_family_support-v1-exit.json` | `ddfcf2bf73026efc1a0f5c1e0d326268517bf7330acab8776476e3ba4e06b745` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/public-fence-hinge_family_support-v1.log` | `dd8e8354c57b0358973c1d4e25c63dd1cdba32d2db4b257436f98a0e9b667de3` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/public-fence-hinge_family_true-v1-exit.json` | `79dc4634bf78b64141fccb49c234e9853858cff5e1726bd7da18194cc8e75de5` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/public-fence-hinge_family_true-v1.log` | `cbc849e25f01798b1f0d864274df6b0bcbf1e2841a5cb21a03538827a89a696b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/public-fence-hinge_max_identity-v1-exit.json` | `e7a07aa9f5658b2e1064ddf665026ce242e0dca69ff0936d36c2310534b78737` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/public-fence-hinge_max_identity-v1.log` | `9b55852fc1fa8483a2e01aa0538672340f649f327792c4e2928b9e926d674536` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/public-fence-hinge_subdifferential_hull-v1-exit.json` | `e1be5798a75f8c6bd1638913dfa882ebbf80f15b2cfcebcdc5d45947f91e8631` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/public-fence-hinge_subdifferential_hull-v1.log` | `2911ce357d99eac65f871bb1a1a6387541f7ce89c99c139d8061557b5382a745` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/public-fence-sourceHinge-v1-exit.json` | `06424e03b95c360e0d99603e7e39bc847e55f2f0e08a583639e5e35628f7940b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/public-fence-sourceHinge-v1.log` | `df112515924fe42259b178c776b61a751d05e240e6fa7489c6da6082c4e44baa` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/public-named-declarations-v1.json` | `81c672ab36eaab01f913aeb21a20ef7e6629ba81a04d3f15be43d52f16e73bfd` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/public-safe-affine_continuous-v1-exit.json` | `49cb3f5ea39619dd9ed4ba81b78644609ec830e14108faacfad2abe1d4681d49` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/public-safe-affine_continuous-v1.log` | `9daad7ab206bcbadba88133e8bdd56bba694e36e0994779d9e54e376f5cc2109` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/public-safe-affine_convex-v1-exit.json` | `cda3c7079f09a1fbb664942ec44ddba944b18606ffa59efbc9cb3a4cfa4c02f5` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/public-safe-affine_convex-v1.log` | `c96c016c5fade2835d6ea6fc69b51afb90e04a5982f105e3d4b37a0daadd3167` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/public-safe-affine_proper-v1-exit.json` | `d7492572d5b72324911e7883e8d63c0c58253737807813c8e19bb81331cc5411` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/public-safe-affine_proper-v1.log` | `c40c719469df54be04ef18ea63670fe611481e2a13e6cda75204d4881b3a14e1` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/public-safe-affine_subdifferential-v1-exit.json` | `1e9dd191872581c6fa918514ac91b2901224f40c62929f5a4f04ac8506d51ed5` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/public-safe-affine_subdifferential-v1.log` | `07cc206ac887c412cb508adda2482dbe38132aa9a2c15cbe4b623322305140c5` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/public-safe-example_2_27-v1-exit.json` | `31c549ccfe8a0b0e358b5dfc5a9f5f69d9633f6ac88e3e9247a4e4ca2c13b092` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/public-safe-example_2_27-v1.log` | `e8f5f6e930b48108f08ae23d18fbaed89adcfff36863cc655458e69dbe16f9ac` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/public-safe-hingeFamily-v1-exit.json` | `b828a7e3b6c4e13b1f12948763354441c3eb59cfd910c7ade7ec14aac9c42fe2` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/public-safe-hingeFamily-v1.log` | `83878e53b9eb6f09c88b424d7846b79902429b23a57464cdc336b9ec237e0285` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/public-safe-hinge_active_negative-v1-exit.json` | `ebe00dd5637862589f7ccccb1b42dc5ea02d258c04ce8b1c643c412aca5e78a4` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/public-safe-hinge_active_negative-v1.log` | `f42850424fad24f61c9a7ab96067eda0184cdf7537471523328681195c2e7352` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/public-safe-hinge_active_positive-v1-exit.json` | `8044de8e3a7d421c50dccfbed7ecec005b572befbc5644c2ec011a65d1127e8d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/public-safe-hinge_active_positive-v1.log` | `bd64b59ac78517590f08f9a6fec6c47aff05e6b56d5dc621fc1764f62c221b62` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/public-safe-hinge_active_zero-v1-exit.json` | `18703cf0669b7bf84ffc38a60dc143b65f87b84d854567c748701f25ac29c53f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/public-safe-hinge_active_zero-v1.log` | `3c5217ab7fa00bbe0b847af123ef8ae108be77b2840b118849241c89b301cf71` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/public-safe-hinge_family_false-v1-exit.json` | `11805ed83707559234972b9cc0ff0d968359f7cc7e85894d9ead18d1926139ed` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/public-safe-hinge_family_false-v1.log` | `c29dc48d534f16b474106b92fe24689588428ef904a13de3012e97aedc1fee29` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/public-safe-hinge_family_support-v1-exit.json` | `97d6bda7a9c4be7b5f728df0c5d964cd890f1a0c043fdc42d876659c96527c71` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/public-safe-hinge_family_support-v1.log` | `8c4eb54ed95353e3b043af1cae26360026009b2a14cc078e2a93ad960a5edfcc` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/public-safe-hinge_family_true-v1-exit.json` | `bb078e59e06d171d6abe52d3faed249e09d80ee1ad08872528733ae1d259e2bb` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/public-safe-hinge_family_true-v1.log` | `b6b8b220bcdddf5d97e683324ed5c5b9f8510d5f820fc9ef45cee46ee87cab7d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/public-safe-hinge_max_identity-v1-exit.json` | `af66e64fd8e774f0a8f54bb0eeafc339f2acadc9b48f6460607f87bd420bccae` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/public-safe-hinge_max_identity-v1.log` | `63c3b2c9192f2a739606ef7ae0e31797f75ae5b34eeecc0360f9037163e33ce4` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/public-safe-hinge_subdifferential_hull-v1-exit.json` | `eb3bc68607da2d46228f32a7762c77bba4963f2208c79b300df79b102d66cf85` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/public-safe-hinge_subdifferential_hull-v1.log` | `386f58b3a99313e3643f2a8ec4fe6c8acc29dd908535782a5168112003276dcb` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/public-safe-sourceHinge-v1-exit.json` | `104b36832f6a347aee06521b86d9a7da4ea8ae0d98af277aec19ceaf1bd102ad` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/public-safe-sourceHinge-v1.log` | `c62895efd2918c34afe532e47ea3b46185a3c445a723df1fd93f179ce0355dbc` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/reader-helper-before-use-v1.json` | `246b9b175a4d1551c2a367a4e4eb5e28f8b1598de60d006eea07296ba5d4d261` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/reader-pre-use-clarification-v2.json` | `a905e04f8e2f0b2f5417338e8d796529e470d1b85be6b30ce3434233b3995d2f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/readiness-helper-before-use-v1.json` | `43fd3dc271f6c4a7f4bbc7107bca6bae99d5e1ffffb5ba49dfd835d53a7341c4` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/readiness-probes-before-use-v1.json` | `c284933b093a4e5f6f397c47a140c8b1b738d23d7ff30fae13c9b40286872237` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/readonly-lookup-diagnostics-v1.json` | `8329264a7b8db8ce2e2dd8cee465db530e35575464f3a0f455af65e05fba8ff3` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/readonly-template-lookup-v2.json` | `ae7cc7d9cb3ceb773c4534a8251e91c2ec00fd29a8fa9dcc3467889b2315af32` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/ready-dependencies-v1.json` | `9a5b3ee8e03af886b560e540a4c8aaa43c4b816184f389f0b85f6e85536ce1cc` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/reference-index-help-v1-01-exit.json` | `676a5e7240af8baa80b13dd94a65b853ec5e4c8f14a5d5b4519e4189a8d9b56e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/reference-index-help-v1-01.log` | `6943acba1d20272cfd239404bfaaa8457d0205a56876004e7c3fed2df97fc3d8` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/reference-index-manifest-v1.md` | `c02cad8b52909c3611466365fac8615d1b5888d610c821bf6f9fdbecafa47a2d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/reference-index-scope-v1.json` | `fea634e5bdedee780a6c8de90d77f53d80d8283bdbca007d2bde2746b13f6736` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/reference-index-scoped-v1-01-exit.json` | `956d22c088acdc541ad4ed43c59eb7e87d6d46a01fab75ab0998c61542406a14` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/reference-index-scoped-v1-01.log` | `6088540fe91064545f51b3b83c91c7e78e752e1b7af2dc52e79ec2fb1cf0d856` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/retained-body-trial-v1-exit.json` | `4ed63f03456c2cdc032bab789e1566b543ff78596e961337d9dbcf7c55b73e8c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/retained-body-trial-v1.log` | `7bab803d72fa3add664b4cd60fa1cb68a2efaf24d062a1e9cd8402530f3f8089` |
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
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/revalidate-bodies-v1-01-exit.json` | `78db2084b98c036b3ba559d094268431b2628d6b5bd1f4566fdc2469631f27c4` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/revalidate-bodies-v1-01.log` | `5a27d776b119424a7a92bc07277e70a115da7b55c161be4e05c737bab057ff3c` |
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
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/snapshots/contract-reviewed-runs--lifecycle_sessions.jsonl.txt` | `67ade5cdfbca60516812e84472e01d21b97ccf314f11082dfe42f4d75da22c8e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/snapshots/contract-reviewed-runs--trials.jsonl.txt` | `382461a06e227b8fc2de3a6f61cb14579f138dbad1fab80a6b73f0bf845a3afd` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/source-contract-inputs-v1.json` | `d3150738bec5ee58b40450d8bf6a3dd3c202d0cb8a1501715571d188e3ca41b0` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/source-contract-packet-v1.md` | `cf698f8eadf4dc00c265e2b6505862253e9fc12fdd41ea6308c59fddd394ea39` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/source-contract-receipt-v1.json` | `33572c3ecb66565a29dc986ccf40bee30b08ca535cb846b60a408409d76dae64` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/source-contract-review-v1.md` | `82df845ae1637e9a8be2bc65b3d68ccfbe8ea0c70d70d0da40c794d9d7c61d2a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/source-printed18-pdf30.txt` | `79a3aacef74fc16fd80b21ef87043e0ff5999ff6cf540e4741f09ca6c6447edc` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/source-visual-read-v1.json` | `788452a98c1ff3dd942525b855d2886753bcb22b44088ed0fdf51ddc4b9fa37e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/stabilized-leaf-selection-v1.json` | `12cd1a8b6dda56977169f5cfa522ac5ec2dc05ddd7fd12fe9488cf5ae002b8fa` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/stabilized-lifecycle-v1-exit.json` | `c39a783ffeb9b5d7a0eb24271203c4859b5a5dcb94c3a2d22fc9b5ada2e0856a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/stabilized-lifecycle-v1.log` | `d6568d36e9350dc644f1a93150df290bd8bc32107b2ba1c015a0f1c7fbc17646` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/statement-fence-help-v1-01-exit.json` | `bde4bb43667bbab98d89dfe53e527b74cb34c6e6cb72b64a3ec91cf6cffb7743` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/statement-fence-help-v1-01.log` | `4f4fca9dfaac7a7c3de8025d3d0f7c4ba58d1f4b33feb08d19e12229942dba75` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/trial-log-help-v1-01-exit.json` | `18ccb79d5a656b73b7daaef9bbaf62cf254c0e0e0e56b5105631dd8a6dbfd932` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/trial-log-help-v1-01.log` | `ea7bd7e4d64216b46f554a90e02a3d58b4fcbe72766c2f7b316b656b94d19b32` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/verify-history-bindings-v1.py` | `11e64311756a9bbdbb723e2668cc7c116d3cfe97684650ea44c0de7c88ae5398` |
| `E:/ABRL/worktrees/research-online-book/runs/online-hinge-migration-20261007/verify-registry-v1.py` | `fc8da2753c78189b2bae9aa92f27e468dbf8dbd5b515192549453932f6d44388` |
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
| `runs/lifecycle_sessions.jsonl` | `fb9019960b1cf6a529e75b73b33a4ffdcdc6c122828fa8916fe076bbfb376364` |
| `runs/trials.jsonl` | `4c8f0b0f10acd4083bf441f7898ac30d9d1cc05d3d7285504031b86e4f65a9ea` |
| `tasks/ONLINE-HINGE-MIGRATION-20261007.md` | `3e67077c6507dcb51b627d82499630c878e378dee7c69b5708d966dba5656d5c` |
| `website/content/chapters.json` | `6f09376f4d7621dd4b678602b25dfe5ada4144bf8b88dbed1dd5e881af7b3302` |
| `website/content/highlights.json` | `b661fddde803913ef1351a21dfe520c9949b515762a4b174ed387ef6e7787dac` |
| `website/content/readings.json` | `f563f9c38434f8bd7192c1dd83f3dd646ce1c48a2301beb352bd15ea2cd093f3` |
| `runs/online-hinge-migration-20261007/public-body-inputs-v1.json` | `6c31291d56631a84c2f230b9bd6a1ee338c930a4b8bd4e5afbb737c3cf7dfe45` |
| `runs/online-hinge-migration-20261007/source-contract-inputs-v1.json` | `d3150738bec5ee58b40450d8bf6a3dd3c202d0cb8a1501715571d188e3ca41b0` |
