# FTL sharp CONTRACT source review v1

Overall verdict: **rejected pending versioned metadata/enumeration repair**. Mathematical target verdict: accepted-with-explicit-delta for all N01–N13. Required mathematical repairs: none. Chapter inventory verdict: rejected in its current form; corrections below do not alter mathematical contract version1. No proving authorization or body/package/chapter acceptance from this receipt.

Actor `/root/source_reviewer`, distinct automated source reviewer with prior staged source/CONTRACT/BODY/FINAL history. Requested GPT-6 Astra / medium; runtime model/effort unattested. Not blind, human or external review.

## Source and exact context

Fresh cached original PDF SHA cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17. Actually viewed original PDF16/17/18 images and read complete PDF13–19 maintext/history/exercises. Source Theorem1.3 fixes initial1/2; proof printed5 gives first-round1/4 and refined1/4+4sum_{2..T}1/t, then coarsens to harmonic/log. Actual meanPredict retains strict-past mean; empty empiricalMean0=0 is not initialprediction. The two new targets match the displayed source bounds; neither adds probability, stability, regret or optimizer-existence assumptions.

Read actual full FTL, Mean and Foundations contexts/bodies for contradiction checks. Existing Theorem1.3 calls BTL on Set.univ using proved GLOBAL minimizing means; feasibility for the source interval comes from empiricalMean_mem under played support. Thus the source min conversion is genuine, although it is not itself an input binder to the terminal. No need to require an interval-valued BTL call when the global minimizing theorem is stronger. Existing stability uses an algebraic square update rather than literally copying every printed triangle step. This is a valid proof-route difference; no new body acceptance here.

Actual13 neutral closed Props and five retained exact-type rfl checks pass; new2public/sixcanary proof bodies and their later actual type identities remain pending. Neutral definitions a,b,c match empiricalMean,meanPredict,probeTargets; decoder correctly separates per-round changing-mean difference from cumulative fixed-final-mean regret. Typed Finset.sum_range_succ' yields shifted tail PLUS first term; positive horizon justifies the T-1 split.

## N01–N13 seven-slot comparison

### N01 BanditRL.OnlineLearning.meanPredict_prefix

Contract target verdict: accepted-with-explicit-delta

- **objects**: Two arbitrary real streams y,z and actual meanPredict.

- **quantifiers**: All y,z and natural t.

- **assumptions**: Equality at every i<t; no interval premise.

- **conclusion**: Equal prediction at t.

- **constants_indices**: Initial1/2; source round t+1; strict indices0..t-1.

- **information_order**: Excludes current/future observation. Deterministic prefix causality.

- **source_delta_boundary**: Library structural consequence of source strategy; total real streams generalize interval game; no stochastic or execution claim.

### N02 BanditRL.OnlineLearning.meanPredict_mem

Contract target verdict: accepted-with-explicit-delta

- **objects**: Real stream, actual prediction, closed interval[0,1].

- **quantifiers**: All y,t with bounded strict past.

- **assumptions**: Every i<t lies in interval.

- **conclusion**: Prediction belongs to interval.

- **constants_indices**: At0 predictor1/2, not emptymean0; endpoints included.

- **information_order**: Current outcome need not be bounded for prediction feasibility.

- **source_delta_boundary**: Structural source prerequisite; no global/future bound.

### N03 BanditRL.OnlineLearning.empiricalMean_update

Contract target verdict: accepted-with-explicit-delta

- **objects**: Real stream and actual empirical means.

- **quantifiers**: All y and positive t.

- **assumptions**: t>0 only.

- **conclusion**: mean(t+1)=mean(t)+(y_t-mean(t))/(t+1).

- **constants_indices**: Real denominator t+1; includes exactly current y_t.

- **information_order**: Update after reveal, sufficient statistic rather than assumed loss stability.

- **source_delta_boundary**: Algebraic helper valid for unbounded real data; t0 excluded even though separate identity could exist.

### N04 BanditRL.OnlineLearning.meanPredict_stability

Contract target verdict: accepted-with-explicit-delta

- **objects**: Actual predictor versus next hindsight mean at same y_t.

- **quantifiers**: All y and t including0.

- **assumptions**: All i<=t in[0,1].

- **conclusion**: Squared-loss difference<=4/(t+1).

- **constants_indices**: Source later4/source-round, Lean t+1; initialcoarse4.

- **information_order**: Prediction strict past, comparison mean includes current target.

- **source_delta_boundary**: Retained coarser initial bound is not the source sharp1/4; newN06 supplies that separately.

### N05 BanditRL.OnlineLearning.theorem_1_3

Contract target verdict: accepted-with-explicit-delta

- **objects**: Same actual prediction stream and final empiricalMean.

- **quantifiers**: All y,T>0.

- **assumptions**: Every played t<T in[0,1].

- **conclusion**: Difference of sums<=4+4 lnT.

- **constants_indices**: Both sumsrangeT; fixedmeanindexT; natural log realT.

- **information_order**: Causal predictions, final hindsight comparator only in analysis.

- **source_delta_boundary**: Source min represented by actual feasible/global minimizing mean, established by Mean APIs; not arbitrary comparator/assumed certificate. No minimax/IID claim.

### N06 BanditRL.OnlineLearning.meanPredict_initial_stability

Contract target verdict: accepted-with-explicit-delta

- **objects**: Initial prediction and one-observation mean.

- **quantifiers**: All total y.

- **assumptions**: Only y0 in[0,1].

- **conclusion**: Initial squared-loss difference<=1/4.

- **constants_indices**: meanPredict0=1/2; empiricalMean1=y0; source first-round0.5 squared.

- **information_order**: No future restriction or hindsight prediction substituted.

- **source_delta_boundary**: Exact unnumbered source bound printed5/PDF17; endpoints sharp, future unrestricted. New body pending.

### N07 BanditRL.OnlineLearning.meanPredict_regret_refined

Contract target verdict: accepted-with-explicit-delta

- **objects**: Same actual prediction and final feasible empiricalMean.

- **quantifiers**: All y and positiveT.

- **assumptions**: Every t<T in[0,1],T>0.

- **conclusion**: Actual cumulative regret<=1/4+sum range(T-1)4/(real t+2).

- **constants_indices**: Exactly source1/4+4 sum source2..T1/t; T1emptytail; all denominators>=2.

- **information_order**: Same stream/run; no assumed stability/regret/argmin input; Mean APIs supply source-min interpretation.

- **source_delta_boundary**: Exact unnumbered source bound; positiveT excludes T0; not universal equality or optimal later constant. New body pending.

### N08 FTLSharpProbe.endpoint_values

Contract target verdict: accepted-with-explicit-delta

- **objects**: Constant0 andconstant1 streams.

- **quantifiers**: Closed four-conjunct test.

- **assumptions**: None.

- **conclusion**: Both initial differences=1/4 andboth<=1/4.

- **constants_indices**: Initial round0/mean1; exactquarter.

- **information_order**: Fixed prediction1/2 independent of target.

- **source_delta_boundary**: Planned validation of two endpoints, not new source theorem or all-horizon tightness.

### N09 FTLSharpProbe.interior_value

Contract target verdict: accepted-with-explicit-delta

- **objects**: Constant midpoint1/2 stream.

- **quantifiers**: Closed two-conjunct test.

- **assumptions**: None.

- **conclusion**: Initial difference0 andstrictly<1/4.

- **constants_indices**: Exact0,1/2,1/4.

- **information_order**: No uncertainty; initialpredictionequalsfirstmean.

- **source_delta_boundary**: Planned non-tight interior instance, not generic interior equality.

### N10 FTLSharpProbe.outside_interval

Contract target verdict: accepted-with-explicit-delta

- **objects**: Constant2 ambient real stream.

- **quantifiers**: Closed two-conjunct test.

- **assumptions**: None; selected target violatesinterval.

- **conclusion**: Initialdifference9/4 and>1/4.

- **constants_indices**: (1/2-2)^2=9/4.

- **information_order**: Fixed initial prediction remains1/2.

- **source_delta_boundary**: Planned support-necessity counterexample outside source game; does not contradictN06.

### N11 FTLSharpProbe.one_round_refined

Contract target verdict: accepted-with-explicit-delta

- **objects**: Constantzero stream,horizon1.

- **quantifiers**: Closed equality andbound.

- **assumptions**: None.

- **conclusion**: Actualregret1/4 andrefinedinequality.

- **constants_indices**: range(1-1)empty; comparatorone-pointmean0.

- **information_order**: Actualpredictor1/2,notemptymean.

- **source_delta_boundary**: Planned genuine newterminal instantiation; noT0 extension.

### N12 FTLSharpProbe.two_round_refined

Contract target verdict: accepted-with-explicit-delta

- **objects**: probeTargets0=0 andpositiveindices1,horizon2.

- **quantifiers**: Closed three-conjunct test.

- **assumptions**: None.

- **conclusion**: Actualregret3/4;<=refinedrhs;rhs9/4.

- **constants_indices**: Predictions1/2,0; comparator1/2; losses5/4 minus1/2. Tail4/2.

- **information_order**: Secondprediction usesonlyfirsttarget; same actualrun.

- **source_delta_boundary**: Planned nonzero/slack validation; no claim refinedcumulativebound sharp.

### N13 FTLSharpProbe.future_independence

Contract target verdict: accepted-with-explicit-delta

- **objects**: Constantzero andprobeTargets,time1.

- **quantifiers**: Closed conjunction.

- **assumptions**: None.

- **conclusion**: Predictions equal whilecurrenttargets differ.

- **constants_indices**: Bothpastindex0=0; probeTargets1=1.

- **information_order**: Strict-prefix producer instance; differing currenttarget cannot alterpre-currentprediction.

- **source_delta_boundary**: Planned causality validation, not equality at allfuturetimes or predictionaccuracy.

## Full definitions

Owned retained meanPredict: if t=0 then1/2 else empiricalMean y t, all total real streams/natural t. Borrowed empiricalMean: sum range n divided by n, so zero-prefix0 by totalized real division. Prospective test probeTargets: if t=0 then0 else1. No hidden stochastic/geometry binder. These exact constructions support neutral decoding; prospective test function is validation-only.

## Separate chapter enumeration decision

The fifteen rows identify the major formal theorem/bound chain, IID motivation/optimal mean/lower bound, regret/no-regret definitions, loss-dependence remark, prefix minimizing mean, BTL, stability, refined regret, harmonic comparison and asymptotic consequence. This is not fifteen proved leaves or a complete chapter denominator. HistoryBits and independent Problems1.1/1.2 are correctly separated; source maintext claims cannot be dropped merely because harder.

However the current ledger has stale package/status labels and collapses the broader p3 initialization into the p4 specialization. The p6 sufficient-statistic claim is not explicit in the ledger intent; N03 is relevant evidence but should not silently certify all streaming/computational claims. Source p2 W-superset-V permission and p4 minimax forward-reference need explicit semantic/deferred disposition, not newly demanded proofs in this sharp-bound package. Versioned ledger corrections/subitems suffice; no fixed mathematical header change requested.

**M1 (ledger metadata)**: Create a versioned effective ledger correcting current_package_only (currently stale Lemma1.2/seven tests) to this five-retained/two-new-bound/six-validation FTL scope, and replace stale Lemma1.2 CONTRACT-pending text by accurately time-bounded prior acceptance/delivery reference without implying chapter acceptance.

**E1 (source enumeration)**: C1-FTL printed3/PDF15 permits any initial point in[0,1]. Distinguish that algorithm family from the x1=1/2 specialization of Theorem1.3 printed4/PDF16. Preserve both source anchors and leave any unencoded general-initialization consequence explicit; do not weaken the frozen sharp targets.

**E2 (source enumeration)**: Explicitly record printed6/PDF18 running-average/no-full-history sufficient-statistic consequence as a C1-FTL subobligation (or separate item), with actual update/initialization route and computational-model limits. Also record p2 prediction-set W superset V footnote and p4 unproved minimax forward-reference as explicit semantic/deferred boundaries, not silently covered claims. No arbitrary increase in proof-leaf count required.

**M2 (prospective raw-binding metadata)**: Before intended appends/status updates, version the effective input/resolution map to immutable OWN raw snapshots for live owning FTL module, Tests root and mutable own task/obligation/retrieval/blueprint inputs. Separately enforce exact retained five proof/header/definition bytes and exact two new headers. Current229 hashes all pass; this prevents future false whole-file unchanged claims, not a current drift finding. Preserve original indexes/receipts.

## Binding and preparation repairs

All229 CURRENT v2 raw rows independently hash-match before/after. Historical v1 index is unaccepted: enclosing preparation log changed from empty to final stdout after capture. Direct v2 freeze resolves that actual stale-row issue; no target/decoder mutation. RUN-relative blind receipt resolution is now consistent with exact packet/report hashes; the failed root-relative FileNotFoundError and original helper remain. Actual blueprint path is proof-blueprints, corrected before review. These repaired issues are distinct from the new ledger/prospective-binding repairs above. All extant exit-record/log hashes inspected match.

## Stable future reader obligations

R1: Attribute existing5proofs/1def to exact Theorem1.3/prefix sources; new2 bounds unnumbered proof printed5/PDF17; six new tests/one testdef are VALIDATION, not six source results. Old theorem_1_3 remains unchanged.

R2: First bound ONLY y0 in[0,1]; refined T>0 and EVERY t<T in[0,1]; no hidden convexity/probability/global bounded future assumptions or T0 refined theorem claim.

R3: Actual causal strict-past predictor, initial1/2 DIFFERENT from empty mean0; current-prefix hindsight leaders only auxiliary; feasible prefix minimizers PRODUCED from actual mean APIs, not exogenous algorithm/stability/regret certificate.

R4: Exact source1/Lean0 indexing and loss comparison; refined tail range(T-1), realdenominators t+2>0, T1 emptytail and initial sharp equality; existing later bound4/(t+1) preserved.

R5: Source min over[0,1] represented by produced feasible/global minimizing final empiricalMean; SAME actual predictor and SAME horizon final comparator; no universal arbitrary-algorithm producer, minimax/IID/no-regret claim newly attributed to these two bounds.

R6: Actual endpointquarter/midpointzero/outside9/4 and two-targetactualregret3/4 versusrefinedrhs9/4 plus future-target perturbation with prefix output unchanged. Outside interval counterexample only validates necessity of support, not source admissible; named tests reuse real public proofs, nonvacuous.

R7: Preserve all Be-the-Leader/other cards/public notes and existing decoded formulas/curatedIDs/moduleglobs/otherBooks; bounded FTL card/notes+2 new source cards/notes and route boundary only. Actual current full HTML and source/formula pixels separate; proof-term dependencies verified separately from teaching links. Display readable formula proof, assumptions and folded exact Lean.

R8: Separate CONTRACT/BODY/type/kernel/fullfenceVALUE/rootTests/fullharness/site/FINAL/native/PR; retain blueprint path correction, receipt RUN-relative path correction/any failure/actual repair; original native headers unchanged. Exact stacked PR187 base not main. Chapter1 source reconciliation and main-relative gaps inclFoundations unwaived unless actual gate resolves; Chapter2null/incomplete,3-16unenumerated/requiredappendices/GoalACTIVE; no merge/deploy/live/chapter/Goal completion or external/runtime attestation.

## Limits

CONTRACT review only: five retained proofs/context checked, two new public and six validation statements not proof-accepted. BODY/kernel/guards/actual VALUE graph, combined root/Tests/harness, reader/site/pixels/FINAL/native/PR remain separate. Nine origin-main gaps including Foundations unwaived unless actual future gate resolves. Chapter2 null/incomplete, necessary appendices, unenumerated3–16 and wholeGoalACTIVE retained. No merge/deploy/live/chapter completion.

## Raw reviewed bindings

| Path | SHA-256 |

|---|---|

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/.gitattributes` | `705fd4d6451a31d36b3df7de96f83f30ac976c9b4a6d1e51671d8e2f33e2d0da` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/00_context.md` | `fb0bdb6d9f151148b5d7b9ba464af834400e1db19e4e533f187020c540cb096d` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/10_upper_director-v1.md` | `fa010e5720705758c3669dc874dc6ab1de539f034644c96d6dabf123e5fb321e` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/20_architect-v1.md` | `c4a9d449de1f5b575c6b79ed97871abdb70bcd313081cef2db162444d25e2b9d` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/base-PR187-fresh-v1.json` | `acd660165980d14dd9896f93fbda74bc3350eea822c59efc061f027c2599b4e2` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/blind-binding-audit-v1.json` | `016af6b12c63151a3899505c5d7e026ef07bfc67d6c4d90b96a8233dea71a06c` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/blind-decoder-receipt-v1.json` | `783fee0e66457b61b01cdbb71500eb2813667730248724888484c23fd6ead9a7` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/blind-decoder-v1.md` | `dc95ac8978ace5bc20659fda3280ae7bbaa5688ce8c751da02f163cd2eae2fa2` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/blind-packet-v1.md` | `64b504cf8a390f08da6b537009048a68ada5b0f4d2bac8420a201fcc6bfaf26b` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/blueprint-own-task-v1-exit.json` | `2b927d9dbbd212db07ff44959552940909c4c44dd173d7d3af589c29c487ff79` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/blueprint-own-task-v1.log` | `a643857d7d47cab31adf6770a9e9b692bbc6d42fc48091af6d477674c0eb8c55` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/canonical-worktree-audit-v1.json` | `bd614db8b96d1af82aefc20fa2e6d1313862ba22f6f7ab28836348ec4cc88ac6` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/chapter-ledger-version-v2.json` | `9d5f58e5f4b67b8039c3d92ec120902c39051505de9f6799455939df06766661` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/common_v1.py` | `713ad2dec42fbbd00f34c79f5c6faa5e99b09772f6ab72cb2a6a2297f657060e` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/draft-event-v1-exit.json` | `86b3dd49e81715e8d32308a233c1ba4f9ee9ab98c07ff7ff782bec5b3ff3de2c` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/draft-event-v1.log` | `1fd6acbd25e32a76afe75ebf9906778c0a500dd7761720d3d75fdd8d5235010e` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/draft-freeze-v1.json` | `1587daddb80401c826f3a348076040bc61eaafbac68060eaba2696f080da6dbe` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/existing-public-type-identities-v1-exit.json` | `53f1fbfbb80f81831ef982d4795a6bf958f397945b590f9d07e021567b9a2abf` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/existing-public-type-identities-v1.log` | `f168cb96d0453aba7860f5e6c0522731cda176ba752f2db13fa5c0b1bfd27249` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/fresh-fetch-v1-exit.json` | `f06f0291048173e491afc1f7531a8a123d860ffe4453b072f976baa609dabf47` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/fresh-fetch-v1.log` | `629538181a023831757fd00e792d7ef740ca5f38172c01a13e81e44deb412ae9` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/help-blueprint-refresh-v1-exit.json` | `5dcfd323917a8a6e226f99fbcff2ec32da8dd88fd7ab6177f3715141d89cdb9e` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/help-blueprint-refresh-v1.log` | `9ed3b46491b1470d6a0bebb1277e25f5cd8e06ea10039b1397e66397aa63e65c` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/help-frontier-refresh-v1-exit.json` | `2878268d3bddf19219bcbdaf74fb9d6296cc46c4bbfd5ec081d6c663651950be` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/help-frontier-refresh-v1.log` | `bff73ff554907d7c5dd50b99f2491f5675e93afb29829e402ec383fb52fe3cdc` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/help-frontier-shadow-v1-exit.json` | `74da8f3eb10ace738bb5780c306d2df4d1c7ac74b89507a4c55428ea28c65715` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/help-frontier-shadow-v1.log` | `ad548f6e24b3214fbf5796c632caa24debbaa21c6622f7dab8abe268f521de7d` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/help-lifecycle-event-v1-exit.json` | `3cbcacb6d3ce7c1128ac2ba5ea8c6159498d3639b47f95d38ee2d8dd443b2855` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/help-lifecycle-event-v1.log` | `b1e8b438a9b725793b9888d206e98a971ace3df200ec90ed9cb63eab26b28507` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/help-list-lean-decls-v1-exit.json` | `2be6702023304fbf1c241f406c06bfe8baf2e8780c7859cc843e775890164752` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/help-list-lean-decls-v1.log` | `258218f16a12b1a530d85ae83e6c2449237af8a0a1153bb35de40245d665b131` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/help-list-mathlib-v1-exit.json` | `fc4565ed34b585e7aa37460df779a13dc3c41b1af34eb797035695f0960ad8ba` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/help-list-mathlib-v1.log` | `eedc3e9609fdc7a3bcf76443a33933477de80dcc4ec9906b64a691e29b207e9d` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/help-list-papers-v1-exit.json` | `9bc5e4baacb510fa271315e206a0b1ced15e6cfb53342d2b154e30fc778cbdc0` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/help-list-papers-v1.log` | `57fdd9fadca031cddeec9da9c4ba947cccb3b1b155129de3a81b72b0c811a696` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/help-list-weapons-v1-exit.json` | `83791cc7a16a31323f8b21f892343f9d17e70bf5c57093701d01bc544be39ea6` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/help-list-weapons-v1.log` | `529fdc45da8d53249b6cea7712803e68cc0251026c7a66d1a067ac6413c9617d` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/help-memory-record-v1-exit.json` | `a8ac9cbb2126c8c2618951280b8c90cd73a9fa8716611971a78333c5137e3fcb` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/help-memory-record-v1.log` | `89e8a7b2bb8d4fd593f0705289ca3c4c63015e48d0e8c9cbe5b71cf2c7cc44f4` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/help-new-task-v1-exit.json` | `4b4fa3596b295c5c7f4c36a6d87c1ce0126e5d0c034e99f7a8a3b9a2b69c4346` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/help-new-task-v1.log` | `25eb9342c3094bee57187630bd149d2c522fc9f7ac7e65bebe5c198eba60ed99` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/help-reference-index-v1-exit.json` | `d61d22bbe0f88e1a8e95424ab07ee739c7182456654b224134f33f09bd6ddef4` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/help-reference-index-v1.log` | `6943acba1d20272cfd239404bfaaa8457d0205a56876004e7c3fed2df97fc3d8` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/help-retrieval-record-v1-exit.json` | `98e4005dfddd3a27fe73ad49f3be118b919d7d7df895ab286c26555e24fdfa20` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/help-retrieval-record-v1.log` | `73ac93f120215511ff0370d7ce100a9d0e83598ad882bcc5773cd1dc889b5321` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/help-root-v1-exit.json` | `3cdc0fe461d4db99d7aeb8146cc2bec4d0c7b407c2f6581769ab1d941cafa3d4` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/help-root-v1.log` | `daacf23e36eec4898dce3b3de02a07b71fb0f80f08e33e8dfe00722e7572970c` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/help-safe-verify-v1-exit.json` | `3d798faa6f053ed2ad38a2df176451552f595ec4d52984ac8810fa52125310ef` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/help-safe-verify-v1.log` | `1773541c625f225e5a9abc61985c3ad19e871cf31aa0cf89cc440b3d8398862c` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/help-search-memory-v1-exit.json` | `33c975c8041b24fdc7d2dfed7e9546aba8cb357abcc9555c8b1a8c08bc5d38f8` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/help-search-memory-v1.log` | `b2f23faf2d0ee17c305335680ebdb2b83ca61999d18021e355d22587d712b79c` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/help-statement-fence-v1-exit.json` | `1c2eb1b8d3273ad75abc75206521adb1dd04ff296b28e36c0f76d7ed51def5ff` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/help-statement-fence-v1.log` | `4f4fca9dfaac7a7c3de8025d3d0f7c4ba58d1f4b33feb08d19e12229942dba75` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/help-trial-log-v1-exit.json` | `c7ce18fe023e2d492982e29da685fd6a393dd4061d8fdb4c04b789e8aaf9704d` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/help-trial-log-v1.log` | `ea7bd7e4d64216b46f554a90e02a3d58b4fcbe72766c2f7b316b656b94d19b32` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/initialize-v1.py` | `be310b05b99028c198cff7aeb4fe9af63d15f0349e829162911923917f57846a` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/leaves/existing-public-type-identities-v1.lean` | `511adfc9a88ae89e8ad1e13fac3bdc60db8f666a93840d93de5c37e184752927` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/leaves/neutral-closed-props-v1.lean` | `6b32529120e3e99c55045c5c9775e6bd6172ea2dbc019ef8c5731c0796c14a2a` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/memory_digest.md` | `819d3b1ccbf8e90a197d88776c5bb5cea1d5e24de1664f3d47f77a85962c84e3` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/neutral-closed-props-v1-exit.json` | `5414b90889ad2bc22396356d1a2267d3ebd0c868b91ea2b0db8ec7a29051f842` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/neutral-closed-props-v1.log` | `f085733e36cade3e296cafa9261930731b2784c1abf2b7649a7d3248262acaf1` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/neutral-map-v1.json` | `880a114c099ce4601be032f259be4532395fcca40db451f8348c815010f1547f` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/neutral-type-bindings-v1.json` | `44b788203e0bfb970d026fd4c46464713eec650724eb1bcb2d5c849a26b512b8` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/new-task-v1-exit.json` | `a3f9d0e305a20ae5cd33f1c69ec893ad10b3948e894e753f016996303fca7666` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/new-task-v1.log` | `c475ab266bc56b2fd2cff01c77b58b09fb239d9a98fc41e3e1338f8fd4c15947` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/owned-blueprint-path-correction-v2.json` | `fba9c756261a47001b0aa60f3ecc8be2b3f3cf4c0aaa2f708e39ecd6cda4d183` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/owned-commit-paths-v1.json` | `f0d226792baef2d3dbfd18b3c44f828b91dbf8dd14ffdf794a927db02319f632` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/paper-boundary-v1.json` | `4b85e7690280863c2a4b3eaab46118453ac1aec397ef8563c47f7567bd57b4f5` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/prepare-chapter-ledger-v2.py` | `5f4aa1d51bd23a95d28547eff5a88de45c6812397d57a3fe91f7ce5239d4d555` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/prepare-contract-v1.py` | `9bdcb759e0c57d523cc3e040f7d61175e8d00ea47839673cabec60a79be094b8` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/prepare-source-contract-review-v1.py` | `1c7b1c1b2af3ea0efe1ced32dfe58b8b8e570d7d810ac27e01f068100a2f9d9a` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/prepare-source-contract-review-v2.py` | `2e0d89305e1cfeff083da704e825c9564b8c98f3ab09797ec141a12dbbc70b38` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/proof-obligations-draft-v1.json` | `43907c4ea54f572e789853a5722701f41ec9809ac14ea00e668b3510faec005f` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/render-source-child-v1.py` | `6d52161daad3f843069007576e8e0edb25408080b83c35c6fdf200967b61449b` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/repair-contract-receipt-path-v2.py` | `32471f2e4f041a415627e3f9af84f3eaf226400f5275ea9b92f81e47d2a78cfb` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/repair-owned-blueprint-path-v2.py` | `d8fcd88195f2b13ef8bbae86e02a536594defc71596c9c0eb5045f5c4394bcea` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/retrieval-actual-existing-API-v1-exit.json` | `be3cbe12d9bf428b6e9bfb37ea1fe4dca60bdf865ed6c0fe78576d38f021ced3` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/retrieval-actual-existing-API-v1.log` | `35ab87889ae18beafb1e31b1b1fe56599a8cd9904990d08d131ce9dd1bc5ea7c` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/retrieval-actual-sum-API-v1-exit.json` | `f2881258c0c4db3fba710ad3c47145bc7552e86bf12cc0f462b4ba0aef49bbe4` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/retrieval-actual-sum-API-v1.log` | `534fdc914e82b9579cc9d65e421f5122ae8005e1f71c5309fef5766b5d258735` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/retrieval-decision-v1.json` | `600c3e4123263a340b70260b11aee16613fb049adf3c7fe8bda39714589b320f` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/retrieval-list-mathlib-v1-exit.json` | `90a37fa3d6896b66e97238252521e075b42c83edf1830b2ca4cb12b0e3077287` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/retrieval-list-mathlib-v1.log` | `884fab88619a3d1adcafe89eecddd2d98f4be5c6fa61262862134dde9e51d225` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/retrieval-list-papers-v1-exit.json` | `9d860ddada2fed665e398d2b9ef187253c3ce4dc38af9b71dc9bd3ef07003eb1` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/retrieval-list-papers-v1.log` | `9acd333996a893a7b5ccad3e674ece26ef05c8b737e7816b33043b121583a619` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/retrieval-list-weapons-v1-exit.json` | `7fca58e30e0c7949e4f9173671ea615d757ff62e37998ae253653fe022b0fcdf` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/retrieval-list-weapons-v1.log` | `a6e4b78de1a30fcf5a0ee66b868eb3ac1bfa68d2250c713f61e690ae064f7ef6` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/retrieval-memory-meanPredict-v1-exit.json` | `1647d5c6873e826d2795077f79d5f83eca05f693b9e838c88aa463e02ce5b062` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/retrieval-memory-meanPredict-v1.log` | `35a78037890e88ed96a53b65e3f00d4b7b427edee8f60f48f5c2c7098a0096e8` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/retrieval-named-empiricalMean-v1-exit.json` | `b768fc2aa34615cee8f4b394b725d81668b88db8e603ff60ecb6e622da45474e` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/retrieval-named-empiricalMean-v1.log` | `e41d887b5516870d21e3bcedca1c4362d96aec9d485b03ce1d72b54720155b01` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/retrieval-named-meanPredict-v1-exit.json` | `5b3361949b74d219ccd0343e2fded2d2d8b7078526ad8de7bf8611c9db90bd63` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/retrieval-named-meanPredict-v1.log` | `d20e7d19c058e1624266147b329e24c252d649276b15407f075279d744d39a63` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/BanditRLProof--OnlineLearningAsymptotic.lean.raw` | `4d704d07b9616ca48a1ee56d47af7f5f8ca9e3797d2a9b47d373038a25d79d59` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/BanditRLProof--OnlineLearningFoundations.lean.raw` | `e23ebdca2f7ce21a16173c93390fd24d16ba36e403c9d084233f7480e75408b8` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/BanditRLProof--OnlineLearningFTL.lean.raw` | `8aee4c971fffbc79f2426fb308f50ec02b664b42a90fe1f85620a313df4c7a06` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/BanditRLProof--OnlineLearningHistory.lean.raw` | `3412177ab7dd0ac0e350d8fde7f91e61640d55743d1f17d15c62a65dd4492fc7` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/BanditRLProof--OnlineLearningIID.lean.raw` | `92af24e6a2c2b1054503492b2bad97cd17ccea2217439f6d2f8a7bedb0de3d5e` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/BanditRLProof--OnlineLearningInformation.lean.raw` | `72bef017a43c293d0d3c449707e4a0e058f4655c2483b54c3120d7b41c98135a` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/BanditRLProof--OnlineLearningMean.lean.raw` | `d65b3e5d5d2e33a0fd94722f1d7d9a09819c963c693e28bf854fae00f5280aa1` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/BanditRLProof--OnlineLearningRegret.lean.raw` | `231eda88cb1c45bf3bc9209bfbdd696fbfbe8a64b00303113a23cbc4dff3ca5b` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/BanditRLProof--OnlineLearningStochastic.lean.raw` | `0242481022883958afef677654fadd3f6e37b381f3fe463e3605f3eb0542f2bd` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/BanditRLProof.lean.raw` | `7cdb1969bad2f7b42cfd7a25f6d15747d0d49178dadc244b70ab1f9b8c92c5ad` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/docs--contracts--online-book-v1--asymptotic-context.json.raw` | `9451439b34caff169c02a8d7fc342aaeff19c49ebdd5af675e253a6fb5949512` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/docs--contracts--online-book-v1--asymptotic-contract.md.raw` | `d00992a19ea7631938e3930d47a86dc5dd1e2399d609362caf88e116bd42d04d` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/docs--contracts--online-book-v1--chapter-2-remaining.md.raw` | `079c709ea26586a8284aee236986a52c654c8a8805b22434442bee54152fbd4b` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/docs--contracts--online-book-v1--comparatorRegret_eq_sum.json.raw` | `3793629d88e754041c0f6ddd58f533f4ebce317dd40f91c2bd0429fcc6294c45` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/docs--contracts--online-book-v1--coverage.json.raw` | `fd7580c2d0ec040352317d3c53dc583a6b9b75a68b4026ebf3b38f7010a98f1e` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/docs--contracts--online-book-v1--empiricalMean_decomposition.json.raw` | `44b64de46ae002b1e8d510bf58488a6bcbb564aadae83df5aaab831360d9e883` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/docs--contracts--online-book-v1--empiricalMean_mem.json.raw` | `37ec1dd63937e5336b9a1a545ec9d36b796456cc67d6713ad6148af3ce62dda9` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/docs--contracts--online-book-v1--empiricalMean_minimizes.json.raw` | `95c3a3c93584a64a234731e6818f43241b01c91ea18278eda486511637052e87` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/docs--contracts--online-book-v1--empiricalMean_unique.json.raw` | `b586cd1a6e547d89d341c0e2c11a72518dbe1c1b91ebb03665ffaa408aa9a279` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/docs--contracts--online-book-v1--empiricalMean_update.json.raw` | `97e959f081525ce6b0081338a53cf951ca0f654063329c5097cc6a533b21cdf1` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/docs--contracts--online-book-v1--expected_square_decomposition.json.raw` | `2e69167dbb15e54ea97c34fcf4b5dbe392133fd7b813573fb6e3387ff3840d20` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/docs--contracts--online-book-v1--ftl-context.json.raw` | `b596b844f54c6aec951323df046c59ab03dad9e76308b160a864a7ef2c12948b` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/docs--contracts--online-book-v1--ftl-contract.md.raw` | `4df627e2b62d3cead508894a60736282dbad9f04779c56978a4b31be0e4d2521` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/docs--contracts--online-book-v1--history-context.json.raw` | `0bc3e178e5e0965d59f187ab122ca6bc5e1a49ac938557a1d8ed7c39bd1be11e` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/docs--contracts--online-book-v1--history-contract.md.raw` | `d8870a3fe87f0d23499c6a7fcef79ac9cd3566d6ad1e93098db3d51542a9f0b1` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/docs--contracts--online-book-v1--history_policy_independent.json.raw` | `7e88d48945deb14edae6274d8b726fb0ec15dff82720caab5c7ae8130e55c084` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/docs--contracts--online-book-v1--history_policy_loss_ge_variance.json.raw` | `7fa43dd4a990d45bf5dd9269cfba90ae16ebb7374fa3293adda7273ecd749e69` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/docs--contracts--online-book-v1--iid-context.json.raw` | `8edee8b9596b8aba601951d7e1d39672be0501ea7e7c8e57b07d60f8eea878c3` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/docs--contracts--online-book-v1--iid-contract.md.raw` | `03c05cd22f1962b420da6a2045a20b1164d1172aa5d6d2e326889d62100f41a5` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/docs--contracts--online-book-v1--iid_meanPredict_excess.json.raw` | `72e9b6a209a40762c1ac88be7d8c6e1b034abe3b8ba5b9f7b48ab60f73c4852f` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/docs--contracts--online-book-v1--iid_meanPredict_excess_nonneg.json.raw` | `bfd87dc31f1fd0ed1d912b34394e15b3c8075bcd6204b2a0997623d2d630a74a` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/docs--contracts--online-book-v1--independent_prediction_square.json.raw` | `e673875ac5de1d0d642cc57d327440b5dfb87d5f8307ff2b2d2166b38b43b41a` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/docs--contracts--online-book-v1--information-context.json.raw` | `2898fb057fda9c27127a9e5922517d175aab15ad87eeff5765d71f1aa46c3d65` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/docs--contracts--online-book-v1--information-contract.md.raw` | `e6e2df1792cdd3b1ca045566d973887c902fa6259cea4e7229154d70c96f0948` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/docs--contracts--online-book-v1--lemma-1-2-context.json.raw` | `91262535548af6ddfdb701db9138eb5c8994583ca945dee31cf0906c438716a7` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/docs--contracts--online-book-v1--lemma-1-2-contract.md.raw` | `0df23105858bac8b0cedea1d4f39db15fe59129fbe02c4eb7b5d7161694df8a6` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/docs--contracts--online-book-v1--lemma_1_2-v2.json.raw` | `062427c8eac86479236e58ee7da4e7a1c3d0f52dd9144b1ab633ee53afa68124` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/docs--contracts--online-book-v1--lemma_1_2.json.raw` | `30c70423015a3c4e69c296e7268dfcd47abde87c11ed980c9789564dc62011a4` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/docs--contracts--online-book-v1--mean-context.json.raw` | `494742dae1c9b3f6328c7c4a59950815720602d9b333ffa74d65b9cdcf779fb7` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/docs--contracts--online-book-v1--mean-contract.md.raw` | `904932aabaa78d30dbff9c5e1aa0986f7373a3f604f10bea02ad75f1abe02664` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/docs--contracts--online-book-v1--mean-uniqueness-contract.md.raw` | `27ba00975d6fd51ad8ff5bbcdde1ad40c3a4bf88bace157e4c0923c1beedc9ac` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/docs--contracts--online-book-v1--meanPredict_independent.json.raw` | `4fa0dedcb0189e381a85105cf1f53fdab876620ad553550b733489611dcf1cc6` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/docs--contracts--online-book-v1--meanPredict_measurable.json.raw` | `1d69eaeefdee20e0e4017c43e4acaaba8660277e8cb4ea878145dd1341b3677b` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/docs--contracts--online-book-v1--meanPredict_mem.json.raw` | `7e78522267d41d68467efaad27c29a3f997f3e767327ef55b87db9a6252c0396` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/docs--contracts--online-book-v1--meanPredict_memLp.json.raw` | `4a4f5b74269f4307f8e04677372bc551d2c972209cda4ef4869766c304dcdde6` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/docs--contracts--online-book-v1--meanPredict_noRegret.json.raw` | `55dc3379102c70ba20377541e512ad7063d0ffedb7ed39dd80744fe42c7da9b5` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/docs--contracts--online-book-v1--meanPredict_prefix.json.raw` | `4fe4ccf9b2b32d5fce4d9d35af207574eadf23617702a6629e3d90d06c6ecd01` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/docs--contracts--online-book-v1--meanPredict_stability.json.raw` | `203cb2143dcf23c540ef6b6f4cde4292b385fc17d6db2865ac2f1f15ab1d7375` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/docs--contracts--online-book-v1--noRegret_of_vanishing_bound.json.raw` | `d2e1c0bf0f3fa793780a0d9054173bdce201e8924add4e9f7cf0bb0bc71f5cb0` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/docs--contracts--online-book-v1--normalized_excess.json.raw` | `fd21f266932988ae7639771a551c3a6b7c77ae989d46c50340f03a2ae76cb88f` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/docs--contracts--online-book-v1--regret-context-v2.json.raw` | `cf8e35fdf1154c73daac93761d4bab6ee05972fafaa21b1760c59756fbc75ae8` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/docs--contracts--online-book-v1--regret-context.json.raw` | `206b6b1e27a1d66af69a66f600c89846a80c0e5bc25fd9a12a42d50b07c2dd17` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/docs--contracts--online-book-v1--regret-contract.md.raw` | `626a6d93313cfedc2d96e09c4cb9b3fa2ead94d0fd1d55466e0b26296367565c` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/docs--contracts--online-book-v1--source-inventory.json.raw` | `a2a504cf40d73f9c5e36f00fc1ef3b949ccaf5a558ab603c1c2a86007f30efa7` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/docs--contracts--online-book-v1--source_mean_optimal.json.raw` | `3c15549318546c50f0cd8297db1f052cd7bdfcfadffed47f0db68acc9dec1ff4` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/docs--contracts--online-book-v1--stochastic-context.json.raw` | `48312c553cc50edf59c6e5767d403d87988d80cc08640c921bfd6fa48c5fc972` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/docs--contracts--online-book-v1--stochastic-contract.md.raw` | `62a3c455c686786dbc12e6bb84558526b8a767e4c50fa09834f8d449dd33d290` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/docs--contracts--online-book-v1--theorem_1_3.json.raw` | `7b8b0643b6bf75300ba5a55cf8a7d9b833f380155fa9c9f8e39306649c815058` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/lake-manifest.json.raw` | `87c3e616f86244550ef39e7415186b11c1d4cf4bef20173196a619d9d4d48f48` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/lakefile.lean.raw` | `0164f3b5b5bdcbb237ab15ae8b44da83e183f4b97d5f3832aa4a57f27dc69d45` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/lean-toolchain.raw` | `b15a57f8ea4c890197465ce1156667ae13d9ed4ab8a9f263a920bf010d967d82` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/MANIFEST.md.raw` | `fcf078e2da910f173435d3b908007bb28e4c30fe27cdd51289b00ff57eb56c16` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/native-scaffold-conversion-windows--ONLINE-FTL-SHARP-20261007.md` | `4fa58f8ef5d2da50f4cf0df20fed192c7b4f6d476257fdc6fb1caf0c3df73e7f` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/native-scaffold-proof-obligations--ONLINE-FTL-SHARP-20261007.md` | `7330ffc18b4f24e4b486a670b11bc1d393a2e0f86c28595b2c9e47432c2177c1` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/native-scaffold-tasks--ONLINE-FTL-SHARP-20261007.md` | `689fbf827999e99009aac96f1982a35d0c7747cdac7194c4d25587b42f656e64` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/owned-paths-before-blueprint-correction-v1.raw` | `ff3808a881ba41fec1cf2916dced5f64f2d15b4161f1872274b96ce58a6c2f62` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/runs--active_frontier.json.raw` | `567e5873aa2549a83f2820d758069213808da822a93087129877385a1addf7c3` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/runs--lifecycle_memory.jsonl.raw` | `94be3ceb994768191ceb6a7545935c8d16c044511dfe8c4482e2fde493eaa5f8` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/runs--lifecycle_sessions.jsonl.raw` | `68f51418514e2bae75550fd6a6fa1cac6217f08855069ffdcdc095ce87be1d53` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/runs--online-foundations-public-20261007--accepted-decision-v1.json.raw` | `aaf64738c8814546ab131e7c0a83ce3c8b4832572b16841f6440ad0a74a1809e` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/runs--online-foundations-public-20261007--delivery-obligations-overlay-v1.json.raw` | `fa97452a89b23ef6de9b53e73b8ded091892650f21b706ec2074326faa3b6eaa` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/runs--trials.jsonl.raw` | `30b5c5be7b6048d039708afa37e53f2f8e198a50960a04d3899f975051d39171` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/Tests--OnlineLearningChapterOneCanary.lean.raw` | `9700f465791ab34e765c6aaf5c8891bcd33a9c5c141d61aa3d0b6a648648368b` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/Tests--OnlineLearningFoundationsCanary.lean.raw` | `a8f625750c9b0f395b8c49cc2a03eb681ba5d7ada7f5373c6052334c09397ecc` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/Tests.lean.raw` | `948edfada8088af64f779a1a53616f4eab2bc797c8843838d044dd4346bf9d51` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/website--content--chapters.json.raw` | `745357bd74bf5d5f0b2937e40cf0daef21c0d04bcc439e8cc559cc08670f7974` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/website--content--highlights.json.raw` | `d4996d6a0df721faffdbf88884e00f6ad76d95980e7893beeb790b939f681c6e` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/snapshots/website--content--readings.json.raw` | `c7a7bebeb988a2dd54221b982eb33bb346e207fd7b1ff9f9bb0cf1e3c5321dc2` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/source-contract-packet-v1.md` | `d2bd0dc2fdd0fd42e37907530dee9d25789e14d5f832a6a49d5bd64e2a531988` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/source-contract-preparation-failure-v1.json` | `d00063b5f355b4436858aa4c66f49d7b9ed14be3999ed6d5d86b0e2571e9c1eb` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/source-contract-preparation-v2.log` | `f86e01f2522669d0113a1abc4317bbfd4059acdc33fa477fcadf51279361ae50` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/source-contract-receipt-path-repair-v2.json` | `daa2ed81b4dc16422cfaa7e7fbc802cb81122b516bb694b91971f80d863215ad` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/source-pdf13-v1.txt` | `b16d82b563558afaaa14776c6015a78be9e0daa3d888a9a0593c057a54d2288b` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/source-pdf14-v1.txt` | `3f9d01aee6e81504b7ca2ef0d9657bc1ee30f36eb54a957b8018c4d0c3e2ac66` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/source-pdf15-v1.txt` | `037b6d907a868c339b881162333f6e56352cbebf285902eb6ed628ff4f8bd947` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/source-pdf16-v1.png` | `1cdaa7b80dc113b8083930eb1dcf245688aa921bfe112021d070610f8cab3eb8` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/source-pdf16-v1.txt` | `b8fe01f6c31bf15cfb67ea948a832f97e2c77f9e1f569a36fd9fa72e831796ee` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/source-pdf17-v1.png` | `8515e968b52d0d84928817aa489e890b5fa9a02207aa95dd3da28c9252eacff2` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/source-pdf17-v1.txt` | `164b4ca2261475aeadaf633ce67afbf8a221f612b8f4db801c36ea75081263e8` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/source-pdf18-v1.png` | `45588776738cd2b9f18f3dd6cbbb05535cd203a9c36351edcd2a310262874664` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/source-pdf18-v1.txt` | `bec2bd23e52551c2f353a7dec52c99582185e812f99a24f55983f209007eb484` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/source-pdf19-v1.txt` | `929515f2d15529e05cc52b7050cf4343872d9b31b1761a5c33a0f59bfc2e0cb1` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/source-pixel-review-v1.json` | `9fb949101ec2f55415b4cc9606bd4c92d8b288b857f2ee90715a01a28331544f` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/source-render-v1-exit.json` | `ebade438226607c7bbb5a68d4082e0790c6a6ee5faae29451826b5964a0aa613` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/source-render-v1.log` | `74db2d21bd3bb8520976e4eb8f7aed203f4cbcb02ff9cefa01b3b6095273a0d2` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/whole-program-obligations-draft-v2.json` | `84ca590d2e0af672aa17f3ea9ea92e34947c344e03d5a49d44062145f1996c7b` |

| `docs/contracts/online-ftl-sharp-v1/chapter-one-source-ledger-draft-v2.json` | `5b1620629a65d59e36ad0ea7409abcf707d3d73cf3dc329cf81da24ae1a429c9` |

| `docs/contracts/online-ftl-sharp-v1/contract-manifest-v1.json` | `2441c7589c9e69329ef227a0e6014da1e98a4ac0a76b9c884462bb42e8f49d9f` |

| `docs/contracts/online-ftl-sharp-v1/contract-v1.md` | `da132b158c0442647644ffec13426cb649379fd1e60909ef765c738d0424bbef` |

| `docs/contracts/online-ftl-sharp-v1/conversion-window-v1.md` | `b3a519a378dc04459bfba0d5f141069970afb7b4919be5dac2d3e3c59d0f8d93` |

| `docs/contracts/online-ftl-sharp-v1/dependency-DAG-v1.json` | `5fc36305a7df165287b82c92ac962040acd7b187d8d9454be16d46722c99f4da` |

| `docs/contracts/online-ftl-sharp-v1/existing-context-and-proof-v1.txt` | `a726a69fba60cf6e6ce35fbbc638ce69a6f6e435661bb8d2afebafac4b758c5d` |

| `docs/contracts/online-ftl-sharp-v1/existing-native-headers-v1.json` | `70d12b7b66600224819d056290905569f31a523cd5db545d536b291a3083559c` |

| `docs/contracts/online-ftl-sharp-v1/existing-proof-headers-v1.json` | `e489532bfbb988bcba4ba20cfd2dfc43bdd6c6a789af301a486c5be9f9a8bbc9` |

| `docs/contracts/online-ftl-sharp-v1/new-public-fingerprints-v1.json` | `cadf956450fb3c37ac47798ca40b3738b47bbe50d6953ddc6a55ddb2ae351c1a` |

| `docs/contracts/online-ftl-sharp-v1/new-public-headers-v1.json` | `cf1de4b82c5c93812697c7facb7906bd84faf2a70cfa8dc7137c215375252063` |

| `docs/contracts/online-ftl-sharp-v1/planned-canary-fingerprints-v1.json` | `957b07d323bdea288a036a3caecb59037ae54d46adbcecd3a70883e8874dbe44` |

| `docs/contracts/online-ftl-sharp-v1/planned-canary-headers-v1.json` | `12bac85ab73ff28d18cf19c123d3f73eac1afbd7e80c75b3f878764f81c2ace4` |

| `docs/contracts/online-ftl-sharp-v1/proof-value-obligations-v1.json` | `466d89faf389e1ee77cc932f5862f44d8d956f832787a719698b5a2cb0872377` |

| `docs/contracts/online-ftl-sharp-v1/semantic-signature-v1.json` | `bb8315bede2f10987c15792ac0b41806166d7622bc8c9861d3965f84ad541ed1` |

| `docs/contracts/online-ftl-sharp-v1/source-card-v1.json` | `13aa98fc662300477aec9ae315e2fa28b4b8d6ef0080bd3130e49338f24e1598` |

| `BanditRLProof/OnlineLearningFTL.lean` | `8aee4c971fffbc79f2426fb308f50ec02b664b42a90fe1f85620a313df4c7a06` |

| `BanditRLProof/OnlineLearningMean.lean` | `d65b3e5d5d2e33a0fd94722f1d7d9a09819c963c693e28bf854fae00f5280aa1` |

| `BanditRLProof/OnlineLearningFoundations.lean` | `e23ebdca2f7ce21a16173c93390fd24d16ba36e403c9d084233f7480e75408b8` |

| `Tests/OnlineLearningChapterOneCanary.lean` | `9700f465791ab34e765c6aaf5c8891bcd33a9c5c141d61aa3d0b6a648648368b` |

| `Tests/OnlineLearningFoundationsCanary.lean` | `a8f625750c9b0f395b8c49cc2a03eb681ba5d7ada7f5373c6052334c09397ecc` |

| `BanditRLProof.lean` | `7cdb1969bad2f7b42cfd7a25f6d15747d0d49178dadc244b70ab1f9b8c92c5ad` |

| `Tests.lean` | `948edfada8088af64f779a1a53616f4eab2bc797c8843838d044dd4346bf9d51` |

| `lean-toolchain` | `b15a57f8ea4c890197465ce1156667ae13d9ed4ab8a9f263a920bf010d967d82` |

| `lakefile.lean` | `0164f3b5b5bdcbb237ab15ae8b44da83e183f4b97d5f3832aa4a57f27dc69d45` |

| `lake-manifest.json` | `87c3e616f86244550ef39e7415186b11c1d4cf4bef20173196a619d9d4d48f48` |

| `runs/active_frontier.json` | `567e5873aa2549a83f2820d758069213808da822a93087129877385a1addf7c3` |

| `../research-online-ogd/tmp/pdfs/orabona-v10.pdf` | `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17` |

| `tasks/ONLINE-FTL-SHARP-20261007.md` | `13ff6d1feeff30c8399dd15721feb220116e5204c9611612bac2aa3d91d1f42e` |

| `conversion-windows/ONLINE-FTL-SHARP-20261007.md` | `13ff6d1feeff30c8399dd15721feb220116e5204c9611612bac2aa3d91d1f42e` |

| `proof-obligations/ONLINE-FTL-SHARP-20261007.md` | `13ff6d1feeff30c8399dd15721feb220116e5204c9611612bac2aa3d91d1f42e` |

| `research-wiki/retrieval-index/ONLINE-FTL-SHARP-20261007.md` | `da132b158c0442647644ffec13426cb649379fd1e60909ef765c738d0424bbef` |

| `proof-blueprints/ONLINE-FTL-SHARP-20261007.md` | `73421a5cdea59ff8ba5642d039c930e6197f879d27e8718f8df1f8501c49d5d5` |

| `research-wiki/mathlib/theorem-cards.md` | `4656c1a8ccd4b2d8523cf5cf48bd1f966e7ba2c2237e2e578d6b8c2ecc6fbd97` |

| `research-wiki/mathlib-candidates/README.md` | `ea4ed80d4eed053d0eea0d315df86075a9445e6280e2a827e3841e5c05d7df37` |

| `.agents/skills/bandit-semantic-roundtrip/SKILL.md` | `7ee7b72b8a84ab954966dc13900952c3439bd8d4e97877b622c1ca0a7aa85477` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/repair-review-index-v2.py` | `32a5d82c89fa074f12f8b270ddde95c3714b0f081e7aa9b57d78b7af6d1167cc` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/review-index-self-log-repair-v2.json` | `cbda4649c2888455b7512159152d22f6b676b0dcf33adcf8aed7a46a6dafd024` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/source-contract-inputs-v1.json` | `a6d7651aa10b5316c5ada5ba0102ccf7524876a14e55042e9ef4a78965ad6724` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/source-contract-packet-v2.md` | `14eeb54d67113582bde4426024b74c9a0bfd664c4a057c6e3a3c736a9fe4b358` |

| `E:/ABRL/worktrees/research-online-book/runs/online-ftl-sharp-20261007/source-contract-preparation-v2-exit.json` | `19ef45f45254d07d1d6ad1e240f78f21f705c4efab8402a86b4bd0bcbdee7c20` |

| `runs/online-ftl-sharp-20261007/source-contract-inputs-v2.json` | `d0c3d0a9a99a049ee8a66ffcca0a994d83d79656cc8dca34005e3b0c92febdc5` |

| `runs/online-ftl-sharp-20261007/source-contract-packet-v2.md` | `14eeb54d67113582bde4426024b74c9a0bfd664c4a057c6e3a3c736a9fe4b358` |
