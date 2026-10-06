# Example2.25 BODYv2 — evidence resolution repair

**Verdict: accepted-with-explicit-delta, BODY only.** The specific BODYv1 evidence-index rejection is resolved. Original rejected report/receipt remain unchanged; this is a new versioned decision, not a rewrite. No mathematical repair.

Actor `/root/source_reviewer`, requested GPT-6 Astra / medium; prior CONTRACT/BODYv1 history is disclosed. No human/external review or runtime model attestation.

## Exact repair and provenance checks

All239current fixed raw inputs independently match. All149prior-contract-binding-v2 rows point to bytes matching their original hashes. Compared v1/v2 row-by-row: original paths and hashes are identical; ONLY two resolved paths change, lifecycle_sessions.jsonl and trials.jsonl now point to the already preserved immutable reviewed-prefix snapshots. The old v1 literal current paths had become stale after appends and are not retroactively called valid.

All217files bound in rejected BODYv1 were independently resolved and verified, using the separately frozen BODY-prefix snapshots for the two globals. Both current global files start with their exact reviewed BODY-prefix bytes. CONTRACT snapshots and BODY snapshots bind different actual stages; neither is substituted silently. Original report raw SHA remains `6bcd593e337a2bd59e2eb0fd289fe26c653809ef2686c8e0fb897c0367e394d0`.

Read the versioned correction helper and actual log/exit: it changes resolution metadata only, verifies all149digests, retains old v1 and original receipt/report/snapshots, and exits0. No native trial is appended by this reviewer, no proof is rerun or falsely claimed newly repaired. Original retained module, complete owned definition, borrowed S/indicator, whole canaries, source/types and frozen headers remain the same reviewed mathematical inputs.

## Three actual proof targets, seven slots

### `BanditRL.OnlineConvex.indicator_subdifferential_eq_normalCone`

Verdict: accepted-with-explicit-delta. Frozen header `501fd379f37c30fe1cd871cfb1cd7f51abfd15ff97bfd2ab7543c267c304497f`.

- **objects_spaces**: Finite-dimensional real inner-product E, with NormedAddCommGroup; explicit FD binder, no supplied CompleteSpace or positive dimension.
- **quantifiers**: Every nonempty convex V, every ambient query x and candidate g; support tests ALL ambient y, cone tests all y in V.
- **assumptions**: V.Nonempty and Convex real V; no query-feasibility, closedness or boundedness premise.
- **conclusion**: S(extendedIndicator V,x)=N(V,x), full equality both directions.
- **constants**: Indicator exactly zero in V/top outside; nonpositive inner(g,y-x).
- **information_probability**: Static set equality; no algorithm/probability/regret/feedback/measurable or executable selection claim.
- **boundaries**: Outside queries give both sets empty. Empty V excluded: generic S of alltop equals all vectors whereas feasible N is empty. Thin nonempty convex sets allowed.

Actual producer: Uses nonempty V to produce SourceProper of the actual zero/top indicator. Actual given support plus subgradient_point_finite and effectiveDomain_indicator derives x in V. Tests every feasible y to obtain real inner<=0. Reverse direction splits arbitrary ambient y into feasible zero-value case and outside top case. Feasibility is derived, not assumed; empty V is not generalized.

### `BanditRL.OnlineConvex.normalCone_interior_eq_zero`

Verdict: accepted-with-explicit-delta. Frozen header `abd3018b9b0d037bdeb12261fee72dbb16d8ef863783ad440fffe1b5dc4a302f`.

- **objects_spaces**: Finite-dimensional real inner-product E, with NormedAddCommGroup; explicit FD binder, no supplied CompleteSpace or positive dimension.
- **quantifiers**: Every nonempty convex V and x in its AMBIENT interior, every g.
- **assumptions**: V.Nonempty, Convex real V, x in interior V; no relative-interior substitution.
- **conclusion**: N(V,x)={0}, including actual membership of zero.
- **constants**: Exact zero vector; inequality nonpositive.
- **information_probability**: Static set equality; no algorithm/probability/regret/feedback/measurable or executable selection claim.
- **boundaries**: Empty ambient interior provides no eligible x; does not force zero normals on thin sets. Zero dimension permitted, no hidden full-dimensional global premise.

Actual producer: For nonzero g, normg>0 and an actual ambient ball radius r>0 produce a=r/(2normg)>0. The proof establishes norm(a smul g)=r/2 and x+a smul g in V, so actual normality gives a*normg^2<=0 against strict positivity. Reverse zero satisfies feasibility from interior_subset and every displacement. No relative interior or vanishing oracle.

### `BanditRL.OnlineConvex.normalCone_unitBall_boundary`

Verdict: accepted-with-explicit-delta. Frozen header `96eae7375828573042996c513a495645d77c3afcd6ca57b31b6d9123f0e9c6fd`.

- **objects_spaces**: Finite-dimensional real inner-product E, with NormedAddCommGroup; explicit FD binder, no supplied CompleteSpace or positive dimension.
- **quantifiers**: Every x with norm1; every candidate g; exists real alpha for that g; all y in closed unit ball tested.
- **assumptions**: Only norm x=1 beyond class binders; no supplied radiality or chosen multiplier.
- **conclusion**: N({y | norm y<=1},x)={g | exists alpha>=0, g=alpha smul x}, both directions.
- **constants**: Closed ball radius1, boundary exact norm1, entire alpha>=0 including0.
- **information_probability**: Static set equality; no algorithm/probability/regret/feedback/measurable or executable selection claim.
- **boundaries**: Zero normal included; no claim at interior/outside query from this boundary theorem. In zero dimension norm1 impossible, not excluded by an added d>0 assumption.

Actual producer: Zero g uses alpha0. Nonzero g is normalized into the closed unit ball; actual normality plus Cauchy and normx1 force inner(g,x)=normg. Expansion proves norm(g-normg smul x)^2=0, hence actual radiality with alpha=normg>=0. Conversely arbitrary alpha>=0 times x satisfies every feasible-y inequality by Cauchy. Both directions/full ray, no radiality premise.

## Complete owned definition, seven slots

- **objects_spaces**: Normed additive group E with real inner product; NO finite-dimensional binder.
- **quantifiers**: Every set V, query x, candidate g; every feasible test y.
- **assumptions**: None on V or x in the definition signature; membership explicitly includes x in V.
- **conclusion**: N(V,x)={g | x in V AND forall y in V, inner(g,y-x)<=0}.
- **constants**: Exact0 and displacement y-x, nonpositive inequality.
- **information_probability**: Set definition, no computation/selection theorem.
- **boundaries**: Outside V and empty V give empty N. If x in V then0 belongs. Arbitrary nonconvex V may be input to definition, distinct from theorem premises.

Owned N is exactly `{g | x in V AND forall y in V, inner real g (y-x)<=0}`; no FD/nonempty/convex binder in the definition. Generic S is wider than source proper-function scope, but nonempty V makes the actual zero/top indicator proper. Empty V remains excluded from the first source equality. Three theorems retain explicit FD and firsttwo retain nonempty/convex hypotheses; source Euclidean representation is coordinate-free, no independently certified isometry/functor. Ambient interior is not replaced by relative interior; norm1 boundary has the entire nonnegative ray including0. No supplied radiality, vanishing or feasibility oracle is introduced.

## Actual canaries and gates remain applicable

The unchanged interval canary accepts -1/rejects+1 and excludes outside2 via actual equality. Singleton proves all real normals and7, not its empty-interior proposition. Intervalhalf invokes actual interior membership and zero-normal theorem. Two TEST basis definitions are genuine real2D PiLp vectors; the boundary canary accepts2e0/0 and rejects e1/inward-e0 by coordinates. Four canary proofs plus two definitions are not six proofs.

Existing actual body re-elaboration10.656s/whole-canary focused3289, ten named standard-three kernel checks (7proofs plus ownedN and2TESTdefs), and four native guards remain applicable unchanged. Actual10selected nodes/1581direct references/15required value pairs were independently rechecked, preserving original4nodes818references exactly. No full registry export, clean rebuild of every cached job, or fresh gate beyond supplied logs is claimed.

## Reader obligations and remaining scope

All nine reader obligations remain separate and pending before integration/FINAL:

1. Explicitly distinguish ONE Example2.25, THREE mandatory equalities and ONE complete retained owned definition; zero new proof/definition/TEST/canonical nodes.

2. Correct SourceNormalCone highlight: definition has intrinsic real inner-product context but NO FD/nonempty/convexity premise; its full body includes x in V. Do not copy theorem-premise or both-directions-proof wording onto the definition.

3. Publish generic S versus printed proper-function scope: nonempty V makes the zero/top indicator proper; empty V gives all-vector generic S but empty feasible N, so nonempty cannot be silently dropped. Keep all-query outside emptiness.

4. Explain coordinate-free finite-dimensional real inner-product presentation includes Euclidean source instances without claiming a separately certified coordinate isometry/functor; actual three theorem FD binders retained, no CompleteSpace/positive-dimension premise.

5. Keep AMBIENT interior and all candidate normals; do not substitute relative interior. No global closed/bounded/full-dimensional assumption on arbitrary V. Zero-dimensional boundary theorem is vacuous because norm1 is impossible.

6. Keep full closed-unit-ball ray equality with every real alpha>=0 including0 and both directions/all feasible y; normalization and Cauchy produce radiality, not an assumed direction or one-vector witness.

7. Scope canary claims accurately: four old proofs plus TWO noncomputable real2D basis definitions. Singleton theorem gives univ and7, does NOT itself prove empty interior. Actual2D outward/zero acceptance and transverse/inward rejection remain.

8. Use fresh stage-qualified evidence and actual4node818reference readiness/eightvalue pairs; not full/canarygraph or current package acceptance. Preserve three curated routes/three notation entries/four canonical nodes; teaching links are not exhaustive proof graph.

9. Preserve next T2.26 and all remaining Chapter1/2/appendix work as mandatory, Chapter2 null/incomplete and Goal active; body/kernel/combined/site/FINAL/immutable/PR remain separate.

Required mathematical repairs: none. Required metadata repairs: none remaining within this v2 resolution review. No combined/root/Tests/fullharness/site/FINAL/immutable/PR or source-package acceptance. Adjacent T2.26 and remaining Chapter1/2/appendix obligations stay required; Chapter2 null/incomplete and GoalACTIVE. No main/live/merge/deploy/retirement or whole-book completion.

## Raw reviewed inventory

Raw byte bindings include current fixed inputs and exact recovered prior-stage paths. Historical/administrative reads certify provenance rather than unrelated mathematics.

| Path | SHA256 |
|---|---|
| `../research-online-ogd/tmp/pdfs/orabona-v10.pdf` | `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17` |
| `.agents/skills/bandit-semantic-roundtrip/SKILL.md` | `7ee7b72b8a84ab954966dc13900952c3439bd8d4e97877b622c1ca0a7aa85477` |
| `BanditRLProof.lean` | `351d5238e97cf54ae4c5f65a7e82cabc40ac7eb6f18c9e64e89e27a6610cb9c6` |
| `BanditRLProof/OnlineClosedProper.lean` | `c66f00c33b45fb8a0e11583eeadf506e176c16166ce2af02f41f0674507cebe7` |
| `BanditRLProof/OnlineConvexExtended.lean` | `bd30bb95a46ccdc3f6d25f808c175af5fee71d075c2b46ffcf6508f15f1ed66a` |
| `BanditRLProof/OnlineNormalCone.lean` | `95fa41f9bf3f04354b0175c1f755786e86c103040f54aed9eab5fbf8a206539d` |
| `BanditRLProof/OnlineSubgradientAbsolute.lean` | `bf3e8d97f67b78e7ad230b8efd321948f4d7ba1a0e9cde31e8d85c1e9019442b` |
| `BanditRLProof/OnlineSubgradientBasic.lean` | `af3d3f56e4a64cd8adbe47368caf5382e63b428f01da29a121c28c8014f352a5` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/.gitattributes` | `705fd4d6451a31d36b3df7de96f83f30ac976c9b4a6d1e51671d8e2f33e2d0da` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/00_context.md` | `e7a4913ff53b95873bbfd04d2d74611129a4248fdb712ac43399021cb83f8ad3` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/10_upper_director-v1.md` | `28426536c95e1631790715531546621895d49cf7c5810d90786fdcbace117063` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/20_architect-v1.md` | `5bb8457120116f7af36b868a2112c054c8363b00854d0dad229da4c741fa8611` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/30_lower_worker-v1.md` | `160b1bf3b2094d5aaa83ba2c383672cc9e9af61aa805d01fe98e9d64c2753173` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/API-route-before-proof-v1.json` | `f7fff76c0928ef492b1b80ae9f8cf378fa81f9376e44f95774a45358e8f0c876` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/actual-types-v1-01-exit.json` | `2c05196642ac4906dd27733a2eefae221830958f64e2964864d2699e1e683325` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/actual-types-v1-01.log` | `fc54f69b79fc723478a7d25b912117336cbcbb07f1906debc19547498a59af2a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/authoritative-private-workflow-binding-v1.json` | `2b9c630b81b9b524476e56fa8727edbdfa31404c8e396c6a8788a515f69fbe7e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/bind-review-packet-helper-v1.py` | `cb7f4d4fddec85e7a5faed56c847f8aaa129f967626133284cabd2ba9fb0aeab` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/blind-generated-before-use-v1.json` | `cf404fb787b5ad76fe031d73c9509fb0fa35577eaf92bffedfdf4eba42e7f84f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/blind-packet-v1.md` | `ca3f458d81affc5a54a9b8eb53fdf8d31fd32ec6b3a644411ecb3ca9b54abc29` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/blind-receipt-v1.json` | `69fc70c2956da88bb824d66872abc7a101ca6b57f93832875e1de55bab9b9380` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/blind-reconstruction-v1.md` | `6f5b6be50a39170f8f326b718cc8410b361d083c33ab6ac7c07416a8df524820` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/body-repair-packet-helper-before-use-v2.json` | `32a9cf49d516f4a2ef0d7946dc2e9c4ca850a7c5050991f36b6c3b57d6f623eb` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/body-resolution-repair-decision-v1.json` | `3f45b289a6f50e2404fc1bd6ca1661763c9b1eec1ca0636e2ac44780b7e94694` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/body-worker-before-use-v1.json` | `a6cc2b48dfb03fe442df79b513cd3ee5a5e450a4725dcb8f3b0b868c5774d90b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/common.py` | `6858e98d74766e95e03b2801b98b00776d98450914dd1990247c6ebeeb3cd3b0` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/compiled-dependencies-v1.json` | `167a9093f9f844d338adb7088e66e176b6917f6dd638619dada57c79f6b755aa` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/compiled-public-graph-v1-01-exit.json` | `421e7f02028922afdc63974851620d95250665cee7cf01c271364757ccaef25c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/compiled-public-graph-v1-01.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/compiled-public-graph-v1.json` | `4995ad1479b96b42152b0e450db6efb3607c1ba1a5cc914965081b2636b0dbfe` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/compiled-ready-graph-v1-01-exit.json` | `b912cfecfe048446e571e0a2520c110fc9aaf7a8914e87561d34b1c0deae98fc` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/compiled-ready-graph-v1-01.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/compiled-ready-graph-v1.json` | `4a9038415113e0df99f32e2ec4f9fca8a13b33d06151e990f7971e6f4541c4ae` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/contract-binding-audit-v1.json` | `fc1464cd2dbf88d70e9305656d9cd4e27490602cb4764c9740d787733abf74fc` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/contract-preparer-before-use-v1.json` | `ccf24c194a97e856837d2440681913fd0f833f8235d39a4feff5c5b3c01787ca` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/correct-contract-resolution-v2-01-exit.json` | `acc08a28411ab61dd8a6a879ec9c60a7ad433b230a6110a813ed3a805229a7cc` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/correct-contract-resolution-v2-01.log` | `b6c3cf986b01a4e0c15fcd830e736ab0a551b889d4fb4c8f5b3e256f09a0c948` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/correct-contract-resolution-v2.py` | `40952ddbe42df617a41723dd39df01dd08308f2bfcaa828b51f94897c279a319` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/draft-fence-SourceNormalCone-v1-exit.json` | `a90fb5985b8d5f6dd79d32beb2d9bc49983d65984666ee4773a99450d20f30a1` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/draft-fence-SourceNormalCone-v1.log` | `0915c4bdf7ad6d80be56dc376b0900558e6fc75dcb330057782d807f862375ca` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/draft-fence-indicator_subdifferential_eq_normalCone-v1-exit.json` | `d243056aeee47d69999b75c06b4af704cf3c06795a059e2c7be990d2236e4c8f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/draft-fence-indicator_subdifferential_eq_normalCone-v1.log` | `99356013add5a9ddd07c49aa6fc9ec1add7fc2b37c82823d85d8e9a374919e14` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/draft-fence-normalCone_interior_eq_zero-v1-exit.json` | `935e30ea38823357f11920ee8fb09d299ed761d9cebf6131459d86ac9b993c31` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/draft-fence-normalCone_interior_eq_zero-v1.log` | `3e3e09508b421935562005370981370d65faed6b5abdf2405b7a7f4bcceb7c8a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/draft-fence-normalCone_unitBall_boundary-v1-exit.json` | `ec467e09fb3707eb303d115549457f84c27755da27f4318104ab10f62aeec509` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/draft-fence-normalCone_unitBall_boundary-v1.log` | `5f5d2727e0fe6d21768cfd2eedc2e66ffd89cd81730300be99de665abd7c209d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/draft-freeze-v1.json` | `8fa1c79d186f34d01559710ec25a72f8eb1eb2ed76ff06544fdb5fe2afadba6d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/draft-lifecycle-v1-exit.json` | `7c6500eb5cebf227fd555ed1b78f65ab56daa9ef26f26d4d87778a9cde6b6e31` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/draft-lifecycle-v1.log` | `4e8edce2c6b79b69faec68c84a7b0222a80c839cfd4cc599fd3e1adf7bd1cb36` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/draft-preparer-before-use-v1.json` | `73d07d70af01412c054a8f97d3283825855dc306ee6e174782194683a683402e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/draft-preparer-before-use-v2.json` | `8be7e0156f80933c7fd4766ec7bb248e1df2df32f1df804ff761f3d933657d59` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/draft-preparer-before-use-v3.json` | `d5c9107c2bd1efa895dfb58ad7c98f95f79a9c0f54cfbdb7c7081d5e0bac578b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/freeze-draft-v1.py` | `7712f080d5dd561deb88da73c1c2e4c18f57e7f12e88c2c6a6620ea75f23332b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/freeze-draft-v2-01-exit.json` | `57733729ceb12cb4b90756addcc5da9da3bbadd655590514f8c72afdf000139b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/freeze-draft-v2-01.log` | `563e36c71a82e5c39a5ba8d91825b873308c3cc8c0d3e86a8f0fc1f1d8938132` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/freeze-draft-v2.py` | `fded243eb8d8c562accc7390545dbb6b3317053bedcb8514340c61ff32fdd9b3` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/freeze-draft-v3-01-exit.json` | `2410c2cc29b34cee4c7dec56da92273137ca9ed7e2e908312c5db0eec7a5cc42` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/freeze-draft-v3-01.log` | `0e25a95e5d4a1a8d277843f58e683fffed62a8b92041e8e4b8c29fe9981175f4` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/freeze-draft-v3.py` | `211d552e669a7b0381c0516cdd5547fc2ecd62120a859790da6c76cc93967592` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/frontier-refresh-help-v1-01-exit.json` | `d3d2dd5fdc64cfb82ce724b9ffecc685c01fd16ac7f4f65570beca6a8d81114f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/frontier-refresh-help-v1-01.log` | `bff73ff554907d7c5dd50b99f2491f5675e93afb29829e402ec383fb52fe3cdc` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/frontier-shadow-help-v1-01-exit.json` | `8ebc1ed6dabe09137f64db414baa2bb481aee1b6c83e2e45faec83e51f094dc7` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/frontier-shadow-help-v1-01.log` | `ad548f6e24b3214fbf5796c632caa24debbaa21c6622f7dab8abe268f521de7d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/historical-raw-supersession-body-v1.json` | `bb634521ffcf245892eca9fe4333a8f3115d3fd8ef5d2cddb407ae7d524d7b0a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/historical-raw-supersession-contract-v1.json` | `255ca21109914591ffbe08e030f7c11dfc7eca3741093bd39ca16d12e621d405` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/historical-raw-supersession-v1.json` | `db1dc5bf7f19754bdaff1aaaf07a816fd4fb5655691066b25dbf9491e01faefe` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/historical-raw-supersession-v2.json` | `656041357ce55fc3558fbd581765f702eecaa923913a65a36e3d9851ff81a2a2` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/leaves/actual-types-v1.lean` | `beb4839d1b8e1638b24f5a6b1919dbdaec57c48325320d502b8c4d2d4682e61d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/leaves/export-public-dependencies-v1.lean` | `3e80ae6ff0faa33eaa6c82eb8d15b0a642367b8284789f9dc2bcf5128cd786bf` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/leaves/export-ready-dependencies-v1.lean` | `7e811ade704cdb6561f86e80b098c05abb776deadef60ec3af2db894591dde3a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/leaves/pinned-APIs-v1.lean` | `79782d342de5ef947b6b857d985e33646cf53589ada53e799a330e2371938835` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/leaves/public-all-axioms-v1.lean` | `8307752d24343de7b0b7fd7bfb0d18713b711252c922452da95183bcc5ea567d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/lifecycle-help-v1-01-exit.json` | `3db099c6fb0bc58532f9c9c924377c851f8825ff24dc36e007daf64cfef03f52` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/lifecycle-help-v1-01.log` | `b1e8b438a9b725793b9888d206e98a971ace3df200ec90ed9cb63eab26b28507` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/list-lean-decls-help-v1-01-exit.json` | `518ab8435445850aae4f2c71ba193dcfc8758e8789a6f752ac66dcf49992ce68` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/list-lean-decls-help-v1-01.log` | `258218f16a12b1a530d85ae83e6c2449237af8a0a1153bb35de40245d665b131` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/local-declaration-search-v1-exit.json` | `def703e427032b8204b9108d069d226587b90c807e4fc5496d6057f194ba4716` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/local-declaration-search-v1.log` | `42e77d66f04a06bf3104eed95fd77d108dcec4128a89c1538907ae293be9f193` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/local-memory-search-v1-exit.json` | `3e6e056a4512669c897ee99a7a8f6282aae48d1e67aefa1c626b60ff2e1527fd` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/local-memory-search-v1.log` | `97caf5dc84aa2be610c26624414c8fdb9456a78496c70ee8ae8b7b2b5e98e708` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/memory-digest-draft-v1.md` | `b46afd9f4f2b2bcc3192fe0268c0844dad8750788e50ffcda9dbe91c62218633` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/native-draft-fences/SourceNormalCone.json` | `0915c4bdf7ad6d80be56dc376b0900558e6fc75dcb330057782d807f862375ca` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/native-draft-fences/indicator_subdifferential_eq_normalCone.json` | `99356013add5a9ddd07c49aa6fc9ec1add7fc2b37c82823d85d8e9a374919e14` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/native-draft-fences/normalCone_interior_eq_zero.json` | `3e3e09508b421935562005370981370d65faed6b5abdf2405b7a7f4bcceb7c8a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/native-draft-fences/normalCone_unitBall_boundary.json` | `5f5d2727e0fe6d21768cfd2eedc2e66ffd89cd81730300be99de665abd7c209d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/native-public-fences/SourceNormalCone.json` | `974b438881ecc9daa56e2874179bfbdbd06150cfd46d58da8a3a009358a65f8d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/native-public-fences/indicator_subdifferential_eq_normalCone.json` | `f95d822fbe91a131c545d18bcdae6b4078802ca2925f3cde448191c55145582b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/native-public-fences/normalCone_interior_eq_zero.json` | `a15b9185043cdf0aa95267b7a40d21027caa74b07a4bea6b6a21838f73f002d7` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/native-public-fences/normalCone_unitBall_boundary.json` | `26b07f6bfb0922e21d809f6b0c4e007af881d933d41bdac60e51329aadbbd354` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/pinned-APIs-v1-01-exit.json` | `10d13bc0bab4e9882261d22bce6694e3fe91d7ead2bbce7af19190d15352e9bd` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/pinned-APIs-v1-01.log` | `c750b8ef51ad31fbbe69ba66854b61bb52c9ae01b131fee4d50bd823fb636d19` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/prepare-CLI-evidence-v1-01-exit.json` | `f0bd378764315918b39a47d9d3ee6a450e613de617110d48a665d0514150b750` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/prepare-CLI-evidence-v1-01.log` | `271086955af5ddf71dc79ba527688c3f19052ef03e5892c64154f73d2c0732c4` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/prepare-CLI-evidence-v1.py` | `2b53f2800ee858b13cb33d9dd56de04c3bc733ed76f4afbad3116b4065f3505d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/prepare-body-resolution-review-v2-01-exit.json` | `993fb44ed2e84490f8ff10ab74e1020509e8398832db51c674b814c3641de2ea` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/prepare-body-resolution-review-v2-01.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/prepare-body-resolution-review-v2.py` | `a3fb3270c353fab60a0754ec3c91a92f4c66bc3c4344b1f49c720c9c89937440` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/prepare-body-review-v1-01-exit.json` | `0e55fd97eeb7f4998da986d7223df983f81bbedd5c0b993c178822007cb56e92` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/prepare-body-review-v1-01.log` | `28ddced1d820bd9e67bf40ddae76c6cc6bb0d47b24355e2e2679c7788e9f6be7` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/prepare-contract-review-v1-01-exit.json` | `0fb4ec09bab62a1a1c71e8ad78c72d2d8e17a8eb20db93111a820850bca30031` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/prepare-contract-review-v1-01.log` | `cb1b98bb612a5d9bc593b555902511919236e8199b0b0cad3cf9e0bf7ba4dfd4` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/prepare-contract-v1-01-exit.json` | `46f7bc4675ab85edfe29594b75e90f2d2a5263f295959a66ac7b77b6994e58c6` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/prepare-contract-v1-01.log` | `fe534597e1d2ad7212d937aa8555292cab430ebb4ed68830344c23c3c1f2c54a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/prepare-contract-v1.py` | `b2733808d1e39017006fee440e68027c916d1392cdfbcb24196ccd7ff313184f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/prepare-draft-index-v3.py` | `194dd2863e93f072f6428ab8b4a0ed268f00ecd70848e085fd3a76716f8641a5` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/prepare-draft-repair-v2.py` | `8ee11728bfec9255cbdcf6e5fcd978308b2a55fdb6045b3a6850558b5298a962` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/prepare-proving-helpers-v1-01-exit.json` | `30023fb2b0cfc40f799776e18f2170945270005fdf2dcde381c6234f10d24573` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/prepare-proving-helpers-v1-01.log` | `6dc3a6711f053c88a730a7dab11d0dabf922b816a07a72737be55d0202d76da3` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/prepare-proving-helpers-v1.py` | `7a761b87c3c9a15ac633557f4dd18a17598a64246ae24dc86241dd6062a389b3` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/prepare-readiness-v1-01-exit.json` | `5b445dcbca011cf136dce5d9529105327c81e71ee68440bd135b5c28763f0421` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/prepare-readiness-v1-01.log` | `4ad983d2b968f536d03077f7ca30d33fd75ce26490d78dd9c38899eb902aea84` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/prepare-readiness-v1.py` | `c99894e672b1c5361737e7ba8766140bf61a8187c4300a8f36dc2f611adc3823` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/preserve-contract-native-v1-01-exit.json` | `0cf2cf40c5eb8b82a584c36b3ba21392cf4d74ea9cfe5b99774b4e69ea0b5f92` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/preserve-contract-native-v1-01.log` | `2593ab45223abe18c8e98ebd794ca1be801a29e92159a78231439872a5100491` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/preserve-native-prefix-v1.py` | `2b15291ea2bad506c56cb5bdbe826ac7af8cfb542cf883eff9bad88293ea3e5a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/preserve-rejected-body-native-v1-01-exit.json` | `1dc37d933345e363509bc8f8e0223d5eb76ad28ce24f2cac7f1ac8115665fe6d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/preserve-rejected-body-native-v1-01.log` | `48cb53f4fe0939fbdbe6002e37646eed55d350c50e9feae282a265b1737e1382` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/prior-contract-binding-v1.json` | `ba7115af9afd940edab7f4f3e607ed77193fb41ec24e2905a9304b767bd638dc` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/prior-contract-binding-v2.json` | `7de3bd5b6374c273c81a550ebe9e893868007cf3614f003ffe0f545e38018191` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/prior-delivery-raw-binding-v1.json` | `cd8a72d717f21e5b8fedf82d437d77307f9d54691caf6ea3daeef204181ce5b8` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/proof-obligations-draft-v1.json` | `c7780de295b356107a5bc474262d665cf394889356d956c6ef45c8a558fa01aa` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/proof-obligations-proving-v1.json` | `3c33d848b9537528de84836a0039f2a75939842f517b6ad2f83281f8c38d7838` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/proving-generated-before-use-v1.json` | `4e8327d42f0f96f5c716406e19a1231969f345b3034d34bfadda968678c1840c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/proving-lifecycle-v1-exit.json` | `4681816bc52dd7ec8d9b353b32e60a9f8e320f130ea41481f7af90f7af6cb136` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/proving-lifecycle-v1.log` | `42b98fb5009241968426c9d4868106dff304ca1c2bad320cbdc81231e27f1632` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/public-actual-bindings-v1.json` | `6e87c6bd0e0dfd15980a75cc0d7c544f0ca0053fb18640307abe886b663f05ed` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/public-all-axioms-v1-01-exit.json` | `6417334cc7893a6953749d7ebc653431338f872dea6638ebbf1a6ddb38c0bff8` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/public-all-axioms-v1-01.log` | `9b1cf58014760dbef78d0240ce8258da9795c04e2c5ced801981156c1082e08a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/public-body-inputs-v1.json` | `d17f46d27496b6442268e1c1195087a52df42b67a72aa05a3e318ed391638c91` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/public-body-packet-v1.md` | `18bc3db71577f049f17ca88c0cabc021b91628d939e4e9a07b227d373c2b41f3` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/public-body-packet-v2.md` | `7a8f5932f142b1f8cea154c66550306f27f2bd5b9acf3886ce6809f63fd9a18c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/public-body-receipt-v1.json` | `47429a8524c42e6b5572cf32075b00e28ec2d3da270761f2619c9f767a29364c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/public-body-review-v1.md` | `6bcd593e337a2bd59e2eb0fd289fe26c653809ef2686c8e0fb897c0367e394d0` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/public-body-v1-01-exit.json` | `9bad5ac8c4651ff7b60f1c8ff992ee9fff504c85777b359134e02f242f0c4c44` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/public-body-v1-01.log` | `74abbb7d088b159e7f0880d17ee8684aff4164cae1a8cd78eec0f526d540d71a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/public-canary-focused-v1-01-exit.json` | `dd1ece6960c65d97159779370dfcd76e679971106ff68cf5ffd0a8e35b876e97` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/public-canary-focused-v1-01.log` | `2f626ad20ca8ba5a665fc0639b8773fd0bdd84ca75e703fd010f7ab1dc615443` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/public-fence-SourceNormalCone-v1-exit.json` | `d17974c4ea060a9566a62d032812c019b22cee8c352fd39063dc6c3fe10906fd` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/public-fence-SourceNormalCone-v1.log` | `974b438881ecc9daa56e2874179bfbdbd06150cfd46d58da8a3a009358a65f8d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/public-fence-indicator_subdifferential_eq_normalCone-v1-exit.json` | `1cad562f98c2f674fe4611646db3d44eb6ee78030c5f973b9fd141085eb209ba` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/public-fence-indicator_subdifferential_eq_normalCone-v1.log` | `f95d822fbe91a131c545d18bcdae6b4078802ca2925f3cde448191c55145582b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/public-fence-normalCone_interior_eq_zero-v1-exit.json` | `36c094ac6affe78d585b41ab0004926a17bb4082af7c36c4dcd7793019cf9e65` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/public-fence-normalCone_interior_eq_zero-v1.log` | `a15b9185043cdf0aa95267b7a40d21027caa74b07a4bea6b6a21838f73f002d7` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/public-fence-normalCone_unitBall_boundary-v1-exit.json` | `3128f518525dd2ce6224b129444e59d5ebbce5d1c9aa3dac7fb833efe75ffac0` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/public-fence-normalCone_unitBall_boundary-v1.log` | `26b07f6bfb0922e21d809f6b0c4e007af881d933d41bdac60e51329aadbbd354` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/public-named-declarations-v1.json` | `ed9d75ba60066b669baae4ef731407ed4dd9d8ec5d0710332d1c167183c19510` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/public-safe-SourceNormalCone-v1-exit.json` | `55393d26312fc4a882c486934f691108f76949396cf01f61f765d57d6ea60432` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/public-safe-SourceNormalCone-v1.log` | `683f6080d1a7a995dd9a1821d7fb98e35365544a19f6ad765412cf5d05668786` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/public-safe-indicator_subdifferential_eq_normalCone-v1-exit.json` | `b96498afdeba52660c8cc28e214b817981202c5bfec67b0d62dfeaa9061eabc3` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/public-safe-indicator_subdifferential_eq_normalCone-v1.log` | `e151e33af45ae01a79c106eee19fea35956431466a123264a12c8b7172b4b517` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/public-safe-normalCone_interior_eq_zero-v1-exit.json` | `5694dc186dc18ae6ad3070010b7b68d9ad5e81540dd04c0716c23adbec2d674e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/public-safe-normalCone_interior_eq_zero-v1.log` | `48614f7d63c73917b0514ac282c37f2279c892676287c385efc536e88b876ce3` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/public-safe-normalCone_unitBall_boundary-v1-exit.json` | `9d7d3119dec527532ac336b1c1ee35ec47497449d3b1860ddf66b6aaeac9ad13` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/public-safe-normalCone_unitBall_boundary-v1.log` | `babd00c10a0b38dba0ded489ab2dcf8a6a5cf933a9fb45ae8e3a51e9b00be241` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/readiness-generated-before-use-v1.json` | `7e48a350dda33e819e3f7c0a801c9151e2610e8c52caf4369b7230cf4f9de7b3` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/ready-dependencies-v1.json` | `5cbde55da656db1b7431aef73d6b904b154fdbead9da2cbd45df4ea133dd0d03` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/record-body-resolution-repair-event-v1-01-exit.json` | `e687e529cf810a54c091c944f007f76d23605296cbc3b9aa40ca9c377b8b83a7` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/record-body-resolution-repair-event-v1-01.log` | `6a54ab55847c8d8f5e43f6c90b8ae73e6e335cd16ea42746933f2c04f44f2672` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/record-body-resolution-repair-event-v1.py` | `bb89de91a8fa0144d2651437a03809ad71c96b77fec79bf6a514ef549e321de9` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/repair-lifecycle-v1-exit.json` | `ee6e5a97ef70909a2d1c01970c207af2939dc763f0b2817118464959e709f89d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/repair-lifecycle-v1.log` | `fe1f1d291d1175bcd432bd4075e47a1afc825002c696a2bd5603b5e48685dbaf` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/retained-body-trial-v1-exit.json` | `44ace78d3e2de1bc03daedf03e8f3f9be15f7d4a6439a0cf818de27d3d3c4d9d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/retained-body-trial-v1.log` | `7254c2947cde06596a05d078bfac83683e50dfccb1c0a3f8aa8d262ec555f2cf` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/retained-focused-v1-01-exit.json` | `108aef680b07a0a56ff3b0f51a8b58b7e3b3b71d534b658042ae403417020366` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/retained-focused-v1-01.log` | `12a3638d2e2f1b2a487e31e65064fef0a31fcb09e27b3e9d567c7245f6af7d74` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/retrieval-index-draft-v1.md` | `ed9f631a9918e045f8ac114f2cfe932e6fd2f92c24ef94692785906dbc1a9d20` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/retrieval-record-help-v1-01-exit.json` | `401a62024f07a7f941b5eae17b6219a568610a552fb531ce0edae7fe14ce9ca1` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/retrieval-record-help-v1-01.log` | `73ac93f120215511ff0370d7ce100a9d0e83598ad882bcc5773cd1dc889b5321` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/retrieval-record-v1-exit.json` | `e8749bd66a091140193ff7f7caf941fb9b5f783ac1c039990547b6046e3e06bb` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/retrieval-record-v1.json` | `75dda3948c8c28cf415ecd4b964ec3d32f9e0b88aa56b365b279a2360abccbea` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/retrieval-record-v1.log` | `b440ffdc57bd2e572fde9b7857c86a905343ef9e8ca6952756745f9f0dafdf26` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/revalidate-bodies-v1-01-exit.json` | `ad06b84b85cc99d8ab8d31312f294ca356cde368f97912b7e37f460cdb695fd4` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/revalidate-bodies-v1-01.log` | `9e73acf9e9dd6c724513cc2174e78062df22e1b2e12b852eba2239d7507c7a75` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/revalidate-bodies-v1.py` | `65ca70f0f8a7babd61fc98c176b46cfb824953a897d6bda4a44dd24efc5a1d34` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/review-packet-helper-before-use-v1.json` | `eb63b6af270a667e39fe6f48df64dd378c5b31cf9bf4e58bba184974fc861e0d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/review-packets-v1.py` | `eadf1963c71eb2d4fee27fae89367bd1f61755ed2928daf7cb2938107001d92b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/review-packets-v2.py` | `0fe49bc57029ccfe8e668effa6d9075871a01371bbb211c21d9eb615126ddaf7` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/run-command.py` | `cb0e98401a104a6f0ad87f684a69a4e776e1de9de7d5b2a7848a394cad0a5db1` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/safe-verify-help-v1-01-exit.json` | `fb84709cce44b9af5fa03a04618fa47e07042928cc54697173a99bd19855214c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/safe-verify-help-v1-01.log` | `1773541c625f225e5a9abc61985c3ad19e871cf31aa0cf89cc440b3d8398862c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/search-memory-help-v1-01-exit.json` | `6c03c468cdbd3a1e22258bad21e9634c477f61a26976798f3795916f4d1ece04` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/search-memory-help-v1-01.log` | `b2f23faf2d0ee17c305335680ebdb2b83ca61999d18021e355d22587d712b79c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/snapshots/before-BanditRLProof--OnlineClosedProper.lean.txt` | `c66f00c33b45fb8a0e11583eeadf506e176c16166ce2af02f41f0674507cebe7` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/snapshots/before-BanditRLProof--OnlineConvexExtended.lean.txt` | `bd30bb95a46ccdc3f6d25f808c175af5fee71d075c2b46ffcf6508f15f1ed66a` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/snapshots/before-BanditRLProof--OnlineNormalCone.lean.txt` | `95fa41f9bf3f04354b0175c1f755786e86c103040f54aed9eab5fbf8a206539d` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/snapshots/before-BanditRLProof--OnlineSubgradientAbsolute.lean.txt` | `bf3e8d97f67b78e7ad230b8efd321948f4d7ba1a0e9cde31e8d85c1e9019442b` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/snapshots/before-BanditRLProof--OnlineSubgradientBasic.lean.txt` | `af3d3f56e4a64cd8adbe47368caf5382e63b428f01da29a121c28c8014f352a5` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/snapshots/before-BanditRLProof.lean.txt` | `351d5238e97cf54ae4c5f65a7e82cabc40ac7eb6f18c9e64e89e27a6610cb9c6` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/snapshots/before-MANIFEST.md.txt` | `bcc85d267f45cb7d5bf550528a927e20afae1b167aac2be8f2fafaf0efe3c158` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/snapshots/before-Tests--OnlineNormalConeCanary.lean.txt` | `b893dad6e8128fe674acb19fd7774de036e953dee8d446d1cd214d20476a2790` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/snapshots/before-Tests.lean.txt` | `cd21ef4e7cea89c7d245eaf4dff14be8baa34f2d336e40d6f6bbb16011678340` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/snapshots/before-lake-manifest.json.txt` | `87c3e616f86244550ef39e7415186b11c1d4cf4bef20173196a619d9d4d48f48` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/snapshots/before-lakefile.lean.txt` | `0164f3b5b5bdcbb237ab15ae8b44da83e183f4b97d5f3832aa4a57f27dc69d45` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/snapshots/before-lean-toolchain.txt` | `b15a57f8ea4c890197465ce1156667ae13d9ed4ab8a9f263a920bf010d967d82` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/snapshots/before-runs--active_frontier.json.txt` | `567e5873aa2549a83f2820d758069213808da822a93087129877385a1addf7c3` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/snapshots/before-runs--lifecycle_sessions.jsonl.txt` | `a83d61df8663da5e18df7e224d75a314a18cac620104df83a0882553686cd439` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/snapshots/before-runs--trials.jsonl.txt` | `079c0903e5f21a99583279ebe75e9aa5fc8d295bda893dceab204b2a02b01e39` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/snapshots/before-website--content--chapters.json.txt` | `8d837318ebd9304d919200cad74f74c29e74b985e6b375a024f31911a92974c6` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/snapshots/before-website--content--highlights.json.txt` | `a52447da51409d17393660958d0b2286933f06f2e9fd6cd569bf7f1193e3b1df` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/snapshots/before-website--content--readings.json.txt` | `c446ac838bfa6aa975e8b0ee5f504477c8a2a3281565455dcb8aa4ad88ceeca5` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/snapshots/body-reviewed-runs--lifecycle_sessions.jsonl.txt` | `cf9e2838e85db1a6ab8fb54cb8676c635d45b2948115cd1f7026e87abdd15a2f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/snapshots/body-reviewed-runs--trials.jsonl.txt` | `3c1464b5a47d971746550ce3025a3b1f4a93d8103a628adfd19c77e6688378d8` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/snapshots/contract-reviewed-runs--lifecycle_sessions.jsonl.txt` | `80fa6c7d7bf00ae94648a34c7832b8fd2fafce73478ffd94c0c737b6653e518f` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/snapshots/contract-reviewed-runs--trials.jsonl.txt` | `079c0903e5f21a99583279ebe75e9aa5fc8d295bda893dceab204b2a02b01e39` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/source-contract-inputs-v1.json` | `3124efe8a2208d80770c19d618c162f2aa1bbf086eb68927849ccfeee2e73b7e` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/source-contract-packet-v1.md` | `83e3a752df113225e9d436b9d66150d872a184a0a6c7f4c12c1ad7618d8cd798` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/source-contract-receipt-v1.json` | `fd08cabd87e5a1ba6845fd2e2b181baef7971867bac8119c04f6445ea793b8fd` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/source-contract-review-v1.md` | `6ecef68153c73ca4bcc425f2e4635b0642574feb4740579f988bf087e7366371` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/source-printed18-pdf30.txt` | `79a3aacef74fc16fd80b21ef87043e0ff5999ff6cf540e4741f09ca6c6447edc` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/stabilized-leaf-selection-v1.json` | `a084a799e1c36fa2d3a466216dafb2f60485ccff6f230e892c72fa535c3c779c` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/stabilized-lifecycle-v1-exit.json` | `b2b640561ee7f76ac906c4648ea595bf9dc242ec5f77bd24f0a50919bbfb2cff` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/stabilized-lifecycle-v1.log` | `5b882f0db896846557379a2795dd11b92c6b907f73986a4574682ced77de1144` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/statement-fence-help-v1-01-exit.json` | `11a99477b0e1aaee7b6d227b2f4ca3ee38ae887e5e09f2a17b4226e409b82b97` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/statement-fence-help-v1-01.log` | `4f4fca9dfaac7a7c3de8025d3d0f7c4ba58d1f4b33feb08d19e12229942dba75` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/trial-log-help-v1-01-exit.json` | `b482ff3cfb27e8c3ec33bed4449383fcfff4a0e6fc3b2d80d1b9595ba3531b96` |
| `E:/ABRL/worktrees/research-online-book/runs/online-normal-cone-migration-20261007/trial-log-help-v1-01.log` | `ea7bd7e4d64216b46f554a90e02a3d58b4fcbe72766c2f7b316b656b94d19b32` |
| `E:\ABRL\worktrees\research-online-book\tmp\online-subgradient-sum-source-pdf30-v1.png` | `c4354de7297923fd82f74645ddd50fdb582f90b6eeb9a7536fd9f33ec5489ebd` |
| `E:\ABRL\worktrees\research-online-ogd\tmp\pdfs\orabona-v10.pdf` | `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17` |
| `MANIFEST.md` | `bcc85d267f45cb7d5bf550528a927e20afae1b167aac2be8f2fafaf0efe3c158` |
| `Tests.lean` | `cd21ef4e7cea89c7d245eaf4dff14be8baa34f2d336e40d6f6bbb16011678340` |
| `Tests/OnlineNormalConeCanary.lean` | `b893dad6e8128fe674acb19fd7774de036e953dee8d446d1cd214d20476a2790` |
| `docs/contracts/online-book-v1/source-inventory.json` | `a2a504cf40d73f9c5e36f00fc1ef3b949ccaf5a558ab603c1c2a86007f30efa7` |
| `docs/contracts/online-normal-cone-migration-v1/contract.md` | `bca4da1f80017b7ba15fbad030f41b86b6b23ddeed78a30204c2b7045db95506` |
| `docs/contracts/online-normal-cone-migration-v1/headers.json` | `77548053e933a25289f69c8695126d8437308840e3f55e70b9a346afbfecef7e` |
| `docs/contracts/online-normal-cone-migration-v1/initial-dependency-DAG.json` | `6785bc98b84a7b877914c94c687ee7fa686c10b6a627f3184d3045add722486e` |
| `docs/contracts/online-normal-cone-migration-v1/scoped-contexts.json` | `7b14fcf8574286c103fcd3fed6724e0a6c481cee9a863bd977a554e6134339e2` |
| `docs/contracts/online-normal-cone-migration-v1/source-card.json` | `6eb3eccc49111000f2d214d292aacc3ebabe9b76ddf2c47adb93cb638fa72fbd` |
| `docs/contributor-codex-contract.md` | `d7dfa3406def35de292b202f45ff8303b9a550310bd00979be838e5a2348a498` |
| `docs/theorem-publication-protocol.md` | `b1e5ac73cfe0a90742567736b422787c90a51e6b6ff007cc1dc8d598948f687e` |
| `lake-manifest.json` | `87c3e616f86244550ef39e7415186b11c1d4cf4bef20173196a619d9d4d48f48` |
| `lakefile.lean` | `0164f3b5b5bdcbb237ab15ae8b44da83e183f4b97d5f3832aa4a57f27dc69d45` |
| `lean-toolchain` | `b15a57f8ea4c890197465ce1156667ae13d9ed4ab8a9f263a920bf010d967d82` |
| `research-wiki/mathlib-candidates/README.md` | `ea4ed80d4eed053d0eea0d315df86075a9445e6280e2a827e3841e5c05d7df37` |
| `research-wiki/mathlib/theorem-cards.md` | `4656c1a8ccd4b2d8523cf5cf48bd1f966e7ba2c2237e2e578d6b8c2ecc6fbd97` |
| `runs/active_frontier.json` | `567e5873aa2549a83f2820d758069213808da822a93087129877385a1addf7c3` |
| `runs/lifecycle_sessions.jsonl` | `56c795eee8bc7b4c918780e07e280d100699d2ab888abaa7ccc0f9086ad09e61` |
| `runs/online-normal-cone-migration-20261007/public-body-inputs-v1.json` | `d17f46d27496b6442268e1c1195087a52df42b67a72aa05a3e318ed391638c91` |
| `runs/online-normal-cone-migration-20261007/public-body-inputs-v2.json` | `499a10f1e24293738bf2dd1d381cf2456da0c7c489919b42d37d56c9e9f38cfd` |
| `runs/online-normal-cone-migration-20261007/source-contract-inputs-v1.json` | `3124efe8a2208d80770c19d618c162f2aa1bbf086eb68927849ccfeee2e73b7e` |
| `runs/trials.jsonl` | `3c1464b5a47d971746550ce3025a3b1f4a93d8103a628adfd19c77e6688378d8` |
| `tmp/online-subgradient-sum-source-pdf30-v1.png` | `c4354de7297923fd82f74645ddd50fdb582f90b6eeb9a7536fd9f33ec5489ebd` |
| `website/content/chapters.json` | `8d837318ebd9304d919200cad74f74c29e74b985e6b375a024f31911a92974c6` |
| `website/content/highlights.json` | `a52447da51409d17393660958d0b2286933f06f2e9fd6cd569bf7f1193e3b1df` |
| `website/content/readings.json` | `c446ac838bfa6aa975e8b0ee5f504477c8a2a3281565455dcb8aa4ad88ceeca5` |
