# Basic subgradient migration: independent contract review

**Verdict: accepted-with-explicit-delta.** Mathematical repairs: none. Reader corrections below are required before final reader/package acceptance.

Actor `/root/source_reviewer`, distinct automated source reviewer; requested GPT-6 Astra / medium. No human/external review or runtime-model attestation. Restricted current blind reconstruction is not a claim of erased prior history. Old20261003 verdicts are historical, not authority for this decision.

All122 fixed raw rows independently rehashed, with no mismatch; inventory itself additionally bound. Source PDF SHA256 `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17`; printed16–17/PDF28–29. Original Definition2.20 says proper; page17 omits convexity from the definition but includes it in the adjacent domain observation. Theorem2.21 has globally real f and assumes support nonemptiness on convex V. The v2context correction accurately distinguishes these.

## Complete definition: seven slots

- **objects_spaces**: All EReal functions on real inner-product E; no SourceProper argument in generic definition.
- **quantifiers**: For fixed f,x,g, ∀y:E; the definition returns all supporting g, not a chosen member.
- **assumptions**: No convexity/properness/point-finiteness restriction in Lean; source Definition2.20 explicitly proper.
- **conclusion**: {g | ∀y, f x + ↑⟨g,y-x⟩ ≤ f y}; exact orientation and finite real embedding.
- **constants**: Coefficient1, no threshold, error or normalization.
- **information**: Static set-valued predicate, no oracle/feedback/probability.
- **boundaries**: At bottom every g; for identically top every g. Finite addend avoids mixed-infinity addition. Faithful source interpretation requires proper specialization.

The real embedding is proper because it is nowhere bottom and has finite value at zero. Thus Theorem2.21 needs no extra SourceProper parameter. In contrast, the all-EReal generic predicate cannot imply domain membership: f≡top has every support although its effective domain is empty. The existing proper finite-witness premise prevents that counterexample.

## Exact targets

### BanditRL.OnlineConvex.subgradient_point_finite

Verdict: accepted-with-explicit-delta

- **objects_spaces**: f:E→EReal on arbitrary real inner-product E with NormedAddCommGroup; no completeness/finite-dimensional hypothesis.
- **quantifiers**: For every proper f and every x,g, actual g membership implies x belongs to effectiveDomain. The support inequality queries every ambient y.
- **assumptions**: SourceProper supplies nowhere-bottom and an actual finite real witness; no convexity. This drops the convexity included in the source adjacent observation.
- **conclusion**: f(x)<top; combined with hf nowhere-bottom, genuine finite value. Exactly converts to dom∂f⊆domf and empty support outside domain.
- **constants**: Coefficient1, finite real inner product, strict below-top domain cutoff; no norm or approximation bound.
- **information**: Deterministic static assertion, no probability, oracle, selection rule, feedback or existence of support supplied as a conclusion.
- **boundaries**: E is nonempty through zero; V absent. Generic bottom/identically-top predicate cases are outside proper specialization. No converse/domain equality/interior-existence result.

Existing proof extracts finite witness y,r and evaluates hg y; top+finite≤finite is impossible. It never imports the desired finiteness conclusion. No body-phase acceptance here.

### BanditRL.OnlineConvex.theorem_2_21

Verdict: accepted-with-explicit-delta

- **objects_spaces**: Globally REAL-valued f:E→ℝ, convex subset V; same SourceSubdifferential applied to global real embedding. Real inner-product generalization of Euclidean source.
- **quantifiers**: ∀x∈V ∃g ∀y∈E supporting inequality. Vector may depend on x, fixed before y; global y is not restricted to V.
- **assumptions**: Convex ℝ V and actual support nonemptiness at every feasible base point, precisely the printed hypothesis. Does not assume ConvexOn f or produce general support existence.
- **conclusion**: ConvexOn ℝ V f: convexity of V plus convex-combination inequality. No global convexity beyond V.
- **constants**: a,b≥0 and a+b=1, equivalent λ∈[0,1], includes endpoints0/1. No smoothness or error term.
- **information**: Static deterministic implication; no measurable/continuous/causal support selection conclusion.
- **boundaries**: Empty V permitted, ambient E nonempty. No closure/boundedness/interior/differentiability or CompleteSpace/FiniteDimensional assumption. Not arbitrary EReal f merely finite on V.

Existing proof selects supplied support at the convex combination, tests both endpoints and cancels the weighted inner displacement. This matches source proof and does not assume target convexity.

## Required source-domain consequence

Fix proper f. From ∀xg,g∈S(f,x)→x∈D, unpack a witness g to obtain {x|S(f,x).Nonempty}⊆D. Outside D, any g would contradict that implication, hence S(f,x)=∅. Conversely either universal outside emptiness or domain inclusion yields the point statement. This discharges the specified logical source observation without a duplicate wrapper, not interior existence.

Both normalized native headers independently match their frozen hashes: subgradient_point_finite `0283a2c9fdd9094e78272c1987b48d4b8920d4c52796753d4ce0466ffddfdd62`; theorem_2_21 `6077cc1eec096063073ea3fe7262db814ffc27392e9422f40fa8d985e208bfdb`. Actual @types match scoped contexts. The current graph has3nodes and320 distinct source-target references (376 if separately counting duplicated type/value occurrences), no mutual terminal value edge. This is readiness evidence, not fresh body acceptance.

Actual canary source is meaningful: global square support2x from residual square, public theorem applied to get square convexity, and every vector excluded at2 for the proper interval indicator. This contract pass does not certify fresh canary/axiom/integrated gates.

## Required reader corrections

1. Explicitly state Definition2.20 is printed for proper functions; generic all-EReal SourceSubdifferential is a wider library predicate, faithful on the proper specialization. Preserve the initial00_context error as superseded history.
2. Disclose bottom-point and identically-top all-vector degeneracies of the generic predicate. effectiveDomain excludes top but includes bottom generically; properness gives actual finiteness. Inner-product E has zero/nonempty, unlike prior arbitrary topological carriers.
3. Explain finite-witness proof and the exact dom∂ inclusion/empty-outside conversion. Explicitly label dropping source convexity a stronger theorem, not identical assumptions; no converse or support-existence producer.
4. Give theorem-specific assumptions: Theorem2.21 globally real f, Convex V, ∀x∈V ∃g ∀ambient y support. Its support-existence hypothesis is printed, not a proof gap or a produced existence theorem. Do not extend to merely finite-on-V EReal functions.
5. Expose arbitrary real-inner-product generalization without CompleteSpace/finiteD; allow empty V but not empty ambient E; include weight endpoints0/1.
6. Distinguish two independently ready proof leaves sharing one complete definition from a causal/dependency chain. Actual scoped graph3nodes320distinct source-target references is not a full/canary export.
7. Accurately describe three genuine canary proofs, six planned named checks including complete definition, and two guards distinct from compilation. Use actual fresh gate status only after later body/integration stages.
8. Count two numbered anchors plus required adjacent unnumbered domain group, two retained proofs/one definition/zero new nodes. Interior existence and relative-interior footnote, Theorems2.22/2.23, Chapter2 and whole Goal remain mandatory/incomplete.

The current reader already identifies global queries, real-valued Theorem2.21, proper finite witness and the quadratic example. Its phrase source claims impose properness where needed is too indirect for the printed definition restriction; the generic infinity degeneracies and exact domain-conversion/dropped-convexity distinctions need explicit display. The current shared contract text across both cards should be made theorem-specific. No silent header weakening is authorized or needed.

## Limits

Acceptance stabilizes only these contracts and source deltas. Two retained proof leaves/one definition are not two new printed theorems. Required interior existence (including relative-interior footnote), later subgradient rules, all remaining migrations and the persistent whole-book Goal remain open. No chapter completion, merge, deployment or new proof-count gain.

## Raw read/binding inventory

All fixed rows were read as raw bytes for hash validation. Mathematical content was inspected in the source, full current module/context, shared definitions, pinned APIs, current reconstruction, native headers/types, scoped graph and selected reader; administrative/old receipts are provenance, not semantic authority.

| Path | Raw SHA256 |
|---|---|
| `../research-online-ogd/tmp/pdfs/orabona-v10.pdf` | `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17` |
| `.agents/skills/bandit-semantic-roundtrip/SKILL.md` | `7ee7b72b8a84ab954966dc13900952c3439bd8d4e97877b622c1ca0a7aa85477` |
| `.lake/packages/mathlib/Mathlib/Analysis/Convex/Function.lean` | `88a435998bf0e4b2051e00ecd04d847f0434e5d67c1298b5eecff9d2936411ad` |
| `.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean` | `e80bb3d346ad6dcaceab9c99dd57025809e3beffded7f92b71104df5fc72d698` |
| `.lake/packages/mathlib/Mathlib/Data/EReal/Basic.lean` | `bf69a9ed4bc39134bbefac1a43b187e2f1e66fd43f352d0810ab89474f054922` |
| `BanditRLProof.lean` | `351d5238e97cf54ae4c5f65a7e82cabc40ac7eb6f18c9e64e89e27a6610cb9c6` |
| `BanditRLProof/OnlineClosedProper.lean` | `c66f00c33b45fb8a0e11583eeadf506e176c16166ce2af02f41f0674507cebe7` |
| `BanditRLProof/OnlineConvexExtended.lean` | `bd30bb95a46ccdc3f6d25f808c175af5fee71d075c2b46ffcf6508f15f1ed66a` |
| `BanditRLProof/OnlineSubgradientBasic.lean` | `4c17a466091b88d90451be897a2f01afa204b41933191244e0093e48396d1962` |
| `Tests.lean` | `1c60f84f3e4d6d778ac8374b46e47b27559d802986459533517034c97a30f048` |
| `Tests/OnlineSubgradientBasicCanary.lean` | `f031106fc8f3fdec2bc1118fba66494a6782e1d2d2764937ea9bffc676d20c4c` |
| `conversion-windows/ONLINE-SUBGRADIENT-BASIC-MIGRATION-20261006.md` | `deb3a473a1c68791c3456a2f3ada3a15bf4e2f73fd3b1367a39703769b5bc0b0` |
| `docs/contracts/online-subgradient-basic-migration-v1/dependency-DAG-v1.json` | `bd14bcd04f062212ea2ee12502e6778b99a1b348fe4ebf29986703e138f82259` |
| `docs/contracts/online-subgradient-basic-migration-v1/headers.json` | `c7b60223ad97ffd4ea481e6b320252b31fbd3f373aa85413be671bbf2b09b83d` |
| `docs/contracts/online-subgradient-basic-migration-v1/scoped-contexts.json` | `8f9505e35d08a2a20a5896dc765157d19c6e8edfc0641271121cd1b9fddbd86f` |
| `docs/contracts/online-subgradient-basic-migration-v1/source-card.json` | `e7870fade027b927a69475c040536c95a1ffb64041d2538165f74872603e80bc` |
| `docs/contracts/online-subgradient-basic-migration-v1/source-intent.md` | `d49174fb1d280462c0d22ab43c7cb2d8f5f834ea62929274063960a0bcb359aa` |
| `docs/contracts/online-subgradient-basic-public-v1/contract.md` | `183b06617e7a1721e939cc8894bde35b74ff8da65075dffc6e02a5ca8db078b9` |
| `docs/contracts/online-subgradient-basic-public-v1/integration.json` | `af2f236a5f924d0c02dae09f5897236d56a69bf1dae141fb36ec78897aa44288` |
| `docs/contracts/online-subgradient-basic-public-v1/subgradient_point_finite.json` | `0b7e72c248ecde02ea861c9618fa477793e89295cf0390474c92d677f64a6816` |
| `docs/contracts/online-subgradient-basic-public-v1/theorem_2_21.json` | `3ee488588650dd60a826f9ea88be6c463deb80a166db75596bac558fec3a2762` |
| `docs/contracts/online-subgradient-basic-v1/context.txt` | `92d545dc9d566c09a2cf44809477c11fa649d855d3f541593a316ab93dffcc34` |
| `docs/contracts/online-subgradient-basic-v1/contract.md` | `bc6186d58620f86b83b5b2f98aa57e1abddbb987171b43da685c8f7eb1803c5e` |
| `docs/contracts/online-subgradient-basic-v1/headers.json` | `f21e451dd5f0c2145e72cac3a01c46e20a47c504b1fe7e5cf4708bc8a41e7972` |
| `docs/contracts/online-subgradient-basic-v1/subgradient_point_finite.json` | `90811bf1909c6b2b779eee3e0ccafcf66e3f322097a98dc7e20b675ccf770c1f` |
| `docs/contracts/online-subgradient-basic-v1/theorem_2_21.json` | `fa7deae0882785c03b7f88e3be47b499b73a7efabf522b893b6f83e39d0a3c06` |
| `lake-manifest.json` | `87c3e616f86244550ef39e7415186b11c1d4cf4bef20173196a619d9d4d48f48` |
| `lakefile.lean` | `0164f3b5b5bdcbb237ab15ae8b44da83e183f4b97d5f3832aa4a57f27dc69d45` |
| `lean-toolchain` | `b15a57f8ea4c890197465ce1156667ae13d9ed4ab8a9f263a920bf010d967d82` |
| `proof-obligations/ONLINE-SUBGRADIENT-BASIC-MIGRATION-20261006.md` | `deb3a473a1c68791c3456a2f3ada3a15bf4e2f73fd3b1367a39703769b5bc0b0` |
| `runs/active_frontier.json` | `567e5873aa2549a83f2820d758069213808da822a93087129877385a1addf7c3` |
| `runs/online-closed-proper-migration-20261006/accepted-decision-v1.json` | `638d4873b46f2189adc1a5145a9cf6efd5a47ce7ddf164e10c69b42cf1b3c41f` |
| `runs/online-closed-proper-migration-20261006/delivery-v1.md` | `3f38739febc454354d2cb044526d6f545d92ba5e480659b42fbb37d9def663e2` |
| `runs/online-closed-proper-migration-20261006/native-acceptance-overlay-v1.json` | `7fd8b31fd4e44f4b373ce5854d11a4e5cde13dd949b4eb095a40db87cd0625eb` |
| `runs/online-subgradient-basic-20261003/acceptance-evidence.json` | `52396ebc90cb6a2cb1de27824089b588e4ffc53532be7e0c179cb47c52db7028` |
| `runs/online-subgradient-basic-20261003/independent-source-review.md` | `f3113c2cb4149d383d18f33465466abfa29a403862a46433ff7fffe1ff1f3409` |
| `runs/online-subgradient-basic-20261003/roundtrip-bindings.json` | `890da16e807e992fa2bae2fe5d5a8412d2d0bd70a0066b69a2e795b48a67a95e` |
| `runs/online-subgradient-basic-migration-20261006/.gitattributes` | `705fd4d6451a31d36b3df7de96f83f30ac976c9b4a6d1e51671d8e2f33e2d0da` |
| `runs/online-subgradient-basic-migration-20261006/00_context-v2.md` | `ae66594ab9928fbac7f7c3096a03f7dce4f44d53abb3473c4b908cbe297690c3` |
| `runs/online-subgradient-basic-migration-20261006/00_context.md` | `d83d3ece834edd78dcdb4218107b6cc46c789ee9688c1b116ba997a4c5c92e27` |
| `runs/online-subgradient-basic-migration-20261006/10_upper_director-v1.md` | `38fd111848308b47449b8dda6363c700e69eb752ffb11546927884c59b824433` |
| `runs/online-subgradient-basic-migration-20261006/20_architect-v1.md` | `2c8301e1538d247e05c6ccd56aa5751ee9bf29b7d121363cd2b1286cc2c7babf` |
| `runs/online-subgradient-basic-migration-20261006/CLI-help-v1-01-exit.json` | `1e2960f6eb6c8d760832d605187bb5cf1d38309ab2d57b0e2f6927c1dac0a53b` |
| `runs/online-subgradient-basic-migration-20261006/CLI-help-v1-01.log` | `daacf23e36eec4898dce3b3de02a07b71fb0f80f08e33e8dfe00722e7572970c` |
| `runs/online-subgradient-basic-migration-20261006/actual-types-readable-v2-01-exit.json` | `171961fd4da30e52f1b016865de8ab7c5134cbbe0637275e6f8f04b1bc01f4b9` |
| `runs/online-subgradient-basic-migration-20261006/actual-types-readable-v2-01.log` | `705908d0757c51767f8caaad142a7117279ab0a77bf6dc5d2c88e0fd22261b2d` |
| `runs/online-subgradient-basic-migration-20261006/actual-types-v1-01-exit.json` | `c1cb7c2603cc2e96dd73db71f16346ef9458c5243228cba4622078da438539a9` |
| `runs/online-subgradient-basic-migration-20261006/actual-types-v1-01.log` | `aa4cba2f1d7a4d05d2cb6b07beba773859bc08731b587579d6ba1da4049a18c4` |
| `runs/online-subgradient-basic-migration-20261006/blind-packet-v1.md` | `ecbb1d5c872b805895ea89db4227831ad6e2d6baae660ecac3f017d03068970a` |
| `runs/online-subgradient-basic-migration-20261006/blind-receipt-v1.json` | `b9084045c72bb8af9ac3d143b60332179565e0c8e33e528bb4d243f3cc0e2549` |
| `runs/online-subgradient-basic-migration-20261006/blind-reconstruction-v1.md` | `9208663b5e6bcdc84068ffa81c4fdb0344f0f09a316bae43f4083441ec4455b4` |
| `runs/online-subgradient-basic-migration-20261006/bootstrap-before-use-v1.json` | `36b80a36d75424650e147fcb12322eab4842acb49d3d69975eac5115b2006830` |
| `runs/online-subgradient-basic-migration-20261006/bootstrap-generated-before-use-v1.json` | `a0286186bff29eeee62e44b1a73978070c702812cf55587e297c8f8140a4fd89` |
| `runs/online-subgradient-basic-migration-20261006/bootstrap-v1.py` | `0fa211a3ec89b7111fa1be6f6787ff25534adc116cc8b8a4a540a3ffb9d724aa` |
| `runs/online-subgradient-basic-migration-20261006/compiled-retained-graph-v1.json` | `bb43aafe7d956cbb61afa4f5b40b33e5c6daa14fa003510fa9a1082c183d5ecc` |
| `runs/online-subgradient-basic-migration-20261006/compiled-scoped-graph-v1-01-exit.json` | `5acbdbdfd9df9523ae6258434a9d7b59eb6d4b473fad7c675d395b2bbf337e29` |
| `runs/online-subgradient-basic-migration-20261006/compiled-scoped-graph-v1-01.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `runs/online-subgradient-basic-migration-20261006/draft-fence-subgradient_point_finite-v1-exit.json` | `43b5bf22158cbefb38a7dcbef5e59e92290b72927b476422918b464431382f94` |
| `runs/online-subgradient-basic-migration-20261006/draft-fence-subgradient_point_finite-v1.log` | `ebc41a4b84251c9324b97fd4470883ada1c55e4de8db7a5d5505ed117a10811a` |
| `runs/online-subgradient-basic-migration-20261006/draft-fence-theorem_2_21-v1-exit.json` | `c57f835f49d5c6a5c16c817646d61b0fe34a9e4f76b33bae7c2454f0b0b8f1e0` |
| `runs/online-subgradient-basic-migration-20261006/draft-fence-theorem_2_21-v1.log` | `437489596aaf51d252b6f7aab985b52e03630a963d2f49dbad284da77319ad51` |
| `runs/online-subgradient-basic-migration-20261006/draft-freeze-v1.json` | `1741c9632d82c5ea5d4effe8fbcd3e89d333931e09c5e07c4257574c15356674` |
| `runs/online-subgradient-basic-migration-20261006/draft-generated-before-use-v1.json` | `759889d2434d46cc2e4e22d5a03312078d60c43f25477c581dcf38d28afd7e64` |
| `runs/online-subgradient-basic-migration-20261006/draft-helper-before-use-v1.json` | `bbb81fd9c7fd3dc2be696334999a8451eff0918bc88665928eca6f6eb863fc46` |
| `runs/online-subgradient-basic-migration-20261006/draft-lifecycle-v1-exit.json` | `7545d568f9996aa2dd28a8e7c51b2b41a897a8f73b647b25e12c0b8896cd92fa` |
| `runs/online-subgradient-basic-migration-20261006/draft-lifecycle-v1.log` | `a27043f37703d31bb692d60061c8e5fe0c1a6ed022f29d1aba52f31264561fb3` |
| `runs/online-subgradient-basic-migration-20261006/fence-help-v1-01-exit.json` | `103fb0fa8949da2fcddfa050ab159cee63f9d78f1aa89ebee6c044ed8c604f90` |
| `runs/online-subgradient-basic-migration-20261006/fence-help-v1-01.log` | `4f4fca9dfaac7a7c3de8025d3d0f7c4ba58d1f4b33feb08d19e12229942dba75` |
| `runs/online-subgradient-basic-migration-20261006/historical-raw-supersession-v1.json` | `039bfd0bcf98c9004a18e8f033004783ab1279bd462f622d524c50b5b5445a28` |
| `runs/online-subgradient-basic-migration-20261006/leaves/actual-types-readable-v2.lean` | `1d7a9d4d504429a471097d449fc90e4055c32548fc2a5f111d6473705ebb8bbb` |
| `runs/online-subgradient-basic-migration-20261006/leaves/actual-types-v1.lean` | `7c989ff8ca74996deb6a8ee5ec9e45b36c92bb3c31c346bfe19b8c466c9bd8d7` |
| `runs/online-subgradient-basic-migration-20261006/leaves/export-scoped-dependencies-v1.lean` | `cb99674d7e47fd304ad4fd5d8cfc7d2f0430f9dec1a12cebc13fe0194628d8e9` |
| `runs/online-subgradient-basic-migration-20261006/leaves/pre-integration-BanditRLProof--OnlineSubgradientBasic.lean.txt` | `4c17a466091b88d90451be897a2f01afa204b41933191244e0093e48396d1962` |
| `runs/online-subgradient-basic-migration-20261006/leaves/pre-integration-BanditRLProof.lean.txt` | `351d5238e97cf54ae4c5f65a7e82cabc40ac7eb6f18c9e64e89e27a6610cb9c6` |
| `runs/online-subgradient-basic-migration-20261006/leaves/pre-integration-MANIFEST.md.txt` | `c234127c39798e29623cf8a46c857fffee1e86eb01f0f88349d750960dc77611` |
| `runs/online-subgradient-basic-migration-20261006/leaves/pre-integration-Tests.lean.txt` | `1c60f84f3e4d6d778ac8374b46e47b27559d802986459533517034c97a30f048` |
| `runs/online-subgradient-basic-migration-20261006/leaves/pre-integration-runs--lifecycle_sessions.jsonl.txt` | `dc60fe0d97254b5141b190947f261c7bd85b31f8a0e23f459620f17129f98d42` |
| `runs/online-subgradient-basic-migration-20261006/leaves/pre-integration-runs--trials.jsonl.txt` | `95bd414b31a2eac2c740fe36f7d40e60f553b44cc78730fa2e6ff0da5febecf1` |
| `runs/online-subgradient-basic-migration-20261006/leaves/pre-integration-website--content--chapters.json.txt` | `677e05d2fe928fb8f8c2c392fed0b5a7c431484154d17fee831cc9023c72ac32` |
| `runs/online-subgradient-basic-migration-20261006/leaves/pre-integration-website--content--highlights.json.txt` | `78d342b3dd0b8d2ca98c79fc4c13030e81846755972d294c179f27fde711a2fe` |
| `runs/online-subgradient-basic-migration-20261006/leaves/pre-integration-website--content--readings.json.txt` | `cd77cc0a8d16cdc8b4e3ddea7efeeae76fbf8cbd9ca0819126fe8eb7041d903d` |
| `runs/online-subgradient-basic-migration-20261006/lifecycle-help-v1-01-exit.json` | `82c4ccd69ea4a44fba884a4a217b06d9eced50df1d39b4de614f9c08f16ad6ab` |
| `runs/online-subgradient-basic-migration-20261006/lifecycle-help-v1-01.log` | `b1e8b438a9b725793b9888d206e98a971ace3df200ec90ed9cb63eab26b28507` |
| `runs/online-subgradient-basic-migration-20261006/list-mathlib-v1-01-exit.json` | `32892e2c6bca0ea72a530382f4859c096aac67f7a92793277ce7e85fa6cb7961` |
| `runs/online-subgradient-basic-migration-20261006/list-mathlib-v1-01.log` | `884fab88619a3d1adcafe89eecddd2d98f4be5c6fa61262862134dde9e51d225` |
| `runs/online-subgradient-basic-migration-20261006/list-papers-v1-01-exit.json` | `334146bb5d0f510b78896e29f1b85c2b65c6b8754012d67405a092db875a8374` |
| `runs/online-subgradient-basic-migration-20261006/list-papers-v1-01.log` | `9acd333996a893a7b5ccad3e674ece26ef05c8b737e7816b33043b121583a619` |
| `runs/online-subgradient-basic-migration-20261006/list-weapons-v1-01-exit.json` | `005bdac4afab2ca03c38c0f1b038fef29708fb41e941ac23e5b0bef1c7a314fa` |
| `runs/online-subgradient-basic-migration-20261006/list-weapons-v1-01.log` | `a6e4b78de1a30fcf5a0ee66b868eb3ac1bfa68d2250c713f61e690ae064f7ef6` |
| `runs/online-subgradient-basic-migration-20261006/local-lookup-v1-01-exit.json` | `acdd16a32a1c57df4ffc7b30454335b967aa5b0ea5db362104dc5f91de428242` |
| `runs/online-subgradient-basic-migration-20261006/local-lookup-v1-01.log` | `9754192a61442b6eeea66c63e08ac99c1c44d77aa2f11bd3222f7d287e05a223` |
| `runs/online-subgradient-basic-migration-20261006/local-retrieval-help-v1-01-exit.json` | `5b3bea30cc3a26881d83f37591993183a31d7e0fa2692a95b1c36094b1e8a1c2` |
| `runs/online-subgradient-basic-migration-20261006/local-retrieval-help-v1-01.log` | `258218f16a12b1a530d85ae83e6c2449237af8a0a1153bb35de40245d665b131` |
| `runs/online-subgradient-basic-migration-20261006/native-draft-fences/subgradient_point_finite.json` | `ebc41a4b84251c9324b97fd4470883ada1c55e4de8db7a5d5505ed117a10811a` |
| `runs/online-subgradient-basic-migration-20261006/native-draft-fences/theorem_2_21.json` | `437489596aaf51d252b6f7aab985b52e03630a963d2f49dbad284da77319ad51` |
| `runs/online-subgradient-basic-migration-20261006/original-BanditRLProof.lean.txt` | `351d5238e97cf54ae4c5f65a7e82cabc40ac7eb6f18c9e64e89e27a6610cb9c6` |
| `runs/online-subgradient-basic-migration-20261006/original-OnlineSubgradientBasic.lean.txt` | `4c17a466091b88d90451be897a2f01afa204b41933191244e0093e48396d1962` |
| `runs/online-subgradient-basic-migration-20261006/original-OnlineSubgradientBasicCanary.lean.txt` | `f031106fc8f3fdec2bc1118fba66494a6782e1d2d2764937ea9bffc676d20c4c` |
| `runs/online-subgradient-basic-migration-20261006/original-Tests.lean.txt` | `1c60f84f3e4d6d778ac8374b46e47b27559d802986459533517034c97a30f048` |
| `runs/online-subgradient-basic-migration-20261006/pre-stabilization-source-properness-correction-v2.json` | `0be3578a4147434a5f1e8351666013e47a8142dd4d545c97644c27910d9566e1` |
| `runs/online-subgradient-basic-migration-20261006/prepare-draft-v1-01-exit.json` | `528d4b8a4cdd30baf76c27dd613a893a0f4a0e2b4928f4d21c645f7c846a00d5` |
| `runs/online-subgradient-basic-migration-20261006/prepare-draft-v1-01.log` | `6e7879c460f626f4c628c869dcf02e427440349aa8d403fc006863d3f81d8d81` |
| `runs/online-subgradient-basic-migration-20261006/prepare-draft-v1.py` | `6aec0310cb22f02aa270ee67aac5a62e054ad5a0bc17e7dca160c035a1ca7aa2` |
| `runs/online-subgradient-basic-migration-20261006/prepare-source-review-v1.py` | `8b50ad21aa6f4f78ef9dadae913009e550644b0ba2e24b046e985c7b6b98da3d` |
| `runs/online-subgradient-basic-migration-20261006/proof-obligations-v1.json` | `05ca66e5eb1ca80266866ffb16238726bf243b873ec08ad9b70eed3c7d4260b8` |
| `runs/online-subgradient-basic-migration-20261006/public-named-declarations-v1.json` | `957840b662616041533b9d69a5344fc8d830d9448ddbc0bc2b888c24e16e9250` |
| `runs/online-subgradient-basic-migration-20261006/ready-dependencies-v1.json` | `558fed3b1100a326dea3ec4577c5c5e6ec19ba7aff1ab6e86754f55ddc7eca0d` |
| `runs/online-subgradient-basic-migration-20261006/retained-module-v1-01-exit.json` | `5876da49e1c88f58597685ede4c4eb857da8bb0fefa1daf1bf5037e2d929a90f` |
| `runs/online-subgradient-basic-migration-20261006/retained-module-v1-01.log` | `259534216db19e154607033c1232bd369dd709ab6302312e88e9666e44a06018` |
| `runs/online-subgradient-basic-migration-20261006/run-command.py` | `c513b8a171af602dd3f72af15823ed5f1308faccdb8526d5dcca87ddcbf86887` |
| `runs/online-subgradient-basic-migration-20261006/search-memory-v1-01-exit.json` | `b63a98b96228c920de891e236c1a2daaed5777386aa3ccb610cf5fec9c845b9f` |
| `runs/online-subgradient-basic-migration-20261006/search-memory-v1-01.log` | `ce0e1c6dde7563cf6f3c90d031eabb32e45bf04197dc13d79ea07839b3c69421` |
| `runs/online-subgradient-basic-migration-20261006/source-printed16-pdf28.txt` | `fc5f1c36f2124f1a4c04c2b56159420778760dc35f58924907058720a09214f5` |
| `runs/online-subgradient-basic-migration-20261006/source-printed17-pdf29.txt` | `38f58d214ab8616aef7b7147338f7fd91ecdcf159b5286ea47092cf4ece81c46` |
| `runs/online-subgradient-basic-migration-20261006/source-review-helper-before-use-v1.json` | `28e5a3d4d7370a16a1960356a96c04b44876d38909e72f2f12d0abdba6bed205` |
| `runs/online-subgradient-basic-migration-20261006/source-review-packet-v1.md` | `d496b0080e652c5edd0a0279b98a5343de67482272c8808dba4a57ef413aacfa` |
| `runs/online-subgradient-basic-migration-20261006/workspace-audit-v1.json` | `12a4be03c105bcd7059f9c1fb3be957ee3e5704e6ac10d50a7d507bc9c8defc9` |
| `tasks/ONLINE-SUBGRADIENT-BASIC-MIGRATION-20261006.md` | `deb3a473a1c68791c3456a2f3ada3a15bf4e2f73fd3b1367a39703769b5bc0b0` |
| `tmp/online-subgradient-basic-migration-compiled-retained-graph-v1.json` | `bb43aafe7d956cbb61afa4f5b40b33e5c6daa14fa003510fa9a1082c183d5ecc` |
| `website/content/chapters.json` | `677e05d2fe928fb8f8c2c392fed0b5a7c431484154d17fee831cc9023c72ac32` |
| `website/content/highlights.json` | `78d342b3dd0b8d2ca98c79fc4c13030e81846755972d294c179f27fde711a2fe` |
| `website/content/readings.json` | `cd77cc0a8d16cdc8b4e3ddea7efeeae76fbf8cbd9ca0819126fe8eb7041d903d` |
| `runs/online-subgradient-basic-migration-20261006/contract-source-inputs-v1.json` | `af71cc203d0208b9f39bd64ab8311afd6f6112f746cc0dfc2912d5766579a422` |
