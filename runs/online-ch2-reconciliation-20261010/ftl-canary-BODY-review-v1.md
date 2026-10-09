# Eight FTL selector canary BODY review

Verdict: accepted-with-explicit-delta. No blocking repair was found in the eight frozen Test bodies. This is a canary BODY decision only.

Actor: /root/source_reviewer, reused distinct staged automated reviewer with prior production and canary-contract history. Requested Astra/medium is not runtime attestation. This is not human, external or absolutely blind review.

All 96 indexed RAW inputs were independently checked before and after content review; all match their frozen SHA256. The index SHA256 is fe2748b0a5c9681d181e266db5b9fe45ccb5c35992fae7c987a47fa4b8557da3. All 34,429 baseline rows were also individually rehashed and match. Historical metadata transitions are not described as unchanged live historical inputs; this review binds the current 96-row set.

The complete Test file, seven-definition context, eight full propositions, three private helpers, full public-value probe and retained compiler/metadata failures were read. Prior production BODY acceptance is reused only at its exact production hash; no new production acceptance is inferred. Both pinned PDF23/24 original PNGs were personally viewed at original detail in this review. Source p11 uses strict-past cumulative minimization; p12 allows any admissible first action. The fixtures are derived audits, not additional printed source results.

## Tests.OnlineFTLSelector.quadratic_trajectory

Actual h0/h1/h2 use predict_zero and quadratic_selection. The latter proves attained minimum and uniqueness by completing the square, then invokes select_eq_some_of_unique. The final forall over range 3 uses predict_some_spec for each actual result. No desired trajectory premise.

- objects: Fixed real interval and two distinct quadratic losses
- quantifiers: Seven conjuncts, final forall t in range3 exists actual p
- assumptions: No external minimum assumptions
- conclusion: 3/4,1/4,1/2 and genuine prefix minima
- indices: 0 empty,1 first loss,2 two losses; minimum sum at half=1/8
- information: Strict past
- source_delta: Nonconstant source-admissible example; not all-time regret

## Tests.OnlineFTLSelector.current_future_independence

Concrete current/future differences are established and predict_prefix is applied to equality on the strict prefix s<2. It does not assert equality of all later predictions.

- objects: Same interval/initial and changed stream
- quantifiers: Three closed conjuncts
- assumptions: No external hypotheses
- conclusion: Current2/future3 losses differ at0 while predict2 equal
- indices: 9/16 versus100; indices0,1 unchanged
- information: Current/future excluded
- source_delta: Only time2 equality, not future trajectories

## Tests.OnlineFTLSelector.off_domain_invariance

The conditional extension agrees on the feasible interval at every time and differs at spatial point 2. Both actual chosen selector equality and predict equality follow from select_congr/predict_prefix, not merely objective-value equality.

- objects: Same selector and two ambient extensions
- quantifiers: Five conjuncts including forall t EqOn
- assumptions: No global function equality
- conclusion: Outside2 differs; both select and predict equal
- indices: 49/16 versus9 at time0,input2
- information: Feasible-domain EqOn only
- source_delta: Actual choice equality, not arbitrary policy invariance

## Tests.OnlineFTLSelector.tied_minimizers

Both endpoints are proved feasible minimizers of the constant objective. selection_witness obtains the actual selected feasible minimizer without identifying it with either endpoint.

- objects: Zero one-loss interval objective
- quantifiers: Six conjuncts ending exists chosen p
- assumptions: No uniqueness
- conclusion: Distinct endpoints both minimize; actual some feasible minimum
- indices: History1 not empty
- information: Static actual selector
- source_delta: No specified tie-break endpoint

## Tests.OnlineFTLSelector.empty_domain

select_none_iff reduces to the impossibility of a point in the empty domain. This does not construct an initialized predictor on an empty subtype.

- objects: Empty real domain and square loss
- quantifiers: Closed Option equality
- assumptions: None
- conclusion: select empty=none
- indices: History1
- information: No prediction initial fabricated
- source_delta: Ambient square minimum does not supply empty membership

## Tests.OnlineFTLSelector.empty_history_and_initialization

An empty sum has every feasible point as minimizer; selection_witness obtains some selected point. Two predict_zero applications retain the distinct supplied initial points without equating them to the empty-history selector.

- objects: Nonempty interval, Fin0 history and two initials
- quantifiers: Four conjuncts
- assumptions: Subtype feasibility built in
- conclusion: Empty select succeeds; predictions0 differ
- indices: Empty history distinct empty domain
- information: No loss read at zero
- source_delta: Does not identify selected empty minimizer with either initial

## Tests.OnlineFTLSelector.affine_nonattainment

The full real line is nonempty, closed and convex, but the identity loss has no attained minimum: any proposed p is defeated by p-1. The actual selector and positive-time predictor are none, whereas the supplied initial point remains playable at time zero.

- objects: Nonempty closed convex full real line, affine identity
- quantifiers: Six conjuncts
- assumptions: Geometry proved, not assumed sufficient
- conclusion: Actual nonattainment; predict0some0/predict1none
- indices: At1 objective x
- information: Direct prefix
- source_delta: No compactness/attainment implication or timeout

## Tests.OnlineFTLSelector.recovery_after_nonattainment

The first prefix is the nonattaining identity objective. The second prefix is exactly x squared and quadratic_selection proves the actual result some 0. This establishes separately recomputed prefix queries, not a valid full interaction through the failed first prediction.

- objects: Full real line, loss0=x and loss1=x²-x
- quantifiers: Four conjuncts including forall x sum identity
- assumptions: No supplied desired minimum
- conclusion: none at1, some0 at2, actual minimum and sum=x²
- indices: Two losses0,1
- information: Recomputes prefix, not absorbing recursion
- source_delta: Example of recovery only; not general recovery guarantee

## Private helpers and compiled evidence

selection_witness uses actual Option cases and select_none_iff/select_some_spec. quadratic_selection establishes the quadratic minimum and uniqueness before applying select_eq_some_of_unique; positivity of the coefficient is used. affine_no_minimum compares p with p-1. All three are accepted within this Test scope.

The focused Lake build exited 0 (3286 jobs). The actual generic probe supplies eight complete proposition witnesses and eight standard-only axiom outputs. All eight frozen normalized headers match their fences, and all eight safe-verify command receipts exit 0. Safe verification is not itself a compilation or source-semantic proof.

The compiled selection contains 24 value-bearing nodes: 13 production declarations, eight public Tests and three private Test helpers. It is a selected graph, not a complete transitive graph, registry or source-result count. Eleven separately selected conjunction branches retain the required production values, directly or through actual referenced private-helper VALUE expansion. The extractor substitutes top-level lets, strips metadata/id and follows And.intro; expansion was checked against actual helper graph dependencies. Syntactic dependency presence does not establish proof necessity or exclusivity.

Preserved failures include Option branch equality orientation, positive multiplication/API and cumulative function simplification errors, then successful repairs without changing frozen statements. The fence driver initially read the wrong bookkeeping key after a successful fence; the missing durable outer failure receipt remains disclosed. No Lean failure is invented for that parser issue. Warning cleanup is not warning suppression.

## Recovery and permission boundary

At time 1, none supplies no playable action. At time 2, some 0 is the result of independently recomputing the supplied longer loss prefix. No valid complete online interaction continuing after failure is constructed. Future reader material must state this explicitly.

Only preparation of an exact scoped integration/publication plan is permitted next. Applying root/Test-root imports, reader/registry changes, native acceptance, Git/site operations or FINAL/package/chapter acceptance requires subsequent review and gates. All eight Chapter2 forward containers remain required/open; Chapter2 remains partial with unknown proof total and the whole Goal remains ACTIVE.

Required blocking repairs: none. The explicit recovery qualification above is mandatory for future reader material.

## RAW bindings

- E:/ABRL/worktrees/research-online-book/.agents/skills/bandit-semantic-roundtrip/SKILL.md — before/after 7ee7b72b8a84ab954966dc13900952c3439bd8d4e97877b622c1ca0a7aa85477
- E:/ABRL/worktrees/research-online-book/AGENTS.md — before/after 5642da8728315c0682c9853cbce4f087b2a7a24c9e46397ae7457db67f9c1995
- E:/ABRL/worktrees/research-online-book/BanditRLProof/OnlineFTLSelector.lean — before/after cd1cae5683edaa40fde18466f1efbca8ad34b295d8dfc3b173a35e0d459405df
- E:/ABRL/worktrees/research-online-book/docs/contracts/online-ch2-reconciliation-v1/generic-ftl-v1/canary-v2/contract-v2.md — before/after 155528852d029658f7aa453bfe651686f8a9d28e587b53b7ffe40604ecad7a7e
- E:/ABRL/worktrees/research-online-book/docs/contracts/online-ch2-reconciliation-v1/generic-ftl-v1/canary-v2/definition-context-v2.lean.txt — before/after e9eb14df49f2ccf9fcf1cf3a629309329a38f5831ced1a581b439e27571b7bcc
- E:/ABRL/worktrees/research-online-book/docs/contracts/online-ch2-reconciliation-v1/generic-ftl-v1/canary-v2/frozen-headers-draft-v2.json — before/after e8b4bca59a56fbbf2b9983f2d6bf78fe4aa61e32bb1cbb2f09495a0a2eb5bdf9
- E:/ABRL/worktrees/research-online-book/docs/contracts/online-ch2-reconciliation-v1/generic-ftl-v1/canary-v2/stabilized-v2.json — before/after d0ed89246539cfb9519939295cdc97d35c67b2cd38f5eae924d2be8a65b44356
- E:/ABRL/worktrees/research-online-book/docs/contracts/online-ch2-reconciliation-v1/generic-ftl-v1/contract-v1.md — before/after 9dea7a69a3f6ae834b5272e8e3c82c829f59451a2650d9bd54bdc799bbc6c073
- E:/ABRL/worktrees/research-online-book/docs/contracts/online-ch2-reconciliation-v1/generic-ftl-v1/DAG-draft-v1.json — before/after 7b72a969dd4ff8cc516e647824cee3188d03d0ee5bd6ae904ceddd4a4371d179
- E:/ABRL/worktrees/research-online-book/docs/contracts/online-ch2-reconciliation-v1/generic-ftl-v1/definition-context-v1.lean.txt — before/after 112847a69636cd98ea1413861fa77dd5d315493f8c591893b4166080674c6db2
- E:/ABRL/worktrees/research-online-book/docs/contracts/online-ch2-reconciliation-v1/generic-ftl-v1/frozen-headers-draft-v1.json — before/after e61a4c49306039e461ad3d02b5a0fc5c39c1af6a1445c5297aa1045dada992a2
- E:/ABRL/worktrees/research-online-book/docs/contracts/online-ch2-reconciliation-v1/generic-ftl-v1/source-card-v1.md — before/after 9b5379789c43489a452db4c9fb6c7fb48ef2ab4797f836bc406affdd789cb298
- E:/ABRL/worktrees/research-online-book/docs/contracts/online-ch2-reconciliation-v1/generic-ftl-v1/stabilized-v1.json — before/after c0e11537af5a29141a8081f45372b393d81d3f26eb1e86a18cf7814dd0aac67a
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-chapter-audit-20261009/source-pdf23-text-v1.txt — before/after 9ad74e9690f425ec817151daa7c9fe63fce7fb78a4da828eb1306ef45f531099
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-chapter-audit-20261009/source-pdf23-v1.png — before/after bca6458493037bf26fb8dec0071d48d7e1bf72d1a91ccb6bb6d6243636e1d23b
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-chapter-audit-20261009/source-pdf24-text-v1.txt — before/after d8ebf890a1864ea175361736b1e2ac258bc10867fb3df8c06aeae3ecd28aaca1
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-chapter-audit-20261009/source-pdf24-v1.png — before/after debdd125caa329788deedad0f3d5d91d77535e22c365f914c8f704958e8d2828
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/31_worker-ftl-canary-BODY-v1.md — before/after 2c267b0f633a70f7302da2beac9990824bf74055ef1e283177939f4a0df38141
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/AuditFTLConjunctValuesV1.lean — before/after aa9ee61608ec4067acb5bd98d0980d20d01b93d0f7ba3afc2707856c658acfb6
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/common.py — before/after 0586bafd475a37c319474569f60edb2f9a6eb781ea0cabe6e72a132d08abf8ce
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/ExportFTLCanaryValuesV1.lean — before/after 91280d900f39b4b53e8df2c90885e64a3d0ff1150818d8236ee4e11fdaffec19
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/fences/canary-1-v1.json — before/after 9462950b72080236824b89b19b198b5fab69dfaa24d2120d375db06239035cc9
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/fences/canary-2-v1.json — before/after 4bf13ae140ed4024af71d94d3d9801154348f56ca9d497c82186705deebfd96c
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/fences/canary-3-v1.json — before/after 0b12640fcad2673d5b5293f29e08858755bfaae1188b072a3b59c6b99ac6ef63
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/fences/canary-4-v1.json — before/after 39dea0fe164e894bb15a74b83a4bf0e708174d4707ac49e623eac89cc1025707
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/fences/canary-5-v1.json — before/after 8445a1cf0f2b4c05e048b6d623c3c0d5ea084730f3dd99c283b36fd77e0b35ad
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/fences/canary-6-v1.json — before/after d77ed97aa4ea6c288f7b5b87d06f05961baa7410746c7a58ea7f468aa07e7eaf
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/fences/canary-7-v1.json — before/after 5e27af9633e8e7083908bf635bf83ad0eba3e0db44b6c3dccdef9bf1b52c27e4
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/fences/canary-8-v1.json — before/after 6dd2bc97d3d97df041176a099390b7b309f5f32259da720b82ae3c30d8f20a89
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/ftl-canary-boundary-leaves-BODY-v1-binding.json — before/after 84e323dcee674642b39a3abaa1872b13162682c12e4ba084d70ae88eee29039b
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/ftl-canary-boundary-leaves-BODY-v1.json — before/after c4d7c78134cc81d15e350351fdc114a0b3ca634a0e0daa69276f009fa05954ef
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/ftl-canary-boundary-leaves-BODY-v2-binding.json — before/after ce4f83bf17b971ebdeabf5a4192988950e36fd889f9dd01003eba6d2a0f11405
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/ftl-canary-boundary-leaves-BODY-v2.json — before/after 852a2c128bd1f195b52fd59e854c53a3966cf5aebe139f67b46d2483996091a5
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/ftl-canary-candidate-v1.json — before/after 862fd853bf2fe62b85594f5c3a759abc0ac545e8d8b53b38d79f07e0a70d8762
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/ftl-canary-case-repair-v2.json — before/after 41c91f11089b1a2647bd4cb7a4ac873f8c55b88acba5aa3b59785dafdf143548
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/ftl-canary-context-repair-event-v2.json — before/after dfd01bc551dac5d3fb70d0c0a9d8670a5374abf4195ba0f16e1edd61ae93dc45
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/ftl-canary-context-repair-v2.json — before/after c3b765614817dbd987b42e7f818d97983e40b1b5c9ac76409de0bf4b02b68417
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/ftl-canary-eight-complete-BODY-v1-binding.json — before/after a82b9548f50918d0d74e37689d53ecc7ae64c783aea1e87caee8186d6b26f15c
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/ftl-canary-eight-complete-BODY-v1.json — before/after 4c71ff73a92c7fa02d9d4b4ad7957abe8aebee4ef54d6ee42cd534bef95b2f1e
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/ftl-canary-empty-domain-BODY-v1-binding.json — before/after 59711469ffce2933f8f3877dcab588a80e16d124b6624615df430d732b8b4d44
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/ftl-canary-empty-domain-BODY-v1.json — before/after 19294e4eff708e02faa204f8a12f3c374d36b86897b522f7e43cd45e972b7177
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/ftl-canary-evidence-preparation-v1.json — before/after eaa7e2d34dc32aabb70b55335be4303da96620c83e008670d42e109cae97f0f3
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/ftl-canary-fence-1-v1.json — before/after 8a29a80a9f4bdfe1be622d8e124ce106eb458318d351c73b9623df36fc051600
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/ftl-canary-fence-2-v1.json — before/after 4a15e938a6257fcd4eee3ffd16f1566d41292b50e37a6209a4204ee0012a2039
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/ftl-canary-fence-3-v1.json — before/after 8ed48083a4189d6d666434f97861b20a560996f4c0ce17a9a6bcb44b12efc7e3
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/ftl-canary-fence-4-v1.json — before/after 2f0092e8f0a166e8c1d8a4b6eb669c03be5a579c18638c250d2a301656ae2b2b
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/ftl-canary-fence-5-v1.json — before/after 19d93711504f614a79216f491178be824f2622e43f82d11b791ae86fbb63d74e
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/ftl-canary-fence-6-v1.json — before/after ae55277ec70f6fe27572f072811b3ee4563b202308d793aaff6e38ed2f72ed10
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/ftl-canary-fence-7-v1.json — before/after 6dee2de638f5576bae0736766f86ec576104ecc76dc0856d95052b1131ff0b57
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/ftl-canary-fence-8-v1.json — before/after 4ac633fe930fa8f67075a4f51aefd3e270c459a109c43f660d5dbf17fc1c10bc
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/ftl-canary-fence-driver-schema-repair-v2.json — before/after 81edbda38e7a5ce9dc14879505d9e7aa9ec170ddb3ae3c3bf854a40089b04780
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/ftl-canary-fence-driver-v2.json — before/after 82e9fa1dfaa822c1fb29e76f63c360892a67b4b099d996bbf24b845295891e90
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/ftl-canary-full-public-values-inspected-v1.json — before/after 3ff7a08edd1efcf2d7a1f7587b2a027ee55bb6d76d1f7ba224b7f000993b9a8a
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/ftl-canary-lake-build-v1.json — before/after 1b3adfdaca6ac8eaa5c7f3c41d2a907c7af20a0db1740dac5dd3a3dedeb1fe01
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/ftl-canary-nonattainment-recovery-BODY-v1-binding.json — before/after 6299bcfead740c237ff773fb2e7b08265df935938412f714549cb21ec26e5471
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/ftl-canary-nonattainment-recovery-BODY-v1.json — before/after fedffda49156b6df94025cd461bfc811027e99abdb293b604062fd9ae0368517
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/ftl-canary-nonattainment-recovery-BODY-v2-binding.json — before/after a9e959457e90ce164b1e212827fe8e9d54fc99047c6f04a178c2961476414e41
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/ftl-canary-nonattainment-recovery-BODY-v2.json — before/after fc6eb652883edf6e6e6aa2660c0cbfa01aa593ca1580a0abc79bb97695b83289
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/ftl-canary-nonattainment-repair-v2.json — before/after 1f486e9f6cdb803c3bdc9debc9fe8f10fbc8bb451046e52eea0a6935e439745c
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/ftl-canary-proving-event-v2.json — before/after 328d395ed6c0835af3412bf50c73354a860e3ed47fe9768a728a478c9f63d368
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/ftl-canary-public-and-axioms-v1.json — before/after a434589e419d4e6b1c9522f531390199248f30eb3490511ccc8cd200be1bd5dd
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/ftl-canary-safe-verify-1-v1.json — before/after ae38d37730186d7763ddf927b3663196426d1b3db39ac5e368a424c2588f4cfb
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/ftl-canary-safe-verify-2-v1.json — before/after ba703a4dcebb3e8a8b97239029f1e07fd546f0180bb8c373ac147eb59f7dd0ab
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/ftl-canary-safe-verify-3-v1.json — before/after 97fd98e6f9514fdd1ff669527e01d124717c3a75b2950ed1c2938d76b4e76cef
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/ftl-canary-safe-verify-4-v1.json — before/after b49ce17abb44d62f9d5712c30ff77cd073aa324c8b4970b39ca52a59f8725b08
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/ftl-canary-safe-verify-5-v1.json — before/after dd282723e9b5f01069456051b0be3c621757212336b5a3821bbc3cd25651cdbb
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/ftl-canary-safe-verify-6-v1.json — before/after f23ce87007d9734442930200630fe384390867073e0bc045720f1791e166ec36
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/ftl-canary-safe-verify-7-v1.json — before/after 06a82ecaf96c1890ff15227bc4b744dd10920ae278ae06116bfacffe5245776d
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/ftl-canary-safe-verify-8-v1.json — before/after a1c2c9262e62d694e780d4147fd4bc143a6ca13697c35fe243ce0ab36706d8b7
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/ftl-canary-selected-conjunct-values-v1.json — before/after 96327b81c4a28db6711e7e338c8355dc85fc05e143bd23dac18a568f095a5665
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/ftl-canary-selected-conjuncts-v1.json — before/after 1b28351e646dff1e9b7f07eab99e3a1c4a80907f0bdcbfa19f66689bb4227b27
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/ftl-canary-selected-value-graph-v1.json — before/after 63fbb9fb6e49ddd94c48cc590f1fd60faefb7002e742a3efafaebbe24c01b67b
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/ftl-canary-selected-values-v1.json — before/after 6b01e6e16a8adaaae6647fc6088f56727f86cb4eaeb0b183144b0917c768d6cb
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/ftl-canary-stabilized-event-v2.json — before/after 9b765240924ca37c39230499659fcfe95aa1e709543ed9fb2d80aee03abda275
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/ftl-canary-warning-cleanup-v3.json — before/after 1af8c67284e05556deff28e3a861d8d08191aa513d9825fd427b3831351e7421
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/ftl-eight-BODY-compiler-inspected-v1.json — before/after a289d1accb3123fc02f1f410f52635f94a4191141f1414df44e30fcdd4c9a407
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/ftl-eight-canary-fences-inspected-v1.json — before/after 14ac68b1055aa9aaa9d62404a389f8f002534b182200f50829d83e3ab855da6d
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/ftl_canary_proof.py — before/after b30751f3b34fece3a4f3cbc0ac7b3ad76cf4a54b19906bcc6aaedc7f9563e270
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/FTLCanaryPublicProbeV1.lean — before/after 4efd9f8a94f07f9fed700373abf68a1ef1c5de933fc646d68175659a4d1d8253
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/generic_ftl_proof.py — before/after d351c2e6276bd5e0002cf0a0ee9faeb729f9c847899134d70bbea4aadc8b42bc
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/neutral-finite-selector-canary-reconstruction-v2.json — before/after e1fd928df8ac5a4722c0aee7b8fac1068028cd7fb1ac0630ac0e9a81ea1d1427
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/neutral-finite-selector-canary-reconstruction-v2.md — before/after 67e319db91affe7faeb62aee6730919f98f965b03ce5ea58da944d934f04e12b
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/neutral-finite-selector-canary-type-probe-v2.json — before/after 1ae264e6629ccd78bb45d151f66ba573e9cfb0af5b02528605b269fb5ebb3b2a
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/NeutralFiniteSelectorCanaryPacketV2.lean — before/after 2981cec41d6e3eaaf917133f22b471e0faa8e9616b3370879a85275b3c508b18
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/production-BODY-canary-CONTRACT-repair-review-v1.json — before/after afa64f1675165d8034eaec08221d678ec3f11e08106c7242627b3c3f409dddb6
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/production-BODY-canary-CONTRACT-repair-review-v1.md — before/after 7685a0c53c335555feaf5fb33d01f20880f81b8efc3c1970843e88527302b268
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/proof-obligations-generic-ftl-v3.json — before/after 85f1d349e78fd9e29c6866df3f27c564b6af45774c0f7dba72e87241cd0c4af4
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/retrieval-index-generic-ftl-v3.md — before/after 63c2bd420566cf10d8151da122fb44bfa820320633b7ac387a120c3a8d832a95
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/snapshots/ftl-canary-boundary-leaves-BODY-v1.lean.raw — before/after ebef6c85070ebf932877d5aa266d28c36cc7d176d39bb7860b4fb103043fda00
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/snapshots/ftl-canary-boundary-leaves-BODY-v2.lean.raw — before/after cc83f12f314112e281c2c26b9bab91eddbce9bd5a6c95844030cfe241113f03b
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/snapshots/ftl-canary-eight-complete-BODY-v1.lean.raw — before/after a6e3b16b29c6a5eddcb343cb555457eb52bed35c9c5089a1948e90f30cb1df85
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/snapshots/ftl-canary-empty-domain-BODY-v1.lean.raw — before/after 14aab324198f81591ae33a729cd6873701fa4ffbc3354f473f104d7f64b6a6c9
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/snapshots/ftl-canary-nonattainment-recovery-BODY-v1.lean.raw — before/after 7e9eeaedf75ffa79ae0e898ff33cfab857511b3da8add3d240e149d3187f6447
- E:/ABRL/worktrees/research-online-book/runs/online-ch2-reconciliation-20261010/snapshots/ftl-canary-nonattainment-recovery-BODY-v2.lean.raw — before/after ed996853d56f0957b70f5d2522fd0d6ad6ce096b621babcdd441b3a96111abc9
- E:/ABRL/worktrees/research-online-book/Tests/OnlineFTLSelectorCanary.lean — before/after a6e3b16b29c6a5eddcb343cb555457eb52bed35c9c5089a1948e90f30cb1df85
- E:/ABRL/worktrees/research-online-ogd/tmp/pdfs/orabona-v10.pdf — before/after cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17
