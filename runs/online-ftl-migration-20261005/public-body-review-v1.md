# FTL migration: actual public body and canary review v1

Verdict: **accepted-with-explicit-delta**, limited to the retained seven actual proof bodies, three definitions and two actual canaries. This is a new body judgment, not retroactive reliance on historical acceptance. Current reader prose and package acceptance are excluded.

Actor `/root/source_reviewer`, distinct automated source reviewer; requested GPT-6 Astra / medium, runtime identity not independently attested; no human or external-model review claim.

## Read and verification scope

All 158 frozen input rows were independently read as raw bytes and hashed: no drift. This receipt adds the fixed inventory itself, for 159 rows. All 93 prior source-contract receipt rows also remain exact. Close semantic inspection covers the full public module and canary bodies, frozen statements/context, source and neutral reconstruction reviewed in this same sequence, actual elaboration/axiom/guard/trial logs and exits, and reused graph structure/retrieval implementation. Ancillary historical input rows are raw-bound provenance, not independently recertified scientific judgments.

Pinned original Orabona v10 PDF digest remains `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17`; freshly extracted physical24/printed12 was read in the preceding source-contract pass. Example2.10 specifies the alternating scalar loss family, arbitrary feasible initial prediction, exact regret against zero and linear lower bound. This body review preserves that source comparison and challenges whether the actual proofs produce it.

## Seven semantic slots

1. **Objects/spaces:** Scalar real linear losses on the actual closed interval [−1,1], recursive coefficient prefix and concrete sign-based FTL output. No surrogate assumed loss bound or abstract minimization oracle replaces these definitions.
2. **Quantifiers/order:** Generic helper streams are arbitrary. The fixed source witness works for every feasible x0 and every natural T>0. The strict-prefix comparison fixes common x0; it does not constrain a hypothetical external future-dependent initialization procedure.
3. **Assumptions:** Generic historical minimization assumes feasible comparator only; at t=0 both objectives vanish. Its feasibility is separate. Actual source terminal restores feasible x0. Positive-time parity helpers require t>0. No extra convexity, differentiability, distribution or boundedness of generic coefficient streams is inserted.
4. **Conclusion/metric:** Proof constructs historical minimization and then separately actual played cumulative losses. Terminal proves both exact comparator-zero regret and its lower bound; zero is not asserted to be a hindsight minimizer.
5. **Constants/index:** Lean0=source round1. Initial loss is −x0/2; each later played loss is exactly1. Sum is T−1−x0/2 and bound T−3/2, not an asymptotic replacement. Source endpoint excludes T=0; T=1 is valid even with negative regret.
6. **Feedback/probability:** Prediction uses only coefficients i<t. Equality with the current coefficient on the specially chosen witness follows arithmetically, not from reading current feedback. Entirely deterministic; no randomized-law or universal all-algorithm lower bound.
7. **Boundaries/attribution:** Positive-time zero-prefix ties select −1. This is one legal generic selection; the source witness has no later ties, so the source failure is unaffected. Six helper theorems and three definitions are refinements, not separately printed source results. Zero new proofs are claimed in this retained-code migration.

## Per-target proof audit

| Target | Actual producer and challenge | Body verdict |
|---|---|---|
| prefixCoefficient_eq_sum | Natural induction unfolds the recursion and sum_range_succ; exact zero case, no premise asserting the sum identity | Accepted |
| linearFTLPredict_prefix | Rewrites both recursive prefixes as sums, applies pointwise equality only on range t, then uses equality in the actual branch selector | Accepted with fixed-initial-input scope |
| linearFTLPredict_mem | Splits the actual definition; x0 membership handles initial branch, exact endpoints handle later branches | Accepted |
| linearFTLPredict_minimizes | Factors each historical objective into prefix times one action. Empty-prefix branch is zero; negative prefix reverses u≤1, nonnegative prefix preserves −1≤u. No regret or minimizer premise | Accepted with separate initial feasibility |
| failure_prefixCoefficient | Induction handles first exceptional coefficient, then mod2 parity and actual recurrence produce alternating half-unit sums | Accepted for positive time |
| failure_prediction | Unfolds actual selector, rules out time0, substitutes proved nonzero half-unit prefix, evaluates its sign | Accepted for positive time |
| example_2_10 | Proves actual later played loss=1 from actual prediction; inducts on n+1 to retain first loss −x0/2; substitutes every positive T=n+1; derives bound from x0≤1 | Accepted with exact source scope |

There is no circular premise or consumer of the desired terminal inequality. The terminal depends on the actual prediction producer. It does not need to consume the minimization theorem in its proof term: the separate minimization theorem establishes that the very same concrete selector is FTL. A teaching explanation can combine these facts, but must not fabricate a direct proof-term dependency from the terminal to minimization or causality.

## Canary audit

`Tests.OnlineFTLFailure.actual_predictions` directly unfolds the three definitions with norm_num and proves outputs 1/3,1,−1. It independently exercises the exceptional initial branch and the first two alternating signs, without merely restating a desired regression outcome as an assumption.

`Tests.OnlineFTLFailure.six_rounds` legitimately instantiates the actual proved source terminal with feasible x0=1/3,T=6 and simplifies the zero comparator to obtain 29/6. This is an integration test of that producer, not an independent proof of six losses by enumeration. Together the two tests are nondegenerate. Neither test exhaustively covers arbitrary tie streams, T=1 or all feasible initial points; those remain quantified proof statements, not additional tested cases claimed here. Both canaries accepted in their actual scope.

## Actual evidence and its limits

Actual direct module elaboration and direct canary elaboration exit0 are present. Focused Lake build completes successfully at 9087 jobs, including replayed dependencies; it is not a fresh combined Tests/full-harness acceptance. Twelve actual named #check/#print axiom records (three definitions, seven theorems, two tests) were parsed and all use only propext, Classical.choice, Quot.sound. No sorryAx is in these accepted records. I inspected evidence rather than rerunning Lean in this review.

Seven frozen normalized public headers were independently re-extracted and matched. Seven actual safe-public records report matching hashes, preserved premise substrings, empty findings and exit0, with fences pointing to the actual public module and scans of module/canary. These are header/placeholder guards, distinct from kernel elaboration evidence.

The full shared compiled graph is reused, not newly exported for this package. I independently tested its six claimed required value occurrences: prefix→sum identity; minimizes→sum identity; prediction→failure prefix; terminal→prediction; failure prefix→recursive prefix; terminal→actual selector. All exist as value or also_in_value edges. Ten FTL nodes concern retained unchanged public bytes; this does not certify a newly exported canary graph or package-wide dependency gate.

The first native trial failed on role lower-worker, the second on status passed; successful third uses lower/compiled and remains reviewer_validated=false. These are preserved administrative enum errors, not Lean proof failures. This review makes no native-trial mutation.

## Required reader repairs and remaining gates

No proof or frozen statement repair is required. Before final reader/package acceptance:

- Correct the prefix highlight to equality of predictions under strict-prefix equality; do not substitute the historical minimization inequality.
- Qualify the minimization highlight: the displayed inequality alone does not assert feasible argmin at time0 for arbitrary x0. Combine with initial feasibility/membership to call the algorithm output an argmin.
- Keep structural/helper attribution separate from the printed Example2.10, and actual graph dependencies separate from curated teaching links.

Those reader issues are known pending repairs recorded by this packet, not newly certified current website content. Fresh root, Tests, full harness, final source-reader/shared registry/site, applicable contributor gate, immutable binding and separate package/PR decision remain required. No Chapter2/book/Goal/main/live completion is certified.

## Exact raw bindings

All rows are actual raw-byte SHA-256, without normalization.

| Path | Raw SHA-256 |
|---|---|
| `../research-online-ogd/tmp/pdfs/orabona-v10.pdf` | `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17` |
| `.agents/skills/bandit-semantic-roundtrip/SKILL.md` | `7ee7b72b8a84ab954966dc13900952c3439bd8d4e97877b622c1ca0a7aa85477` |
| `BanditRLProof.lean` | `d16d741b3bca1b4f7c30fbad7a2b5b3e8283d079cf49695720f4b256fb3b5bfb` |
| `BanditRLProof/OnlineFTLFailure.lean` | `6e8a2d00f2d8c2bd342208f8495f8257df2d074d5ca52efadba014cbc662c984` |
| `BanditRLProof/OnlineLearningFTL.lean` | `8aee4c971fffbc79f2426fb308f50ec02b664b42a90fe1f85620a313df4c7a06` |
| `BanditRLProof/OnlineLearningFoundations.lean` | `e23ebdca2f7ce21a16173c93390fd24d16ba36e403c9d084233f7480e75408b8` |
| `BanditRLProof/OnlineLearningMean.lean` | `d65b3e5d5d2e33a0fd94722f1d7d9a09819c963c693e28bf854fae00f5280aa1` |
| `BanditRLProof/OnlineLearningRegret.lean` | `231eda88cb1c45bf3bc9209bfbdd696fbfbe8a64b00303113a23cbc4dff3ca5b` |
| `Tests.lean` | `693654a3126313f0e7db548ff08f6ee961e8b7656602fb56dc590a1cdbe0a825` |
| `Tests/OnlineFTLFailureCanary.lean` | `b928a253c241c10962a14ec1e07ac842cab45bd4bf11ec97b22f9d01c7f3b783` |
| `conversion-windows/ONLINE-FTL-MIGRATION-20261005.md` | `9e77e1afb74bbc00310670fae6faa9b3ee46fdc2bd35b93031a70e133562c6d4` |
| `docs/contracts/online-book-v1/coverage.json` | `fd7580c2d0ec040352317d3c53dc583a6b9b75a68b4026ebf3b38f7010a98f1e` |
| `docs/contracts/online-book-v1/source-inventory.json` | `a2a504cf40d73f9c5e36f00fc1ef3b949ccaf5a558ab603c1c2a86007f30efa7` |
| `docs/contracts/online-ftl-migration-v1/context.lean.txt` | `c79a87fb372d3df1c763733e89f09460d98217002964b10b0510a7c0b919c33a` |
| `docs/contracts/online-ftl-migration-v1/example_2_10-header.txt` | `ebfbe805a0af1ff9596ef3b11129800adf3c1a7feb0c5422d68ef33c0aadf780` |
| `docs/contracts/online-ftl-migration-v1/example_2_10.json` | `8528cdb1c011c46d4ab99c1d08b1139641452559f9b46279e2ce98f661a5744f` |
| `docs/contracts/online-ftl-migration-v1/failure_prediction-header.txt` | `a0140f69ef2d8a442baba1515ae79a5e2d1bf50ee202d2d6d65d4ed3228a2a52` |
| `docs/contracts/online-ftl-migration-v1/failure_prediction.json` | `80cd647c3fba3f9350c13acee068192b0c6329779703fcac21ec64de2e2527b4` |
| `docs/contracts/online-ftl-migration-v1/failure_prefixCoefficient-header.txt` | `18db4f0d22114e7d31561d0a166975507a92aa86b71b8ecb53dd7aaaf43c9b78` |
| `docs/contracts/online-ftl-migration-v1/failure_prefixCoefficient.json` | `fa3b03955791e598b6eab117c301710a7e1c17b4b68fcfb3d97b022600d89ec2` |
| `docs/contracts/online-ftl-migration-v1/linearFTLPredict_mem-header.txt` | `0ad64fe6705a215b72d63268c4ffed14b7046d7ec0afd1da99501bc36214bfb9` |
| `docs/contracts/online-ftl-migration-v1/linearFTLPredict_mem.json` | `4b36ce6c35b397e07123e7708593968b5ea6e36b9a2a125fcd8c6e3bd8873c3f` |
| `docs/contracts/online-ftl-migration-v1/linearFTLPredict_minimizes-header.txt` | `25d2e9e8ad532891418b3208378fbf5e07a11547eb948d00c4b562bf279806b2` |
| `docs/contracts/online-ftl-migration-v1/linearFTLPredict_minimizes.json` | `aa2d90ecb224e05c15989f2d84c426520201035631a27821bae5f93adb620da3` |
| `docs/contracts/online-ftl-migration-v1/linearFTLPredict_prefix-header.txt` | `80f8d35ee9da71211024b311d9abdadd239a94329599b4cc27dc20108b6d65c4` |
| `docs/contracts/online-ftl-migration-v1/linearFTLPredict_prefix.json` | `0093689e272bf8f97ad8e66f5fdd6f79c5183767842552ad015734ffbd15d327` |
| `docs/contracts/online-ftl-migration-v1/prefixCoefficient_eq_sum-header.txt` | `7a4beb1c9281f80b1f4b6a48f5247d364a42c3b6b4752c1c0c6878b73aa1e9ad` |
| `docs/contracts/online-ftl-migration-v1/prefixCoefficient_eq_sum.json` | `042060dc36c81b9f1b6a4ecfc47fb2df21d791645acc0e24857cc9390b277776` |
| `docs/contracts/online-ftl-migration-v1/source-intent.md` | `ae383dd2e505be3b6121907f6b6d4ccf538d0dba9f445fa7ef32fb42be10eff1` |
| `docs/hierarchical_harness.md` | `6027004b33e316f5d47794ddbda01414ce6c811ba164163c7b2ece671b9468b7` |
| `docs/lifecycle_and_proof_frontier_hardening.md` | `335a861e00d13d59f88080ec54e6174722afc7534ad9e74f4261b4247f50165a` |
| `lakefile.lean` | `0164f3b5b5bdcbb237ab15ae8b44da83e183f4b97d5f3832aa4a57f27dc69d45` |
| `lean-toolchain` | `b15a57f8ea4c890197465ce1156667ae13d9ed4ab8a9f263a920bf010d967d82` |
| `proof-obligations/ONLINE-FTL-MIGRATION-20261005.md` | `4d9086d6f038eca802f0cd72d5b5c2d7be1be088636397bd6df47a67589a5e1a` |
| `runs/active_frontier.json` | `567e5873aa2549a83f2820d758069213808da822a93087129877385a1addf7c3` |
| `runs/online-ch2-enumeration-20261005/source-navigation-draft-v1.json` | `d048e0adc6aec11efc83b4aa50c870c57b72008371960f00f487e57e236f3fd0` |
| `runs/online-ftl-failure-20260914/acceptance-decision.md` | `d9c2be7c1b8bdabf129f67a52b69ba659500bb6af5bf73d8180dcd2f97ef62a4` |
| `runs/online-ftl-failure-20260914/source-audit.json` | `58875cb7de405d20fb37a1ca48a343c7cf72257af9c1389678a76050b3a50ccf` |
| `runs/online-ftl-migration-20261005/00_context.md` | `6f14bd1398b137aa0d6f198f603d31051c5c6938c9a01b30e1bb7f3f742cbbb1` |
| `runs/online-ftl-migration-20261005/10_upper_director-v1.md` | `73279669d8b45a274af3fbf4c3ffff12f0dfb0463e628990cb19b30ef2fa943c` |
| `runs/online-ftl-migration-20261005/20_architect-v1.md` | `7e2a2fdcf66b63eeb9d00809a02092bb0ac2af531916584a4bf04cb35471f19f` |
| `runs/online-ftl-migration-20261005/30_lower_worker-body-audit-v1.md` | `0fbf75ad71670a26abc8ad8a821e99f84141ed2d751b6a911d99f9ae26049c9e` |
| `runs/online-ftl-migration-20261005/actual-declaration-retrieval-exit.json` | `62a55fe1e41d77338dfe53a4b4d0ed9b4f7281f819fde4ae8e3b199f7733ec44` |
| `runs/online-ftl-migration-20261005/actual-declaration-retrieval.log` | `95db75e2a6d1cfb0632ab222e324bb96d04ae0e42aa9da61b33ad702c899b396` |
| `runs/online-ftl-migration-20261005/blind-packet-v1.md` | `60ba567cec00c4f2e93fd67069c4da01c338bc198ca80153237f5e80d5217708` |
| `runs/online-ftl-migration-20261005/blind-receipt-v1.json` | `928536f2240f2d632ee568071f38fe47a44a7b3ed7e520d6ae5db1b5122d967b` |
| `runs/online-ftl-migration-20261005/blind-reconstruction-v1.md` | `a9b97e423357edd5f7134e68149169a3423da28577edcd70810f17682fa3d9e8` |
| `runs/online-ftl-migration-20261005/chapter2-navigation-draft-01-exit.json` | `bcc37dad1aeacc7f80710cbd3b5ebff4d4d69feedc440ed1f98baab48a4e8b24` |
| `runs/online-ftl-migration-20261005/chapter2-navigation-draft-01.log` | `c86ed1f54309f2de77cb02cd94a4b2cc8322da00084c0c7816ab276dc5071a6a` |
| `runs/online-ftl-migration-20261005/contract-binding-audit-v1.json` | `b0fd9d890978345a9c325ebc609766582828fe2e8a088126839d9c8c6ce5692c` |
| `runs/online-ftl-migration-20261005/contract-source-inputs-v1.json` | `e20d698a338cd816b34c71caf4b327f7e91fa4c5fe5e3c5ff7fb72fc2b53ba34` |
| `runs/online-ftl-migration-20261005/draft-freeze-v1.json` | `60fa37190c4550edcbccaf4db72dc780a677ab48f71fc2c3286eb0c0818bf04a` |
| `runs/online-ftl-migration-20261005/draft-lifecycle-exit.json` | `32da2a68241961564fddbc250e4fa34161499427b9442160b07336b81c3c54cb` |
| `runs/online-ftl-migration-20261005/draft-lifecycle.log` | `6c4b2f1c6f56a8656bef4bfc2c18056b57d6074b3220ac284af756406e6928e1` |
| `runs/online-ftl-migration-20261005/failed-raw-snapshot-v1-01.lean.txt` | `e43322d81532b84897b69263410cefefbc98208829dc1f4b261e76ed0912d30d` |
| `runs/online-ftl-migration-20261005/fence-example_2_10-exit.json` | `957c48491465a62360a1c0e19638c094b0220127e9455baba5cd6bb3c72c2f13` |
| `runs/online-ftl-migration-20261005/fence-example_2_10.log` | `b7f79804702d12b47d0ab5e85abccb5a5ae440ca17d3b3d058fa610e6ac40cb9` |
| `runs/online-ftl-migration-20261005/fence-failure_prediction-exit.json` | `ca8512e2123e44752fb184ff0f584c8b5c0726090c0db722500009228306511b` |
| `runs/online-ftl-migration-20261005/fence-failure_prediction.log` | `3b4b99dc18031de73e20880aa43e18336fe07bc981db934b29a9a42292f31961` |
| `runs/online-ftl-migration-20261005/fence-failure_prefixCoefficient-exit.json` | `91aa322098cce0ea84cfe00a321976a5d762eed0b7fb9fecd5bc08da876fbef9` |
| `runs/online-ftl-migration-20261005/fence-failure_prefixCoefficient.log` | `a0d5b8b62802572a5a6610e12809a01f78e9df85b59b7527e8733188e93a4249` |
| `runs/online-ftl-migration-20261005/fence-linearFTLPredict_mem-exit.json` | `977252e92ed36ccb5f9710c802fac91f4dca4bc7c1a6208b69aa30d9830df44f` |
| `runs/online-ftl-migration-20261005/fence-linearFTLPredict_mem.log` | `d5df0e1fb94b461005002507f3508fec78eedc8b72caed3c9b51bbf03658f6a5` |
| `runs/online-ftl-migration-20261005/fence-linearFTLPredict_minimizes-exit.json` | `2c737c5b18e46cb0bb5f2f63fb02eabeac37a7fa7ee0c887d18e4066166ff63c` |
| `runs/online-ftl-migration-20261005/fence-linearFTLPredict_minimizes.log` | `a07d7d39ef493c052bb353a9e4f2880bb1a1d1e20eb39d7dd9efe8ec0b2cb0fb` |
| `runs/online-ftl-migration-20261005/fence-linearFTLPredict_prefix-exit.json` | `8f589542b6935db5bb3898906de1aa6ce3e581af17326747e18474d180b36151` |
| `runs/online-ftl-migration-20261005/fence-linearFTLPredict_prefix.log` | `ceb2965b472f72e27610feed8f694affd6dab3ddd1b05d104095a8b7aef6d5f1` |
| `runs/online-ftl-migration-20261005/fence-prefixCoefficient_eq_sum-exit.json` | `31636f682ced580c380250b0792ba717d8f605a7bd6b3b2b8210fb72c145aec3` |
| `runs/online-ftl-migration-20261005/fence-prefixCoefficient_eq_sum.log` | `3b7ad6e631e28c3e7fecdc5a9a6472a957e61d4fc7ce673c67dff2cdfbd4c50a` |
| `runs/online-ftl-migration-20261005/focused-build-v1-01-exit.json` | `2db2c872f7067505679e9c868dd8165719f78c1ce8c4307aa1ced36a0ec5160d` |
| `runs/online-ftl-migration-20261005/focused-build-v1-01.log` | `dbcf5f679dd64840e914173c834638ac86a94ab80f154161f35825e69cca74e1` |
| `runs/online-ftl-migration-20261005/help-new-task-exit.json` | `9630e1c62174673313ac4012b1f058b3ecb55ca55f0b2323d4c94a20a94674c9` |
| `runs/online-ftl-migration-20261005/help-new-task.log` | `25eb9342c3094bee57187630bd149d2c522fc9f7ac7e65bebe5c198eba60ed99` |
| `runs/online-ftl-migration-20261005/leaves/prepare-body-review-attempt01.py` | `41b3a78b53a8d6f7fffd52bbf90df90ec6714838d0f117b5a523ec14808fa772` |
| `runs/online-ftl-migration-20261005/leaves/prepare-body-review-attempt02.py` | `31b9b4abe599047106b223494fc83de053e4715d377bc7a60a4e3f5885eeafd3` |
| `runs/online-ftl-migration-20261005/leaves/public-axioms-v1.lean` | `b1969c03d237c4c25d0316f82f31e280f69a123aa88034669485c3e3352d4a4a` |
| `runs/online-ftl-migration-20261005/native-fences/example_2_10.json` | `b7f79804702d12b47d0ab5e85abccb5a5ae440ca17d3b3d058fa610e6ac40cb9` |
| `runs/online-ftl-migration-20261005/native-fences/failure_prediction.json` | `3b4b99dc18031de73e20880aa43e18336fe07bc981db934b29a9a42292f31961` |
| `runs/online-ftl-migration-20261005/native-fences/failure_prefixCoefficient.json` | `a0d5b8b62802572a5a6610e12809a01f78e9df85b59b7527e8733188e93a4249` |
| `runs/online-ftl-migration-20261005/native-fences/linearFTLPredict_mem.json` | `d5df0e1fb94b461005002507f3508fec78eedc8b72caed3c9b51bbf03658f6a5` |
| `runs/online-ftl-migration-20261005/native-fences/linearFTLPredict_minimizes.json` | `a07d7d39ef493c052bb353a9e4f2880bb1a1d1e20eb39d7dd9efe8ec0b2cb0fb` |
| `runs/online-ftl-migration-20261005/native-fences/linearFTLPredict_prefix.json` | `ceb2965b472f72e27610feed8f694affd6dab3ddd1b05d104095a8b7aef6d5f1` |
| `runs/online-ftl-migration-20261005/native-fences/prefixCoefficient_eq_sum.json` | `3b7ad6e631e28c3e7fecdc5a9a6472a957e61d4fc7ce673c67dff2cdfbd4c50a` |
| `runs/online-ftl-migration-20261005/native-new-task-exit.json` | `84c33c85a21b1c1583c282e6398cb95e699977beb4b564ca68a64f45b773d695` |
| `runs/online-ftl-migration-20261005/native-new-task.log` | `9bedc35fdb5ba9ca1e6b8d1bcb2319e8f4b6112854d75a96c199d85b04745e8e` |
| `runs/online-ftl-migration-20261005/original-public-canary.lean.txt` | `b928a253c241c10962a14ec1e07ac842cab45bd4bf11ec97b22f9d01c7f3b783` |
| `runs/online-ftl-migration-20261005/original-public-module.lean.txt` | `6e8a2d00f2d8c2bd342208f8495f8257df2d074d5ca52efadba014cbc662c984` |
| `runs/online-ftl-migration-20261005/prepare-body-review-v1-01-exit.json` | `4e90c546f7fa0dfaa76dc569c6edf5b24c487ed47d9dee5172e5e5733e5f43b5` |
| `runs/online-ftl-migration-20261005/prepare-body-review-v1-01.log` | `832375e7c5fc06eb4a0796ea61b7cd3a012b2868603369601cd543961db56252` |
| `runs/online-ftl-migration-20261005/prepare-body-review-v1-02-exit.json` | `de6e79d768e3921eef9565a33d90c3f38c15616bd648d1a4dce37c4d66916e49` |
| `runs/online-ftl-migration-20261005/prepare-body-review-v1-02.log` | `fa1ddc7602b3f6111b02bc3e815676c5aa93974d65e09bd6c25c89da8bf71ec6` |
| `runs/online-ftl-migration-20261005/prepare-body-review-v1.py` | `8f14b92419366064fad908b0d1a1f5f2c98c405c203356a2c93ddc5e65adead9` |
| `runs/online-ftl-migration-20261005/prepare-draft-v1-01-exit.json` | `f23b44109c6ad1ec3343ce7a4be0d22605723c3623032d7a3908313a8985c926` |
| `runs/online-ftl-migration-20261005/prepare-draft-v1-01.log` | `6c04c70eeca532ef8bb1810268e6d0efb69826a52bb79cb7290a42f869355174` |
| `runs/online-ftl-migration-20261005/prepare-draft-v1-02-exit.json` | `4fa2d391ada062ebeaacb9018352b7fab4f0da4769728ee1cf3a799964bf2471` |
| `runs/online-ftl-migration-20261005/prepare-draft-v1-02.log` | `2b5d97eeee01690414f1271cba87571387e4727820034d5df902657f580b3947` |
| `runs/online-ftl-migration-20261005/prepare-draft-v1.py` | `c8f3560f64beb86068e0341602da32fab884abfd2ca08b1b0e2b840749d1d16b` |
| `runs/online-ftl-migration-20261005/prepare-proving-v1-01-exit.json` | `fe4186b748d7675ee4992baec05478e647090760779b8514a2789bd78d798f1f` |
| `runs/online-ftl-migration-20261005/prepare-proving-v1-01.log` | `26e274f6e1f2c87804862f450fd89969e4513f17776b582b29857dd4e1f7cd33` |
| `runs/online-ftl-migration-20261005/prepare-proving-v1.py` | `c8ec1cc1e46b9576502b48dad017baf5b46f4984f08cc4dc6cf86a5d39c245d1` |
| `runs/online-ftl-migration-20261005/prepare-source-review-v1-01-exit.json` | `fbcc837539173bee75389eba37c2a63414cdca98148d5763e852752115f11e0f` |
| `runs/online-ftl-migration-20261005/prepare-source-review-v1-01.log` | `d67a5faeb070faf19fe8152ce984ccf71716b6dc36de2bc09500dbb0d2295857` |
| `runs/online-ftl-migration-20261005/prepare-source-review-v1.py` | `27bc256cdfa9ceb79eafc61c6014a402e17d9832699d0236829c953ee2aca806` |
| `runs/online-ftl-migration-20261005/proof-obligations-proving-v1.json` | `c9afdb184a1bb7b2863a7b3cda8e13c246961e404114330d37d7413db68d589c` |
| `runs/online-ftl-migration-20261005/proof-obligations-v1.json` | `d2858ac09451d032870512fabd9853cca4a81183fd7d4093b2c6caad5da0fe5a` |
| `runs/online-ftl-migration-20261005/proving-lifecycle-v1-exit.json` | `78d5a7329f12e71fa768bb21033ff19f037e13b9f64666604bc801d0488e4377` |
| `runs/online-ftl-migration-20261005/proving-lifecycle-v1.log` | `dd2c3308f3d6340a24c28939c980904bd5df22eb27474892e94fc8b7baa433e1` |
| `runs/online-ftl-migration-20261005/public-actual-bindings-v1.json` | `3293ce7e0ed25d73fe6a45e06349d2befa191e4b15fa3f8cf4f2ab6f31c04f31` |
| `runs/online-ftl-migration-20261005/public-axioms-v1-01-exit.json` | `67e6a8bb34544e4ea789c6eda28a135cf63226f2c6e258e23cb2aa6ec5f54028` |
| `runs/online-ftl-migration-20261005/public-axioms-v1-01.log` | `74cfd04bfebb93b2b7a76828a236797e1c07b442265fd85569f110b52ca33750` |
| `runs/online-ftl-migration-20261005/public-body-review-packet-v1.md` | `acc960452de5d2e47746ffaeb2461b4f584b556ee3d614514a8775b7384e3d50` |
| `runs/online-ftl-migration-20261005/public-canary-elaboration-v1-01-exit.json` | `235c80565d5e881e9360293707b07dbbf8aa03bf960eb253baecdbacf2e8ba83` |
| `runs/online-ftl-migration-20261005/public-canary-elaboration-v1-01.log` | `e560db50ab0000f90dac7380170f5bd1e4704325ee1fc278534a52fa76aed5bd` |
| `runs/online-ftl-migration-20261005/public-named-declarations-v1.json` | `2ae06857a6da33f14d68c34998beeca87073d09299e4ac798af4c8598ac66f08` |
| `runs/online-ftl-migration-20261005/public-safe-guard-audit-v1.json` | `a9bd90a4bca7a60bae84b3f3243dd9f507f54cf0eb8dff6b0118bbb9965e76c4` |
| `runs/online-ftl-migration-20261005/ready-dependencies-v1.json` | `82a7886b1bbc2d895f3492ca1546abe2d9376a2f504fcff38c0443aaf39e748b` |
| `runs/online-ftl-migration-20261005/ready-graph-retrieval-v1-01-exit.json` | `7cc6b5d35a71233c2b078fcda7b59ca0165525902bcd93d5f7bcc898611e6db8` |
| `runs/online-ftl-migration-20261005/ready-graph-retrieval-v1-01.log` | `f4a05ab54da9b839ad0911052c985d2215df55147fc336647f618bb2de22f990` |
| `runs/online-ftl-migration-20261005/retained-body-elaboration-v1-01-exit.json` | `5767ae9b6f68b55dbf6fced9c66317200803c44acaf49ddeedeaf2f5243fff20` |
| `runs/online-ftl-migration-20261005/retained-body-elaboration-v1-01.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `runs/online-ftl-migration-20261005/retained-body-trial-v1-02-exit.json` | `da3de70f397ecaf0b9ef4612d30f7ff87a0f29f11964180c7a1e59ed9bb4f27b` |
| `runs/online-ftl-migration-20261005/retained-body-trial-v1-02.log` | `f748215723b036084c70dd84e0a980a106ae60fc67305dddac30595f0365fef4` |
| `runs/online-ftl-migration-20261005/retained-body-trial-v1-03-exit.json` | `9d1450b6f95e300f132a2f4a5a4f227f3e65a5536e04708914a16f6a4e403f9e` |
| `runs/online-ftl-migration-20261005/retained-body-trial-v1-03.log` | `b5d370e619ff526ecca4e6b886384b28c1732eec1d014ec61e24aedc771941ac` |
| `runs/online-ftl-migration-20261005/retained-body-trial-v1-exit.json` | `4c13d2519b714630f87d826277f5af15608c4b60a6e7803301ba48d1b6fdcbea` |
| `runs/online-ftl-migration-20261005/retained-body-trial-v1.log` | `1bf4360182030254f323b395c8540020136af10f24e11cd351bfa22ce5f04abf` |
| `runs/online-ftl-migration-20261005/retrieve-ready-graph-v1.py` | `b61eb4d2868ec079ee56703201e1af05df1218b3e9c927e95449a8bd5865dff3` |
| `runs/online-ftl-migration-20261005/run-command.py` | `c513b8a171af602dd3f72af15823ed5f1308faccdb8526d5dcca87ddcbf86887` |
| `runs/online-ftl-migration-20261005/safe-public-v1-example_2_10-exit.json` | `e0f8060eba27f37481879914ccfcacabdc89f127c64e7489fa017dd3cf00cd97` |
| `runs/online-ftl-migration-20261005/safe-public-v1-example_2_10.log` | `5c070ba573c47def281d44cc1c03fa2f017ccdb5295e561811aaa94acd35fdae` |
| `runs/online-ftl-migration-20261005/safe-public-v1-failure_prediction-exit.json` | `6e07e61bf1f13e79746b1c4c3343e885dfc49e1706f7e42df22c97b2add0e373` |
| `runs/online-ftl-migration-20261005/safe-public-v1-failure_prediction.log` | `e26c5e252e9c18bfd9db8bc686e2f7b71ebb478af1a88a3585963d0046e1b502` |
| `runs/online-ftl-migration-20261005/safe-public-v1-failure_prefixCoefficient-exit.json` | `6ff4707a08d96f717041d18c3c1e859cb9f83dd5c6b2f809ff2919cc53ba50df` |
| `runs/online-ftl-migration-20261005/safe-public-v1-failure_prefixCoefficient.log` | `24adb5dd2d8b5bcc69879dc0605f6741cfa4a6e5fb4a38cca141c166f9ccb032` |
| `runs/online-ftl-migration-20261005/safe-public-v1-linearFTLPredict_mem-exit.json` | `6f9ce4be160c6a20a55d22e02c60d3ffc827222f00b3821134a08cd5dc8c3adb` |
| `runs/online-ftl-migration-20261005/safe-public-v1-linearFTLPredict_mem.log` | `6677353fa5a6eec693b3e3738a10844dae48821bac13b7a225674f1f4f8b2b43` |
| `runs/online-ftl-migration-20261005/safe-public-v1-linearFTLPredict_minimizes-exit.json` | `e200f62287d5284ee877847806f56879508b434b1deb806c1573407466b5c07a` |
| `runs/online-ftl-migration-20261005/safe-public-v1-linearFTLPredict_minimizes.log` | `e7415e0d95e21c7e8a8cdc3122bb0d7e8c55919af8352e8da746b1f533ca89ed` |
| `runs/online-ftl-migration-20261005/safe-public-v1-linearFTLPredict_prefix-exit.json` | `abcd23acf6ed0fc9a0ab0fb33d51e81b058732d81b49d11fbe5123659fb160e2` |
| `runs/online-ftl-migration-20261005/safe-public-v1-linearFTLPredict_prefix.log` | `b3e27c3a094cdfddaf74354dd41411be676427c3827d7005d1e47b65d17fcad4` |
| `runs/online-ftl-migration-20261005/safe-public-v1-prefixCoefficient_eq_sum-exit.json` | `305491f351b45d2fa31023852ef75e58e842990490ea155833d46cfde17c864c` |
| `runs/online-ftl-migration-20261005/safe-public-v1-prefixCoefficient_eq_sum.log` | `5af30fd9d5e2a6fe2dfa99eb12bf3ec228e03cea8818be0b99cc617331c70f41` |
| `runs/online-ftl-migration-20261005/source-contract-receipt-v1.json` | `f64d10493094ae4c0afdf6e62877336ed6170bc241f61b613578698f3df2f535` |
| `runs/online-ftl-migration-20261005/source-contract-review-v1.md` | `fd46a46cd1febc1dbb90df97c7ff9a7fb464f1517e67c9736188a5d64ea35e61` |
| `runs/online-ftl-migration-20261005/source-printed12-pdf24.txt` | `f08eac17353c880065998a9a39fd8e132854d6905f29969e3865c46bbf346107` |
| `runs/online-ftl-migration-20261005/source-review-packet-v1.md` | `b909d6f0a28e6b0e66e09aef7217ab90ba263bb33b1d08ee125b233fe182773f` |
| `runs/online-ftl-migration-20261005/stabilized-lifecycle-v1-exit.json` | `adf12fadaae690d03a19b8df864c52cd5bde9e152fed86379042e8c4ff037c8d` |
| `runs/online-ftl-migration-20261005/stabilized-lifecycle-v1.log` | `ce02da0a36ae4744c909056b736567e7bcbd1c45fb7b59e7dc737db94274610e` |
| `runs/online-ftl-migration-20261005/verify-public-fences-v1-01-exit.json` | `346ab7bf168a9aacefe07455dfa50dc607cb62c8720aab4935c0905a5a280dd0` |
| `runs/online-ftl-migration-20261005/verify-public-fences-v1-01.log` | `9bf83e4a559862f73115cd6320e2ff17b641146909f853d86a2c2f15745ad045` |
| `runs/online-ftl-migration-20261005/verify-public-fences-v1.py` | `c3012281b2f05e45bee1bbc65af1b02903cc0d06ff180875e68bbf253ae5f7a1` |
| `runs/online-ftl-migration-20261005/workspace-workflow-audit-v1.json` | `f8dca81889278c756c9157e78b74e7f3daf9a868ec020d38ddebd8e45dcfe773` |
| `tasks/ONLINE-FTL-MIGRATION-20261005.md` | `a27ae5d2880a98588a4057dad432c35335d564ea9fe75ddfdd7c28e23ea5b51d` |
| `tmp/online-ch2-enumeration-source20-35.txt` | `adc5b396aa3d32dff754c77dbd05d708e967d4c88eddad78c97cf34e47e9b935` |
| `tmp/online-ogd-migration-full-graph.json` | `035630137ecb541e2680c1db4f0ce03b2380f46f322efc157227c6fc73bd9613` |
| `website/content/chapters.json` | `fdfbb741f585e2e5f5ea2ac0a00251aa0e46a6eec1d01ca32ec25749fa68a34c` |
| `website/content/highlights.json` | `e024cf33a9e39cfdd50889c136d543014b0aa61fe6d69d7bfea2e7b454388cd0` |
| `website/content/readings.json` | `981fbf21e718fbb337cb848a065e686e8e874591e1869fc29b5d81964974aef6` |
| `runs/online-ftl-migration-20261005/public-body-inputs-v1.json` | `6f288f672ea4b03e24d8084c9539aba2174b3005672d76fb6d8c606151f3ca4d` |
