# FTL migration: independent source-contract review v1

Verdict: **accepted-with-explicit-delta**, restricted to stabilization of the retained seven statement contracts and three definitions against Example 2.10. No new body, canary, combined-project or package acceptance is conferred.

Actor: `/root/source_reviewer`, distinct automated source reviewer from the formalizer and `/root/normal_blind`. Requested model GPT-6 Astra / medium; runtime identity is not independently attested. This is not human or external-model review. Historical same-actor acceptance is not evidence for this judgment.

## Actual checks and source

Independently read and SHA-256 checked all 92 fixed input rows: zero drift. The inventory itself supplies a 93rd raw binding below. Binary/raw reading for inventory integrity is distinguished from semantic scrutiny: this review closely inspected the original source page, full current FTL module for contradiction checks, all seven frozen headers/native records, three context definitions, source intent, neutral packet/reconstruction/receipt, and current preparation/snapshot evidence. Ancillary historical rows are bound for provenance, not recertified as independently correct. No theorem compilation was run in this review.

The original pinned PDF SHA-256 is `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17`. Fresh pdftotext extraction of physical page 24 (printed 12) was read directly. Example 2.10 fixes V=[−1,1], initial coefficient −1/2 and later coefficients +1 on even source rounds, −1 on odd source rounds. It allows any feasible first action and states regret against 0 exactly T−1−x₁/2 ≥ T−3/2. The source's immediately preceding sentence permits any admissible first point.

All seven actual public normalized declaration headers equal their frozen statement strings and native SHA-256 values; every declared assumption fragment occurs in the actual header. This checks header identity, not a fresh safe-verifier/build gate. Both authoritative original module and canary snapshots equal current public raw bytes. The earlier snapshot01 extra-EOF administrative failure remains failed history. The clean blind packet contains definitions and proof-omitted statements, without source names; its reconstructed quantifiers and boundaries agree with the actual declarations. Its raw input and report hashes match this inventory.

## Seven-slot comparison, per target

Columns are the required slots: objects; quantifiers; assumptions; conclusion; constants/index; information/probability; excluded boundary. Every row is accepted at statement level with the explicit refinements below.

| Target | Objects | Quantifiers | Assumptions | Conclusion | Constants/index | Information/probability | Boundary |
|---|---|---|---|---|---|---|---|
| prefixCoefficient_eq_sum | Real coefficient stream, recursive prefix | Every z,t | None | Prefix equals finite sum | range t excludes t; empty sum 0 | Deterministic strict past | Generic library identity, not separately printed theorem |
| linearFTLPredict_prefix | Two streams, same x0 and time | Every z,w,x0,t | Equality for all i<t | Actual predictions equal | Strict cutoff, includes t=0 | Current and future coefficients may differ | Fixed initial input; no external x0-selection information theorem |
| linearFTLPredict_mem | Real action in closed interval | Every z, feasible x0, every t | x0∈[−1,1] | All predictions feasible | Endpoints included | Deterministic | No claim for infeasible initial action |
| linearFTLPredict_minimizes | One current action evaluated on all past linear losses | Every z,x0,t and feasible comparator u | Only u∈[−1,1] | Exact past-objective inequality | Empty t=0 objective; no error term | Uses past coefficients, not cumulative played actions | Inequality alone is not feasible argmin at t=0 for arbitrary x0; combine membership theorem |
| failure_prefixCoefficient | Specified alternating stream | Every t>0 | Positive t | Prefix −1/2 for odd t, +1/2 for even t | Lean t=source round−1 | Deterministic fixed sequence | t=0 excluded, generic streams not covered |
| failure_prediction | Actual sign selector on specified stream | Every real x0,t>0 | Positive t only | Prediction +1 odd Lean t, −1 even Lean t | Corresponds to source even/odd rounds | Computed from past, despite equaling current coefficient on this witness | Initial action unrestricted in this helper; source terminal restores feasibility |
| example_2_10 | Actual cumulative real linear losses and comparator 0 | Every feasible x0 and every natural T>0, same witness stream | x0∈[−1,1], T≥1 | Equality AND uniform lower bound | Exactly T−1−x0/2 and T−3/2 | Deterministic realized regret of this actual FTL family | No all-algorithm lower bound, expectation, optimal-comparator identity, or T=0 equality |

The three definitions are faithful structural refinements: prefixCoefficient accumulates exactly z0 through z(t−1); linearFTLPredict prioritizes x0 at time zero and then minimizes the linear prefix using its sign; failureCoefficient shifts source one-based indexing to zero-based indexing, retaining the exceptional first coefficient. These definitions introduce no convexity, stochastic or oracle premises. The generic stream need not be bounded; the source witness is the specified bounded stream.

## Challenges, explicit deltas, and disposition

1. **Actual minimization versus a desired bound.** The minimization header evaluates the same current action against every past loss, not the already played sequence. Factoring the historical objective as S_t x makes the sign selector an actual minimizer: S_t<0 selects upper endpoint 1; S_t≥0 selects lower endpoint −1. Feasibility must be supplied separately at t=0. The packet and decoder state that limitation correctly; no source narrowing results because the terminal assumes feasible x0.
2. **Tie and source universality.** A concrete −1 choice at positive zero prefix is a permitted FTL tie resolution, not the full family of all possible tie rules. The specified failure stream has prefix ±1/2 for every positive time, hence unique later minimizers. The source failure conclusion therefore remains valid for arbitrary feasible first action; this concrete generic selector does not lose any behavior relevant to the example. Do not present the generic helper as a universal theorem about arbitrary adaptive tie policies.
3. **Causality and indexing.** The time-t prediction reads only a strict prefix, with x0 a fixed input. Source round t+1 maps to Lean t, reversing the apparent even/odd labels exactly as required. The witness stream is fixed independently of x0. The availability of an entire stream as mathematical input does not make the selector anticipatory. Conversely, the prefix theorem does not prove anything about an external procedure choosing x0 using future data.
4. **Regret boundary.** At T=1 the exact value is −x0/2 and the lower bound is −1/2. At T=0 the proposed equality would falsely give −1−x0/2, so the explicit positive-horizon condition is necessary. Comparator 0 is feasible but generally not the hindsight minimizer. Every later played loss is +1, giving exactly the printed finite-horizon identity, rather than only an asymptotic linear-growth claim.
5. **Attribution and status.** Six helper statements and three definitions articulate the algorithm/source arithmetic; they are library refinements, not six additional printed source theorems. Existing bodies were available and inspected only for contradictions; their historical compilation and prior same-model verdict are not fresh body acceptance. Native captures and declaration retrieval are not safe-verifier proof acceptance.

No mathematical contract repair is required. Mandatory next work: fresh actual-body and nondegenerate canary review/build, current focused and combined root/Tests/full harness evidence, appropriate axiom/native proof-dependency/fence checks, source-faithful shared reader/registry/site and contributor review, immutable bindings and separate package/PR decision. Neither Chapter 2, Chapters 1–16, exercise inventory, Goal, main integration nor live publication is accepted here. Historical failures must remain distinguishable from successful repair evidence.

## Exact raw bindings

All hashes below are SHA-256 of actual raw bytes, without line-ending or JSON normalization.

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
| `runs/online-ftl-migration-20261005/actual-declaration-retrieval-exit.json` | `62a55fe1e41d77338dfe53a4b4d0ed9b4f7281f819fde4ae8e3b199f7733ec44` |
| `runs/online-ftl-migration-20261005/actual-declaration-retrieval.log` | `95db75e2a6d1cfb0632ab222e324bb96d04ae0e42aa9da61b33ad702c899b396` |
| `runs/online-ftl-migration-20261005/blind-packet-v1.md` | `60ba567cec00c4f2e93fd67069c4da01c338bc198ca80153237f5e80d5217708` |
| `runs/online-ftl-migration-20261005/blind-receipt-v1.json` | `928536f2240f2d632ee568071f38fe47a44a7b3ed7e520d6ae5db1b5122d967b` |
| `runs/online-ftl-migration-20261005/blind-reconstruction-v1.md` | `a9b97e423357edd5f7134e68149169a3423da28577edcd70810f17682fa3d9e8` |
| `runs/online-ftl-migration-20261005/chapter2-navigation-draft-01-exit.json` | `bcc37dad1aeacc7f80710cbd3b5ebff4d4d69feedc440ed1f98baab48a4e8b24` |
| `runs/online-ftl-migration-20261005/chapter2-navigation-draft-01.log` | `c86ed1f54309f2de77cb02cd94a4b2cc8322da00084c0c7816ab276dc5071a6a` |
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
| `runs/online-ftl-migration-20261005/help-new-task-exit.json` | `9630e1c62174673313ac4012b1f058b3ecb55ca55f0b2323d4c94a20a94674c9` |
| `runs/online-ftl-migration-20261005/help-new-task.log` | `25eb9342c3094bee57187630bd149d2c522fc9f7ac7e65bebe5c198eba60ed99` |
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
| `runs/online-ftl-migration-20261005/prepare-draft-v1-01-exit.json` | `f23b44109c6ad1ec3343ce7a4be0d22605723c3623032d7a3908313a8985c926` |
| `runs/online-ftl-migration-20261005/prepare-draft-v1-01.log` | `6c04c70eeca532ef8bb1810268e6d0efb69826a52bb79cb7290a42f869355174` |
| `runs/online-ftl-migration-20261005/prepare-draft-v1-02-exit.json` | `4fa2d391ada062ebeaacb9018352b7fab4f0da4769728ee1cf3a799964bf2471` |
| `runs/online-ftl-migration-20261005/prepare-draft-v1-02.log` | `2b5d97eeee01690414f1271cba87571387e4727820034d5df902657f580b3947` |
| `runs/online-ftl-migration-20261005/prepare-draft-v1.py` | `c8f3560f64beb86068e0341602da32fab884abfd2ca08b1b0e2b840749d1d16b` |
| `runs/online-ftl-migration-20261005/prepare-source-review-v1.py` | `27bc256cdfa9ceb79eafc61c6014a402e17d9832699d0236829c953ee2aca806` |
| `runs/online-ftl-migration-20261005/proof-obligations-v1.json` | `d2858ac09451d032870512fabd9853cca4a81183fd7d4093b2c6caad5da0fe5a` |
| `runs/online-ftl-migration-20261005/run-command.py` | `c513b8a171af602dd3f72af15823ed5f1308faccdb8526d5dcca87ddcbf86887` |
| `runs/online-ftl-migration-20261005/source-printed12-pdf24.txt` | `f08eac17353c880065998a9a39fd8e132854d6905f29969e3865c46bbf346107` |
| `runs/online-ftl-migration-20261005/source-review-packet-v1.md` | `b909d6f0a28e6b0e66e09aef7217ab90ba263bb33b1d08ee125b233fe182773f` |
| `runs/online-ftl-migration-20261005/workspace-workflow-audit-v1.json` | `f8dca81889278c756c9157e78b74e7f3daf9a868ec020d38ddebd8e45dcfe773` |
| `tasks/ONLINE-FTL-MIGRATION-20261005.md` | `a27ae5d2880a98588a4057dad432c35335d564ea9fe75ddfdd7c28e23ea5b51d` |
| `tmp/online-ch2-enumeration-source20-35.txt` | `adc5b396aa3d32dff754c77dbd05d708e967d4c88eddad78c97cf34e47e9b935` |
| `runs/online-ftl-migration-20261005/contract-source-inputs-v1.json` | `e20d698a338cd816b34c71caf4b327f7e91fa4c5fe5e3c5ff7fb72fc2b53ba34` |
