# ONLINE-LINEARIZATION source contract review v3

Verdict: **accepted-with-explicit-delta**, for stabilization of the 18 frozen unproved headers and their actual definition context only. No proof-body or public/package acceptance is granted.

Actor `/root/source_reviewer`; requested GPT-6 Astra / medium; runtime model identity not independently attested. Distinct automated source reviewer, not external-human or external-model review. Formalizer and clean v3 decoder are separate actors. Only the two new review outputs were written.

## Source, neutral reconstruction and actual interfaces

The original pinned PDF independently hashes to `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17`. Physical34/printed22 was freshly extracted and read. Section2.3 explicitly compares the original loss gap with the global supporting linear loss at the same plays, sums those gaps and explains OLO-to-OCO transport for arbitrary vector sequences. It does not assert that this reduction is always optimal. Physical28–29 was also reread for Definition2.20: properness is inherited and support tests all ambient y. No eighteen numbered source theorems are asserted here; structural declarations are library refinements of one unnumbered reduction.

All 52 fixed v3 raw rows hash-match. All 18 header files independently match the native normalized headers extracted from the actual draft declaration file, their SHA256 fingerprints and premise fragments. The draft has empty `:= by` slots, not proofs. The original and neutral probes only check well-typed propositions/context. Their exit0 evidence establishes type formation, not theorem validity or axiom closure. The two context copies have identical decoded text but different raw line endings; each is separately raw-bound.

The actual clean v3 blind report and receipt were awaited, then read and independently hash-checked. They reconstruct all 18 targets across seven slots and correctly distinguish selected-vector histories from output histories, universal from played legality, and full-sequence B from a prefix-restricted bound. V1 missing type context and v2 probe failure remain historical diagnostics; neither is clean acceptance. The v3 packet's introductory mention of v2 is historical wording, not a second accepted packet.

Imported semantics were checked directly: shared Domain, SupportPolicy, OracleLaw, canonicalPolicy/currentSubgradient, SubdifferentiableOn, SourceProper, global SourceSubdifferential, subgradient_point_finite and comparatorRegret. Actual EReal.toReal sends both infinities to zero. The contract therefore must rely on properness and real global support to establish finiteness; toReal alone is not evidence. The displayed neutral definitions agree with the relevant actual interfaces. Inspection of these imported files is scoped to these definitions/APIs, not a new acceptance of every theorem in each file.

## Anti-anchored findings and retained deltas

The history recursion is genuine: A sees a finite strict-past vector tuple; p sees strict-past whole losses, reconstructed actual outputs through the current point and the current whole loss. The current vector is appended only after play. The outputHistory_played and output_linear_run targets are essential producers: without them, the intended same-run reduction would merely be asserted. They are explicitly required rather than assumed as terminal input.

Main regret_comparison and regret_transfer deliberately omit Feasible and universal OracleLaw. Given properness and actual legal global support, even an ambient played point has finite loss; a feasible comparator has finite loss from regularity. This makes the algebraic comparison stronger than the source-feasible algorithm case. It does not claim such an arbitrary ambient-output learner is a valid OCO algorithm. The feasible/canonical adapters supply that separate implementation scope. Universal Feasible constrains off-path vector histories for those adapters; the main comparison does not acquire that extra restriction.

The shared Domain retains nonempty closed convex structure from the OCO setup; the pointwise support algebra itself needs less. Thus this is stabilization in that inherited domain model, not a claim of maximal reduction generality for arbitrary nonclosed/nonconvex sets. Finite-dimensional real inner-product abstraction represents Euclidean space, including dimension zero. Regularity needs properness and nonempty global supports on V, not global convexity, differentiability, bounded domain, bounded vectors or Lipschitz constants.

The hB premise is a genuine universal OLO performance contract for the same A at fixed T, over every full vector sequence and every feasible comparator. Instantiation with generated supports is a valid reduction interface, not circular assumption of the desired actual OCO gap. It does not produce a useful OLO bound, prove sublinear regret, handle an expectation-only guarantee, or impose that B depends only on the first T entries. Future proof/reader claims must preserve these qualifications. A and p are fixed external functions; prefix causality does not prove how a caller selected them is independent of future information. No randomized law or executable oracle is covered.

## Per-target seven-slot verdicts

Every row below is accepted for contract stabilization with the shared deltas above. O=objects, Q=quantifiers, H=hypotheses, C=conclusion, K=constants/indexing, I=information, B=boundary.

| Target | O | Q | H | C | K | I | B |
|---|---|---|---|---|---|---|---|
| `outputHistory_last` | A,h and reconstructed output tuple | All A,t,h | Ambient only | Last coordinate equals A t h | Input length t; output t+1 | Only supplied past vectors | t0 permitted; initial output need not be zero |
| `history_zero` | Actual vector history | All A,loss,p | None beyond ambient | H0=empty function | Length0 | No current feedback yet | Does not assert x0=0 |
| `history_succ` | Consecutive histories and selected g | All runs,t | No legality/regularity | H(t+1)=snoc H(t) g(t) | One append | Current loss read only for appended support | Selected may be illegal without a premise |
| `history_castSucc` | Old history coordinates | All runs,t,i<t | Finite index only | Old entry unchanged on append | No shift; new index t excluded | Past persistence | No i at t0 |
| `history_selected` | History and actual selected sequence | All runs,t,i<t | No extra premises | H(t)[i]=selected(i) | Exact same index | Same run; no current vector in history | t0 coordinate quantifier empty |
| `output_linear_run` | Actual play and linearRun of actual selected sequence | All runs,t | No legality or feasibility | Exact same output under same A | Coefficient1 equality | linearRun queries only indices below t | Not an unrelated vector sequence |
| `outputHistory_played` | Reconstructed and actual output tuples | All runs,t,i<=t | No extra premises | Reconstruction equals actual output(i) | Includes current output, not next | Earlier outputs use appropriate prefixes | t0 single initial output |
| `output_mem` | Domain and actual output | All feasible A,loss,p,t | Universal Feasible V A | Actual output in V | No numerical bound | Feasibility does not require loss legality | All off-path histories covered by input feasibility |
| `history_prefix` | Two loss streams/common A,p | Every t and pair of streams | Whole-function equality for s<t | Equal actual vector histories at t | Strict cutoff | Conditional on fixed A,p | Current selected vectors may differ |
| `output_prefix` | Paired actual plays | Every paired run,t | Same A,p; strict-past loss equality | Equal current output | Strict cutoff, initial A0 common | No future/current loss affects play | Not independence of externally chosen policies |
| `oracle_feedback` | Actual run and universal support law | All feasible A,legal-law p,T | Feasible; OracleLaw; regular losses below T | Played LegalFeedback | 0<=t<T | Off-path law sufficient, not main-terminal requirement | T0 vacuous; no converse |
| `canonical_feedback` | Canonical chooser run | All feasible A,regular losses,T | Feasible and prefix regularity | Played legality without caller-supplied law | Current chooser fallback0 unused on valid points | Classical current choice | No executable or unique selection claim |
| `trajectory_finite_loss` | Played EReal value | Every feasible run,T,t<T | Feasible and prefix regularity | Value equals finite-real embedding of toReal | Exact equality, no magnitude bound | Does not require selected p to be legal | No eligible t at T0 |
| `support_gap` | One proper globally supported loss | All ambient x,g and feasible u | Regular V f; hu; actual global hg | Finite real gap <= inner g (x-u) | Unit coefficient, no slack | No algorithm assumption | x need not belong to V; finiteness derived |
| `linearLoss_gap` | Real inner-product linear loss | All g,x,u | Ambient inner product only | Loss difference equals inner g (x-u) | Exact unit coefficient | Algebraic identity | Zero vectors/dimension0 allowed |
| `regret_comparison` | Actual run and OLO regret on generated supports | All A,p,loss,T and feasible u | Prefix regularity; played legality; hu | Original regret <= linear regret on same A/path | Factor1; no additive term or norm bound | Generated adaptively; exact output_linear_run needed | No Feasible/OracleLaw premise; stronger algebraic ambient-play comparison; T0 |
| `regret_transfer` | Same run and arbitrary real bound functional B | Fixed T; hB all full g and all feasible comparators | Comparison premises plus universal OLO hB | Original regret <= B(actual selected,u,T) | No prescribed rate/sign; B may depend on full g | Universal pathwise bound instantiated on adaptive g | Conditional reduction, not bound producer; not expectation-only or anytime |
| `canonical_regret_comparison` | Feasible learner and canonical actual run | All feasible A,regular prefix,T,u in V | Feasible, regularity, hu; no supplied legality | Exact comparison using canonical selected sequence and same A | Factor1, T0 included | Current classical chooser supplies legal feedback | Source-feasible implementation adapter, not new numbered source theorem |

## Required subsequent work

No mathematical header repair is required for this scope. All 18 theorem bodies remain obligations. Future body review must see actual persistence/reconstruction and strict-prefix proofs, actual support-to-finite conversion, and summation into the identical OLO trajectory. Meaningful canaries should exercise nonzero history-dependent play, current-loss changes with unchanged play, strict regret comparison, a real universal OLO-bound instantiation, invalid/infinite inputs excluded from performance, and T=0. These are future validation obligations, not completed evidence.

Public integration, root/Tests/full harness, actual axiom/dependency audits, source-qualified reader/registry, immutable bindings and PR delivery remain pending. Section2.3 stabilization does not finish Chapter2, unit scaling, optimal-step work, older-stack migration or Chapters1–16. No trial/frontier mutation, proof acceptance, merged/main/live or external-human review claim is made.

## Raw reviewed-file hashes

The fixed rows, actual clean blind outputs, pinned PDF and additionally inspected actual interfaces are bound below. Raw hashes do not normalize JSON or line endings.

| Path | Raw SHA256 |
|---|---|
| `runs/online-linearization-20261004/source-binding.json` | `678a9e1ddaec74a2916d1e0f4804118bea6b3bc7e9e147734c4bae93992d629e` |
| `runs/online-linearization-20261004/source-pages.txt` | `0267283cba2567b3ff620e2e521962cdd0bc6e5ad2b715b158ce7855c7a07f26` |
| `runs/online-linearization-20261004/source-card.md` | `8e4c2febc3d9fef6806fad4f545ba931a2f18bb729755420e63e3f0575ad1691` |
| `runs/online-linearization-20261004/blind-packet-v1.md` | `8fa339b23741cd83f1d2e0c3b1710ab93b88ded4a4a7101be2bd441728800ce1` |
| `runs/online-linearization-20261004/leaves/target-v1.lean.txt` | `eca6ecd2a774d5bfbf2ca09fd7149daf4aa3f64f046d745265152f2d88badc19` |
| `runs/online-linearization-20261004/leaves/context-v1.lean.txt` | `9ec3e2b701f36ce5eae78732304b3b87a5dcb4f8225924b355ace8b7488aa5be` |
| `runs/online-linearization-20261004/leaves/types-v1.lean` | `acf2c877df828e96fdb55addecad4a445b5ba1c4ab64e7c514cf20b98933e700` |
| `runs/online-linearization-20261004/draft-types-01.log` | `b55db884677326dbfcabe6e3429cfa756654e99b3cbecb2e90b9ed989263444c` |
| `runs/online-linearization-20261004/draft-types-01-exit.json` | `12534f8b882af454cdbd7a2613662bda4029c6210aa0bf5e80d2be167c2e7817` |
| `docs/contracts/online-linearization-v1/canonical_feedback-header.txt` | `760d2ecabdffa7b48d70ef09c5802da0651b40c1feeb0e12c76cac6fa61aca75` |
| `docs/contracts/online-linearization-v1/canonical_feedback.json` | `6487cfa6bfe4fb84b2d3b53a14ba54aa6b981ae90576b7a94681cfce4c781dc1` |
| `docs/contracts/online-linearization-v1/canonical_regret_comparison-header.txt` | `3b7a863740f496ae0c710b95bda666eec365e96741b254291f80d49d3906eed2` |
| `docs/contracts/online-linearization-v1/canonical_regret_comparison.json` | `628f33c771abbd045026609791541afdb11358cb0458cb190a4f62f97c1ad5de` |
| `docs/contracts/online-linearization-v1/context.lean.txt` | `bdaedf3be81cea1b729845d4433e0e7926d9c63bfd561a41149e6c9dafceac4c` |
| `docs/contracts/online-linearization-v1/history_castSucc-header.txt` | `c13d5cf0176c2be95a8842a813fbb9331aff955e6d3ea6b4757a786c7a53ed52` |
| `docs/contracts/online-linearization-v1/history_castSucc.json` | `d65ff388fb0f9afafbd218aee4b22147fbfc70a30149bfe3e2ae43a2ec7984fb` |
| `docs/contracts/online-linearization-v1/history_prefix-header.txt` | `bc6c7fa34a06393f2f5a724dee5d1c7dd23e2c2e7786fe0b1bd8032f14d32fc2` |
| `docs/contracts/online-linearization-v1/history_prefix.json` | `214ada18324696df4b3084e9769cc19e217d2ad0f3f3114aa783aa0722f69518` |
| `docs/contracts/online-linearization-v1/history_selected-header.txt` | `f6fdf438fb7944dbb1077c998c7b875219eb2cd851a5fa9535d63c49a94a0c23` |
| `docs/contracts/online-linearization-v1/history_selected.json` | `5592ec451e486e58f641d3b7b8fc113b2935ba5f1f58c5d21800283ced331ced` |
| `docs/contracts/online-linearization-v1/history_succ-header.txt` | `37fa8219737d266f604b10adea530102a218af786b6a24d43a7041e2a928b2b3` |
| `docs/contracts/online-linearization-v1/history_succ.json` | `04e7c36998ae6b8a070ffbfbf0322e3c68dc553b5100e5903dadabdf547d82b0` |
| `docs/contracts/online-linearization-v1/history_zero-header.txt` | `1cde80b88a5e7e1887591149b2e45b197ddf145609af62b5702b3eaa1a959889` |
| `docs/contracts/online-linearization-v1/history_zero.json` | `0ef72c4d3dacb2c79d2ee5c05a9dd26bd1b7c3cd29f6458822137b5ac31ced80` |
| `docs/contracts/online-linearization-v1/linearLoss_gap-header.txt` | `db742a269f68436661269b02d41ac09a494c1c9c6a245df630b010c59d2c7cd3` |
| `docs/contracts/online-linearization-v1/linearLoss_gap.json` | `0cd19e1c4ddfb3c624b018fd00eaeea7642e119b681a02870f84e21c399e2407` |
| `docs/contracts/online-linearization-v1/oracle_feedback-header.txt` | `581a546e30e4cc92339c337ebb20c74fbb2b9c5ab4dae55e81507ccb206c9946` |
| `docs/contracts/online-linearization-v1/oracle_feedback.json` | `51e911bcfd7cc44a89409fb70ea7f49deb42accfbe2795768c0a17714c2522b5` |
| `docs/contracts/online-linearization-v1/output_linear_run-header.txt` | `e9d416b8d36d46070f8e875c25e34beb303b28f627a6dff7ab9801edcfb9b1b7` |
| `docs/contracts/online-linearization-v1/output_linear_run.json` | `3451005f4ca3fbfc284a86a6b220cbcd6d893f6c9c6c31984be67e126b6a64ca` |
| `docs/contracts/online-linearization-v1/output_mem-header.txt` | `d77eb66fa66bbb34fdf81400b9209cce5a135754f971c121b39ee4c10bc68c80` |
| `docs/contracts/online-linearization-v1/output_mem.json` | `aae4178189a996b8fd4d6bb99f66fac7afb0bf34d390783c2e022a4f13d5c084` |
| `docs/contracts/online-linearization-v1/output_prefix-header.txt` | `4eac8a36c4ea69db0fb564df06d5dee8407ed3a517a6c6c054f67b552459a9a7` |
| `docs/contracts/online-linearization-v1/output_prefix.json` | `e12eb1e4a703ca3539a1e33ec58fc156cc9b630c5ed24d07306c00f3bd2d933d` |
| `docs/contracts/online-linearization-v1/outputHistory_last-header.txt` | `580388e8e7428c98eeb300992e5e35b6a6a20cc97dff039153954644970d6335` |
| `docs/contracts/online-linearization-v1/outputHistory_last.json` | `42b6413b0671fc9ac1be9b86cc12b49f3df05f636281dcaacdf9f19036408cb5` |
| `docs/contracts/online-linearization-v1/outputHistory_played-header.txt` | `df04ad85352fb33b9c431b2603a72d68380ceb2f9fd101075164c5ee503e9cb6` |
| `docs/contracts/online-linearization-v1/outputHistory_played.json` | `7b9ff1a51be9c50c2cacfe6910cd8ab8255d0f2f96ac14d90d9cc31cc0810b1c` |
| `docs/contracts/online-linearization-v1/regret_comparison-header.txt` | `1e9d4e83d217172dbc06f7a9c8077ff474757e429d34bcec878ac40431219714` |
| `docs/contracts/online-linearization-v1/regret_comparison.json` | `2cc634775684d4f35932e2fd880d14a2f4190628c323c987ec5bd2175a29d744` |
| `docs/contracts/online-linearization-v1/regret_transfer-header.txt` | `2d69556f6d54dcc219b0121f662285136e4e3050dbabcb6022351f46da71c009` |
| `docs/contracts/online-linearization-v1/regret_transfer.json` | `11bfab33548d01b5bc7f63376d5d4ab69d7da1d352f2bce2feaaa27c9f661b02` |
| `docs/contracts/online-linearization-v1/support_gap-header.txt` | `a38adcd0f43051fc5f1dadcbddcacd4e0c291571fa09bb505311af0280951089` |
| `docs/contracts/online-linearization-v1/support_gap.json` | `3f33e87a2e83016b86be4546a7527457cdb6ec419cf58bb9c8735a3d675cadae` |
| `docs/contracts/online-linearization-v1/trajectory_finite_loss-header.txt` | `f119e9cb531bb54beccaf76d238e18b75d1d3b22b05014fc0845e915cebdab0d` |
| `docs/contracts/online-linearization-v1/trajectory_finite_loss.json` | `740eab398df26f85f0230688695d2d75f285a48a568fb6e762f644b7ee83cd77` |
| `runs/online-linearization-20261004/blind-packet-v3.md` | `964805de5c70073daab3df66cd0ba003b8acd832708a7d7bb6388e11aee49bb1` |
| `runs/online-linearization-20261004/blind-presentation-repair-v2.md` | `88ff1621a9fb242e80ed59e872514696ec9ae51339b0ef6200557e748c04cac0` |
| `runs/online-linearization-20261004/blind-presentation-repair-v3.md` | `0d7b9a36a3883d7e32ebd5a51d2a7492a22f170faf4aee74eaf1c98c7654e7ce` |
| `runs/online-linearization-20261004/leaves/neutral-types-v3.lean` | `03b0426b2cacd8dcc689f9737eed4062c54009bfdf66fdd1890f11d75bb6d4c2` |
| `runs/online-linearization-20261004/blind-neutral-types-03.log` | `f844d7782396e70190978d8bb2fcd69a6e0ee99c006c728b089afd873b893d1d` |
| `runs/online-linearization-20261004/blind-neutral-types-03-exit.json` | `36169ace5f94fee7aa878e5902aa78ab5cb2f29dd0674eda88d4ac890335003f` |
| `runs/online-linearization-20261004/source-review-packet-v3.md` | `ab842b6899e13929bafe04536883c01c1763098e21ceab466a073765a59b10b4` |
| `runs/online-linearization-20261004/contract-source-inputs-v3.json` | `e70b85bab1f3fd272ddb7c4b41d90d1ef534f26c3d5229216c19e3149bbb2d63` |
| `runs/online-linearization-20261004/blind-reconstruction-v3.md` | `69644a4fee4faa4f6441a4ed8ddd7b16aca1a9558b3838204545c384fa6f4542` |
| `runs/online-linearization-20261004/blind-receipt-v3.json` | `74d1bbcad14fb6008b3268f52eb5201e03d9deac3920274c32db25167503ee88` |
| `../research-online-ogd/tmp/pdfs/orabona-v10.pdf` | `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17` |
| `BanditRLProof/OnlineSubgradientPolicy.lean` | `ac8fbfb3eee3c92ebb79b44f33beec33b500105bb7e54df5176c14e886c2c662` |
| `BanditRLProof/OnlineSubgradientDescent.lean` | `6ba8586e1691babc2db3e0c0fcddb69b4236e16f9f192c464b4c04262e854f1c` |
| `BanditRLProof/OnlineClosedProper.lean` | `9a5fcfb9e26a2a35d8e5bb7ef7b7a7dfd65a7f1c8daab03faebb51e41d54e7c6` |
| `BanditRLProof/OnlineSubgradientBasic.lean` | `4c17a466091b88d90451be897a2f01afa204b41933191244e0093e48396d1962` |
| `BanditRLProof/OnlineLearningRegret.lean` | `231eda88cb1c45bf3bc9209bfbdd696fbfbe8a64b00303113a23cbc4dff3ca5b` |
| `BanditRLProof/OnlineGradientDescent.lean` | `e7edba540c2f60032bb4a34aaf0768b3107b94276b67b6f41fc289009c8924c1` |
| `.lake/packages/mathlib/Mathlib/Data/EReal/Basic.lean` | `bf69a9ed4bc39134bbefac1a43b187e2f1e66fd43f352d0810ab89474f054922` |
