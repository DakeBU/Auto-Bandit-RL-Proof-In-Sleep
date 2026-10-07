# Contract source review: legal-history absolute-loss guessing

Verdict: **accepted-with-explicit-delta**, CONTRACT stabilization only. No blocking mathematical or metadata repair found. Four prospective target types are accepted with the qualifications below; no target proof body is certified.

Actor: `/root/source_reviewer`, distinct from root formalizer and `/root/osd_blind`. Requested GPT-6 Astra / medium; runtime model identity is not attested. I have prior staged source-review history, including earlier related packages. This is not a blind, external or human review and does not recursively reaccept dependency histories.

I independently verified all 87 frozen raw rows before and after review. The pinned original PDF digest is `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17`. I actually viewed this run's source PDF13/27/31/32 images and read the relevant source text. PDF13–15 establishes the interval prediction game and comparator convention; PDF27 supplies the tuning transfer and future-energy caveat; PDF31–32 supplies subgradient substitution, Algorithm2.2 and Example2.32. Definition2.20's proper-function convention is respected because the reused absolute losses are genuinely finite everywhere and proper. Generic extended-real support/toReal conventions do not substitute fake finite values here.

The source example prints asymptotic upper regret, not the exact finite constant in the new target. The latter is the justified D=G=1 specialization of the stated transfer. The eventual target is a separate upper-average consequence; it permits negative regret. Fixed exogenous policies may close over external parameters: finite explicit input types certify a structural factorization, not independent external parameter selection. No universal off-path law, probability structure or executable support oracle is imposed or certified.

## Per-target seven-slot comparison

### selected_bound — accepted-with-explicit-delta

| Slot | Finding |
|---|---|
| objects | Real scalar absolute loss embedded finitely in EReal; true interval projection; global ambient supports. |
| quantifiers | Every eta, label stream, initial real point and finite-history policy; every t<T on that actual run. |
| assumptions | Played LegalFeedback through T only. No feasibility, label bounds, positive eta or off-path OracleLaw. |
| algorithm_information | selected is the supplied policy applied to actual finite past losses/history and current loss; no comparator input. |
| conclusion | Norm of every actual selected legal support is at most one, not an assumed gradient bound. |
| normalization_boundaries | Absolute loss has global support norm bound one even outside the interval; T=0 gives no t<T. |
| source_relation | Library specialization of full shifted support classification. Arbitrary real labels/initial points/rates explicitly extend source game scope. |

### step_clamp — accepted-with-explicit-delta

| Slot | Finding |
|---|---|
| objects | Same real interval Domain and actual policy output/selection, not an independent trajectory. |
| quantifiers | Every eta,y,x1,p,t with no legality premise. |
| assumptions | No source performance assumptions; identity only. |
| algorithm_information | Next output projects current output minus current selected support times eta; current output precedes current loss selection. |
| conclusion | Full equality with min(max(raw,0),1), not just feasibility or a distance estimate. |
| normalization_boundaries | Scalar multiplication becomes real multiplication; eta can be negative or zero, and t starts at zero. |
| source_relation | Algebraic update refinement of Algorithm2.2 and interval projection; unconditional identity does not certify illegal-policy performance. |

### example_2_32 — accepted-with-explicit-delta

| Slot | Finding |
|---|---|
| objects | Finite real absolute-loss comparator regret of the actual played policy run on [0,1]. |
| quantifiers | Fixed y,x1,p and positive prescribed T; same run for every feasible comparator u. |
| assumptions | Feasible x1, all played labels feasible, and global-support legality on exactly this constant-eta run. No supplied norm/regret bound or off-path law. |
| algorithm_information | Existing Nat.rec/Fin.snoc recursion with finite explicit history and current-loss support query; rate fixed to 1/sqrt(T). |
| conclusion | Sum over range T of actual loss minus comparator loss is at most sqrt(T). |
| normalization_boundaries | D=G=1; T>0 prevents the tuning denominator degeneracy; source round1 is Lean0. Labels retained despite algebraic redundancy. |
| source_relation | Exact finite constant-one specialization of the source O(sqrt(T)) example through the OSD transfer and equation2.1; not a verbatim printed numerical theorem. |

### example_2_32_average_eventually — accepted-with-explicit-delta

| Slot | Finding |
|---|---|
| objects | Signed average regret for a horizon-indexed family of actual constant-rate policy runs. |
| quantifiers | Fixed y,x1,p; legal feedback for every positive horizon; then fixed feasible u and positive epsilon, eventually all natural T. |
| assumptions | Feasible initialization, globally feasible labels, same-policy family legality. No nonnegative-regret premise. |
| algorithm_information | Each T uses its own eta=1/sqrt(T) trajectory. Fixed p does not turn these paths into one anytime path. |
| conclusion | Eventually actual signed average regret < epsilon, an upper consequence only. |
| normalization_boundaries | Real division by natural T; finite exceptional T=0 irrelevant to atTop. Negative averages are permitted. |
| source_relation | Derived one-sided family consequence; neither signed Tendsto zero nor absolute Big-O nor an anytime guarantee is asserted. |

## Context and evidence scrutiny

The actual shared SupportPolicy/history/output/selected/LegalFeedback definitions supply the causal recurrence; LegalFeedback is actual global support membership, not a desired regret certificate. Source supports at the kink may be any member of the whole closed interval. The selected-bound target does not restrict them to a canonical or zero choice. The existing loss norm producer covers all real x,y, so the two broader helpers are sound contract generalizations. Existing regret_tuned requires actual same-run norm bounds and proper/subdifferentiable losses; the planned dependencies can supply them rather than assume the conclusion. This is dependency/interface scrutiny, not a fresh full-body acceptance of all imported modules.

The v2 closed-proposition bridge explicitly maps W/F/X/A/L/b to the actual domain/policy/output/selected/legality/finite absolute loss and proves four type equalities by rfl. I compared the complete S01–S04 binders and conclusions to all four frozen headers. The recorded bridge exit is zero (10.364 seconds), with ordinary unused proof-binder warnings. These are proposition identities, not proofs of any Q or S target. The decoder reconstruction preserves the same quantifier order, global supports and one-sided family boundary.

Original neutral-context owner/type-alias/global-support-context errors and the first bridge import-position failure remain retained. The v2 context/import repairs do not weaken the frozen headers. The initial immutable-guard preparation failure is preparation history, not mathematical closure. Native/raw fingerprints have different roles; this review binds original raw bytes. Existing canary modules are bounded dependency context, not new canary acceptance for these four targets.

## Future reader obligations (not discharged here)

- **R1**: Attribute one printed Example2.32; identify two helpers and the exact finite/one-sided eventual refinements rather than four printed results.

- **R2**: State the real interval game, feasible initial point/played labels/comparators, positive known horizon and eta=1/sqrt(T); retain labels even if unused in algebra.

- **R3**: Explain actual finite-history/current-loss policy inputs and output-before-current-feedback order; no certified independence of externally chosen p, eta or initialization, executable oracle or randomized-law guarantee.

- **R4**: Show played global support membership and the entire shifted support sets, including closed [-1,1] at equality. Optional universal off-path OracleLaw is not a performance premise.

- **R5**: Disclose selected_bound and clamp broader algebraic scope; unconditional clamp is not a performance guarantee for illegal feedback.

- **R6**: Present same-run all-comparator finite sqrt(T) bound, D=G=1, genuine finite loss conversion and actual selected norm producer; do not supply the desired bound as a premise.

- **R7**: State one-sided eventual signed average bound for separate known-horizon runs, not signed convergence to zero, absolute Big-O, future-energy optimization or anytime performance.

- **R8**: Separate reused declarations from four prospective new proofs, dependency readiness/type equality from proof/gate completion, and bounded package from required remaining canonical migration/maintext/Chapter1/2/appendix/whole-Goal work.

Required mathematical repairs: none. Required metadata repairs: none. Required blocking contract repairs: none. Future reader obligations above remain mandatory; BODY review, genuine new canaries, combined root/Tests/harness, graph/kernel/source guards, reader/site/FINAL, immutable acceptance and delivery remain separate. No chapter, whole Goal, main, merge or live completion is accepted.

## Raw inventory

Each listed file was read for raw-byte verification; semantic inspection was directed at source, exact contracts/context, bridge/decoder, dependency interfaces and diagnostic evidence described above. Hashing an imported canary is not independent acceptance of every earlier proof.

| Path | SHA-256 |
|---|---|
| `BanditRLProof/OnlineGuessingSubgradient.lean` | `95d206190d443939115037f9bf6d0eeb1e3229f3ae52eb4150927fbe69e89348` |
| `Tests/OnlineGuessingSubgradientCanary.lean` | `b6a6e3f5c019172e2ee46d3caf03fcbc65d9bbe3a90474b03532ca560f849a61` |
| `BanditRLProof/OnlineSubgradientPolicy.lean` | `ac8fbfb3eee3c92ebb79b44f33beec33b500105bb7e54df5176c14e886c2c662` |
| `Tests/OnlineSubgradientPolicyCanary.lean` | `f830ff51718c5d8504fd02fd98c7372a48ca4f8928410fb7660645a4e3ecff6b` |
| `BanditRLProof/OnlineSubgradientDescent.lean` | `6ba8586e1691babc2db3e0c0fcddb69b4236e16f9f192c464b4c04262e854f1c` |
| `BanditRLProof/OnlineGradientDescent.lean` | `9300cb2735da9f125e404f78b86509df47fe65a5f4d89abc469e071bdffdb871` |
| `BanditRLProof/OnlineSubgradientBasic.lean` | `af3d3f56e4a64cd8adbe47368caf5382e63b428f01da29a121c28c8014f352a5` |
| `BanditRLProof/OnlineSubgradientAbsolute.lean` | `bf3e8d97f67b78e7ad230b8efd321948f4d7ba1a0e9cde31e8d85c1e9019442b` |
| `lean-toolchain` | `b15a57f8ea4c890197465ce1156667ae13d9ed4ab8a9f263a920bf010d967d82` |
| `lakefile.lean` | `0164f3b5b5bdcbb237ab15ae8b44da83e183f4b97d5f3832aa4a57f27dc69d45` |
| `lake-manifest.json` | `87c3e616f86244550ef39e7415186b11c1d4cf4bef20173196a619d9d4d48f48` |
| `runs/active_frontier.json` | `567e5873aa2549a83f2820d758069213808da822a93087129877385a1addf7c3` |
| `docs/contracts/online-book-v1/source-inventory.json` | `a2a504cf40d73f9c5e36f00fc1ef3b949ccaf5a558ab603c1c2a86007f30efa7` |
| `research-wiki/contribution-contracts/ONLINE-GUESSING-OSD-20261004.json` | `388e8d2338a4d31ee8a309de3b2748c40ed1310867d9d8455e00c3c40fe3bfc1` |
| `research-wiki/contribution-contracts/online-osd-policy-public-20261007.json` | `0ff90ba5e7d18e7df12bafb012488752e3f8af00b12e20cabcbd385ec04a4818` |
| `runs/online-osd-policy-public-20261007/accepted-decision-v1.json` | `160e82bbb83da1eb05b1e136bd6365236e334aa290ed171e6206d527e2a6f6a4` |
| `runs/online-osd-policy-public-20261007/delivery-obligations-overlay-v1.json` | `5533554583815813ec1451c84fb33bbbff7497890e7b5f330646c82fee4462de` |
| `docs/contracts/online-guessing-osd-policy-v1/contract-v1.md` | `ca6afb3d99a55e3ca2c1e34a928ac77f693b6066f386f58f1233883e0901e231` |
| `docs/contracts/online-guessing-osd-policy-v1/dependency-DAG-v1.json` | `eea555342753d1d94aceb2a24b2e56c1b35b14ab39297eed72981cbd4d7ea369` |
| `docs/contracts/online-guessing-osd-policy-v1/draft-statements-v1.lean.txt` | `420b8fc71d153519e452c5ba0211f0efe703bab93dd25dbfe38a3fab31525d3e` |
| `docs/contracts/online-guessing-osd-policy-v1/headers-v1.json` | `5a8a77de34420dff1c0ad1796f978e150b679dc96a2825c10b8af2cd5e656cab` |
| `docs/contracts/online-guessing-osd-policy-v1/public-context-v1.txt` | `aab4cd91a19313249489820f6306f694f58230162a6479edaa99fb51e80c4ab4` |
| `docs/contracts/online-guessing-osd-policy-v1/raw-statement-fingerprints-v1.json` | `dfd8c5388cc4046c6125314b498542d1e8254363e3bb5507d1e0eff71bcd2f52` |
| `docs/contracts/online-guessing-osd-policy-v1/semantic-signature-v1.json` | `24b87f916e34af8c3ef91fc8c4edee27e6a6fe091181fd95cd676bac6a6f5eb6` |
| `docs/contracts/online-guessing-osd-policy-v1/source-card-v1.json` | `ea6ca30268154ae7c197fcee73b15fb03bf436c49f8e0520029c400426bf10eb` |
| `runs/online-guessing-osd-policy-20261007/.gitattributes` | `705fd4d6451a31d36b3df7de96f83f30ac976c9b4a6d1e51671d8e2f33e2d0da` |
| `runs/online-guessing-osd-policy-20261007/00_context.md` | `571a6629a3091d61a8be166557173c784e704c67c1bc2cd81cbbb3717e84d70d` |
| `runs/online-guessing-osd-policy-20261007/actual-neutral-type-bridge-v1-01-exit.json` | `3b5c0f0bd9d0c36046dc0ba7d52a6e4d0446a76842d4b7ec0b2962e3b1bd6454` |
| `runs/online-guessing-osd-policy-20261007/actual-neutral-type-bridge-v1-01.log` | `008c2c3896b024144ea494034b19b21eb5ea7bd4c5e75aafb79da5c7c76c3267` |
| `runs/online-guessing-osd-policy-20261007/actual-neutral-type-bridge-v2-01-exit.json` | `5d213404bea4366f33b2bb430070ee6787bba2cf6b321407956c11ccc3b07c9c` |
| `runs/online-guessing-osd-policy-20261007/actual-neutral-type-bridge-v2-01.log` | `5488c68630f1863497a87871c5f86bb91450c58babb1d6a3bcf16473e70d9759` |
| `runs/online-guessing-osd-policy-20261007/architect-v1.md` | `ecc410ea29f8ce09ed9233bae04200f1dd48e92a8bde778f7689b51be7c544e9` |
| `runs/online-guessing-osd-policy-20261007/base-PR181-fresh-v1.json` | `cf5dc4d02990e7ae0d4b24ac449f90fb6a3b49690304c8d1d74b98f93178456f` |
| `runs/online-guessing-osd-policy-20261007/blind-packet-v1.md` | `31e2ec8f03e2442aa8709a4f5a16ed2d4cc95b4d9e3b0bc8bfb30492cca4a97b` |
| `runs/online-guessing-osd-policy-20261007/blind-packet-v2.md` | `e9501bd48f6f600470d8f7c7f637c6ce2d10f0ceba46c0b937e538601ad0cf95` |
| `runs/online-guessing-osd-policy-20261007/blind-receipt-v1.json` | `3e23c8d923d0208be13fd4b985e3e37ef4393a6be39f572fb50622e4377a2b05` |
| `runs/online-guessing-osd-policy-20261007/blind-reconstruction-v1.md` | `adef3270559baf2ef9b027677da5004bb5d4efe6f60315213fb90c4acbe3fb5d` |
| `runs/online-guessing-osd-policy-20261007/contract-resume-v2.json` | `2a66b8f2895626a6df99342ae0933216f9d8c966f9f62fab91ae3a7ec6ea2c67` |
| `runs/online-guessing-osd-policy-20261007/director-v1.md` | `7acfa40f167b5e5a20c32a3521559c9924002fd4d13aa6e4d96dc0d1aab1d09e` |
| `runs/online-guessing-osd-policy-20261007/draft-event-v1-01-exit.json` | `ca1434d1ae9506147e4045b78c4b8478ebdb4fc25fbbe87ef4ab71a7639d051b` |
| `runs/online-guessing-osd-policy-20261007/draft-event-v1-01.log` | `13c736a6caef1322c6c8fe4b7fe7d6f8d218dd573bb07a0280378e13652fb630` |
| `runs/online-guessing-osd-policy-20261007/draft-freeze-v1.json` | `7ede07989a13e704bd7c9faf1b68b7f1c1377811f895cc8818e170112671a542` |
| `runs/online-guessing-osd-policy-20261007/existing-canonical-headers-v1.json` | `986af56ef8e30e4e0b7f9ccefba51a3857a0e0279c4707f8cfb60c7030b7eb1d` |
| `runs/online-guessing-osd-policy-20261007/leaves/actual-neutral-type-bridge-v1.lean` | `7b18d1c0274f10c76c8b5b6fe1fdcf6736fe88852f8f12fc4cc35cb58837923e` |
| `runs/online-guessing-osd-policy-20261007/leaves/actual-neutral-type-bridge-v2.lean` | `268a56d6ce567698bbc6ec5faa7f43336f886b5c22d82fb61e954a599c65f535` |
| `runs/online-guessing-osd-policy-20261007/leaves/neutral-types-v1.lean` | `c8a77668566f1a7055003668919c90e65bb6dbcda550933dbe928d426f9dff6b` |
| `runs/online-guessing-osd-policy-20261007/leaves/neutral-types-v2.lean` | `48463e29a6ee46f991100b7ceb5434b59b9ed403d366e018f6b5ca4ede597076` |
| `runs/online-guessing-osd-policy-20261007/leaves/retrieval-probe-v1.lean` | `74f9baacebec27b98063e2bb95c824f12f31a302acf1798dfa26645ec3939be9` |
| `runs/online-guessing-osd-policy-20261007/local-semantic-search-v1-01-exit.json` | `82381f8c4dee5545d7746a3ee2e544a88df03b219a109537baf24d5236334153` |
| `runs/online-guessing-osd-policy-20261007/local-semantic-search-v1-01.log` | `34efceb78684665a1f78dc10022a72c2febf785633c4c0be4d6a570d7ffbceed` |
| `runs/online-guessing-osd-policy-20261007/mathlib-semantic-search-v1-01-exit.json` | `476319281b4ffbba3e08c0d2acb98b2b60de713c7d755bf0716b68359be991b8` |
| `runs/online-guessing-osd-policy-20261007/mathlib-semantic-search-v1-01.log` | `d6904072b6e66b7c7e0f80850e3e7125cd874301104d352d674ceb8010044ed4` |
| `runs/online-guessing-osd-policy-20261007/native-new-task-v1-01-exit.json` | `e0902387130dd27bbc7af42411c5f0cd5bbf015d7f2558c59d503757b4252641` |
| `runs/online-guessing-osd-policy-20261007/native-new-task-v1-01.log` | `f15fd8ae1bd0a68ba5cc6e01900987415a935f6ad20961cece0fa1708a3efb1e` |
| `runs/online-guessing-osd-policy-20261007/neutral-repair-v2.json` | `d186deac300222a6d7020cebdc134af3393bb4afeda1182edccf434e021b5d6c` |
| `runs/online-guessing-osd-policy-20261007/neutral-to-actual-map-v1.json` | `0f01aabebf4f92bbd9bd66a6378c9b9d0f4db3c1bceade55fafd3e9dfc6b96b5` |
| `runs/online-guessing-osd-policy-20261007/neutral-types-v1-01-exit.json` | `1862f1a90d42430d6c4687fab50266cc1fb93f29fa87578cadf0343397c92f9b` |
| `runs/online-guessing-osd-policy-20261007/neutral-types-v1-01.log` | `dab0a237c976c6d67f7adb469f1b9e2a9c7dcfd67a0f82d2a2fdeb50d9ae3872` |
| `runs/online-guessing-osd-policy-20261007/neutral-types-v2-01-exit.json` | `27e90ce13aa05694ac625108d2076d90e58058cf218d57c884780dc0b1687506` |
| `runs/online-guessing-osd-policy-20261007/neutral-types-v2-01.log` | `d5cfeced48ad86a9963be5663ead11cdc5f4bf44fa49663aa9ceb66cb683d3d5` |
| `runs/online-guessing-osd-policy-20261007/prepare-contract-v1-failure.txt` | `08f2aab0110ac7e324b9eda5d3a40e365e38f402cc965b76faa8b7e5a25758a2` |
| `runs/online-guessing-osd-policy-20261007/retrieval-probe-v1-01-exit.json` | `ae37656cedf3a1a73297e5d236fc60f3cb9e1ab9de30866b58393061ba0e4406` |
| `runs/online-guessing-osd-policy-20261007/retrieval-probe-v1-01.log` | `6c3f1afbbfc870c29610c11799528e94bd2f3d2d91801025974130f8245303b7` |
| `runs/online-guessing-osd-policy-20261007/retrieval-record-v1-01-exit.json` | `ea5a25cc0532a4a92a925c2e3af987cd8f5b420e354a451a8adc12c6c280c61f` |
| `runs/online-guessing-osd-policy-20261007/retrieval-record-v1-01.log` | `3d01c9d3180176e17a5bf27108e5a97cf2b6aff5643c77d1eaf91892c518a930` |
| `runs/online-guessing-osd-policy-20261007/retrieval-v1.json` | `3caca075e549995199350f20e5725159bb4b748d09cac21b77bf42a878e89f0e` |
| `runs/online-guessing-osd-policy-20261007/reuse-decision-v1.md` | `85de97315bc4b2f228771aaa1f88f4ecb84da05c56132bc467925110842f9e0c` |
| `runs/online-guessing-osd-policy-20261007/review-scope-v1.md` | `800edba682c83c83fff18412e0c37c32798e2f57ea2ad46202cb8706521d0c41` |
| `runs/online-guessing-osd-policy-20261007/source-pdf13-v1.png` | `228ea769f7cec2ba5fe2d5e416b4ac5f60c93ec38f83a2dd7a537c2a51d2c5f4` |
| `runs/online-guessing-osd-policy-20261007/source-pdf13-v1.txt` | `b16d82b563558afaaa14776c6015a78be9e0daa3d888a9a0593c057a54d2288b` |
| `runs/online-guessing-osd-policy-20261007/source-pdf14-v1.txt` | `3f9d01aee6e81504b7ca2ef0d9657bc1ee30f36eb54a957b8018c4d0c3e2ac66` |
| `runs/online-guessing-osd-policy-20261007/source-pdf15-v1.txt` | `037b6d907a868c339b881162333f6e56352cbebf285902eb6ed628ff4f8bd947` |
| `runs/online-guessing-osd-policy-20261007/source-pdf27-v1.png` | `6df81ff53a64e9721ff400bcd3b41566aabdfacbe59da1eaf8b1331929836d49` |
| `runs/online-guessing-osd-policy-20261007/source-pdf27-v1.txt` | `aed61245f25b365224da1ea1ca3a2d3f8439365707e6cca6e1f08b05087eaf42` |
| `runs/online-guessing-osd-policy-20261007/source-pdf28-v1.txt` | `a9d4910e2c687a25babd24d5b4c30f4e6c4d1fdc4018c29ad239c327bacfd87c` |
| `runs/online-guessing-osd-policy-20261007/source-pdf31-v1.png` | `c1cb49ac038e88055cb4651f70755c456ccbc817a70c5a06c818f5967676bfa2` |
| `runs/online-guessing-osd-policy-20261007/source-pdf31-v1.txt` | `7709a706da7b5320555f5ef19e07fa798affde6a077363425b929c07af0b9a99` |
| `runs/online-guessing-osd-policy-20261007/source-pdf32-v1.png` | `ef5bdf4653f3d3a12dfd1809478e362e034bfb6b184a88c0ed199d98bd115b22` |
| `runs/online-guessing-osd-policy-20261007/source-pdf32-v1.txt` | `3cb9fb0c18b5b9c63c280944188334305bd9a042fed58fad67e797b6d7b76bdd` |
| `runs/online-guessing-osd-policy-20261007/source-pixel-review-v1.json` | `28081790fe96bbb1dee6ecbe80e7b4cb6b6b0e305a09588d9e3abde893672697` |
| `runs/online-guessing-osd-policy-20261007/source-render-v1.json` | `a392a97e03651879b7e6b905910ec83168c4ed8e045f3fa0e5b30cf006d65cd1` |
| `runs/online-guessing-osd-policy-20261007/type-bridge-v2.json` | `8209100ec10a22521af40e64e86e468a04f178e389ad795db2eedf2aba330ff7` |
| `runs/online-guessing-osd-policy-20261007/worktree-audit-v1.json` | `cf41d07ec439e9e8d8a0c4d8082ac25fc6be36d6fbf2e400d1d6b945fc2b3000` |
| `tasks/ONLINE-GUESSING-OSD-POLICY-20261007.md` | `0bb21ef080ae5bc1f35781c2119824424a48819abba814a59259b3b17104812c` |
| `conversion-windows/ONLINE-GUESSING-OSD-POLICY-20261007.md` | `ca6afb3d99a55e3ca2c1e34a928ac77f693b6066f386f58f1233883e0901e231` |
| `proof-obligations/ONLINE-GUESSING-OSD-POLICY-20261007.md` | `dc9d3091e207b46c36675ce6f1a186f7b4e53f15fd1da47b5fa7a9cc8ec96724` |
| `proof-obligations/ONLINE-GUESSING-OSD-POLICY-20261007.json` | `487eda1be3a39881443be42b2e8557cc9aebd0611ceda4b62c31613f576e8540` |
| `runs\online-guessing-osd-policy-20261007\source-contract-review-packet-v1.md` | `7eebc69d779b8ebac20bdf4e07b0b9adfc9c2fad7dcf6950defef81b94c87614` |
| `runs\online-guessing-osd-policy-20261007\source-contract-review-inputs-v1.json` | `4c80cc827655ece3e7c8578ee9cee66ee5f5e4d9b0bd2c05beb213b640cfa8d3` |
| `../research-online-ogd/tmp/pdfs/orabona-v10.pdf` | `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17` |
