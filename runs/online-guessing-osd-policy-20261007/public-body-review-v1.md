# Actual public-body review: absolute-loss history-policy OSD

**Verdict: accepted-with-explicit-delta, BODY scope only.** Four new public proof bodies and the entire new canary were independently inspected. No blocking mathematical or metadata repair was found. Reader obligations R1–R8 remain mandatory and are not discharged by this review.

Actor `/root/source_reviewer` is distinct from root formalizer and osd_blind decoder. Requested GPT-6 Astra / medium, runtime unverified. Prior staged source-review history, including this package CONTRACT review, is disclosed; this is neither blind nor external/human review. Existing dependency evidence is used within this bounded review, not recursively reaccepted.

All 181 current fixed raw inputs and all 87 original CONTRACT rows match independent SHA-256 recomputation. The pinned PDF was freshly rehashed to cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17 and source PDF27/31/32 text reread. Original source images were actually viewed in the separate CONTRACT stage; no new pixel inspection is claimed here. The source gives the absolute-loss full support branches and asymptotic upper regret, with equation2.1 supplying the D=G=1 finite specialization. The positive known horizon and same-rate trajectory remain explicit.

## Four targets: seven slots and actual producers

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

Actual body: The proof applies the existing full global absolute-support norm producer to hlegal t ht. No norm bound is assumed. Arbitrary x1/y/eta scope is maintained.

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

Actual body: The proof unfolds actual output_succ and the shared unit-interval projection, then converts scalar smul to multiplication. It proves the full identity without needing legality.

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

Actual body: The proof derives interval diameter one from both interval inequalities, rewrites only the identical rate 1/(1*sqrt T), supplies actual proper/subdifferentiable absolute losses and selected_bound to shared regret_tuned with D=G=1, then unfolds regret and uses EReal.toReal_coe. No infinite fallback, assumed regret, unrelated path or comparator-dependent run enters.

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

Actual body: The proof obtains reciprocal-sqrt convergence, intersects the eventual smallness event with T>0, invokes the new finite theorem on the same horizon-specific legal run, divides by nonnegative T, and proves sqrt(T)/T=1/sqrt(T) using positive denominators. Only an upper inequality is concluded; no lower bound or signed Tendsto zero is inferred.

## Genuine canary and dependency scrutiny

The complete canary has **47 declarations: 36 proofs, 6 definitions and 5 abbreviations**. Together with four public proofs this gives 51 named checks, not 51 canary declarations. Both rfl initial-output proofs are included. All 36 original canary proof headers match the repaired bodies; all four production headers match the frozen complete contracts. No new production definitions were introduced.

The policy recovers nonnegative source labels from the current finite loss at zero and uses the first past loss only at a kink. Its legality proof handles both strict sign branches and both closed-interval endpoints at equality, then policy_legal supplies actual history at each played query. A and B yield (.5,0,.5,0,.5) and (.5,1,.5,1,.5); at time2 current loss and point agree, while past loss produces supports +1 and -1 and different next outputs. Thus history sensitivity is demonstrated, not an unused policy argument.

Actual arithmetic gives A regret against 1/4 at horizon4 equal 1/2, B regret zero, A selected energy4 and terminal squared distance1/16. The canary invokes the real shared sharp fixed theorem with the negative terminal term; its right side is1. It separately invokes the NEW all-comparator tuned theorem, with eta=1/2=1/sqrt4, and the NEW eventual-family theorem with legality proved for every horizon. No supplied desired inequality replaces these calls.

The off-path counterexample uses loss(-1) at feasible .5: the policy selects -1 although the full global support is {1}. The actual source streams nevertheless have proved legality. Hence optional OracleLaw is demonstrably not a hidden assumption. Future negative labels/rates after time4 preserve output4 through strict-prefix equality. Zero rate with initial2 is tested only as a clamp identity, not a legal initialized performance run. T=0 remains excluded by the tuned theorem and discarded in the eventual proof; this canary does not claim a new tuned T=0 performance theorem.

The reused Nat.rec/Fin.snoc definitions use finite prior losses and current loss for selection, and actual projection for the next output. The selected norm, legality, regret and tuning all refer to the same eta-dependent run. Properness and real finiteness are produced for absolute losses; toReal_coe is used on genuine finite embeddings. The shared tuning proof first uses the sharp fixed result and only then drops a nonnegative terminal term. This audit does not certify independent choice of externally supplied policies/rates/initialization, randomized laws, an executable oracle, or one anytime path.

## Actual evidence and retained failures

Public focused build passed with3324 jobs; repaired whole-canary focused build passed with3325 jobs (caches/replayed dependencies included). The recorded actual public-type, kernel and export commands exited0. I parsed all51 unique multiline kernel records: each lists only propext, Classical.choice and Quot.sound; no sorryAx. Four current raw/native guards report matching statements and preserved literal assumptions. Guards are not compilation or semantic proofs.

The actual compiled TEST environment has51 selected nodes (40 proofs,11 definitions including abbreviations),4689 recorded direct edge occurrences, and all26 prescribed VALUE dependency pairs were independently checked against node value_dependencies. Summing separate deduplicated type/value dependency arrays yields a different count5408 and is not the edge-table measure; neither is a full registry or combined-root graph claim.

The first literal-source-assumption guard failed on prose while the statement hash was already identical; corrected literal hlegal/ht guards preserve the mathematics. Initial canary build failed on alias/higher-order rewrite matching, a definitional selected-rule equality and natural-cast sqrt simplification. The original failed log/snapshot remains. Repairs change tactic bodies only, preserve all canary headers and the public body. My first local kernel-log parser also missed a multiline record; a whitespace-aware read found all51 unchanged actual records. No evidence file was altered to obtain this result.

## Remaining reader and package boundaries

- **R1 (future mandatory)**: Attribute one printed Example2.32; identify two helpers and the exact finite/one-sided eventual refinements rather than four printed results.

- **R2 (future mandatory)**: State the real interval game, feasible initial point/played labels/comparators, positive known horizon and eta=1/sqrt(T); retain labels even if unused in algebra.

- **R3 (future mandatory)**: Explain actual finite-history/current-loss policy inputs and output-before-current-feedback order; no certified independence of externally chosen p, eta or initialization, executable oracle or randomized-law guarantee.

- **R4 (future mandatory)**: Show played global support membership and the entire shifted support sets, including closed [-1,1] at equality. Optional universal off-path OracleLaw is not a performance premise.

- **R5 (future mandatory)**: Disclose selected_bound and clamp broader algebraic scope; unconditional clamp is not a performance guarantee for illegal feedback.

- **R6 (future mandatory)**: Present same-run all-comparator finite sqrt(T) bound, D=G=1, genuine finite loss conversion and actual selected norm producer; do not supply the desired bound as a premise.

- **R7 (future mandatory)**: State one-sided eventual signed average bound for separate known-horizon runs, not signed convergence to zero, absolute Big-O, future-energy optimization or anytime performance.

- **R8 (future mandatory)**: Separate reused declarations from four prospective new proofs, dependency readiness/type equality from proof/gate completion, and bounded package from required remaining canonical migration/maintext/Chapter1/2/appendix/whole-Goal work.

Mathematical repairs: none. Blocking metadata repairs: none. Required BODY repairs: none. Combined root/Tests/full harness, reader integration, site/registry/FINAL, immutable acceptance and actual PR delivery remain separate and unaccepted here. Chapter/whole Goal/main/merge/live completion is not claimed.

## Exact raw inventory

Every fixed row was read for raw-byte verification. Semantic scrutiny focused on the entire current public and canary source, source text, exact contracts/context, recorded build/type/kernel/guard evidence and actual selected graph; inventory inclusion is not blanket reacceptance of every historical dependency proof.

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
| `BanditRLProof/OnlineGuessingSubgradientPolicy.lean` | `ed32d846509d0dc34eb05ce6fad5d3af8aa6dbf92a8c8a78cc8859b0e42e6b0e` |
| `Tests/OnlineGuessingSubgradientPolicyCanary.lean` | `16591f7ee319275d2fe9399d6ad89b2aec179b97f0c80f12d5c2633428074658` |
| `proof-obligations/ONLINE-GUESSING-OSD-POLICY-20261007-proving-v1.json` | `ea5a25f3fc240504a6ef9c31ce4ecdcd5b96ec0c8422e8150ac8cb410b8ad14a` |
| `research-wiki/retrieval-index/online-guessing-osd-policy-20261007.md` | `1300d1345cfbbd2a692e90f6ef7f10f3c42df33e694e43d7f20d6d6ba58b5661` |
| `runs/online-guessing-osd-policy-20261007/all-axioms-v1-01-exit.json` | `fad2bdc7f8b84b9425d81b054ea93f4b3f64af625abdacfd74fa98651d57993e` |
| `runs/online-guessing-osd-policy-20261007/all-axioms-v1-01.log` | `1d197d8fa510f034de6c5778247c92033ab22416e1508add6b76d6c7fed025c7` |
| `runs/online-guessing-osd-policy-20261007/all-public-types-v1-01-exit.json` | `482f67fb6eb0b98afad76864eaaa05ef53dd70cdea6605286f5f0a6f0e3d4ea9` |
| `runs/online-guessing-osd-policy-20261007/all-public-types-v1-01.log` | `24c3a6b105333e174128c22844865eb5b29dd4acc623b570738eaf61f339ff28` |
| `runs/online-guessing-osd-policy-20261007/body-bindings-v1.json` | `0ab31c06ba0e87cb3bae93a0ed7d9d15f35365f18b87e98d20335d1203062c42` |
| `runs/online-guessing-osd-policy-20261007/body-safe-example_2_32-v1-exit.json` | `4645eb42f5140d9f9219f23b1239d160932dce43b03ea31c310f8102d6e927ff` |
| `runs/online-guessing-osd-policy-20261007/body-safe-example_2_32-v1.log` | `0ba32d436de3ac5ae4a855c336b767f6c2c28c5c30a2560f317e43cbc00a19ab` |
| `runs/online-guessing-osd-policy-20261007/body-safe-example_2_32_average_eventually-v1-exit.json` | `3aa6667b5d28ecec948049d2fd088eaf46e0e8c5259549e016454f1b867cafc1` |
| `runs/online-guessing-osd-policy-20261007/body-safe-example_2_32_average_eventually-v1.log` | `2a83890481ff232d2b7adc6a8dd87773bf1514693c8d97fac546ef943068257e` |
| `runs/online-guessing-osd-policy-20261007/body-safe-selected_bound-v1-exit.json` | `7945859c78c248911d3ce685023318a3c77699625b141c89a435730603909887` |
| `runs/online-guessing-osd-policy-20261007/body-safe-selected_bound-v1.log` | `53b47a8e6f99b6d21b0140e40439053549c659e48ece6f2eca52bfcc0e7647c3` |
| `runs/online-guessing-osd-policy-20261007/body-safe-step_clamp-v1-exit.json` | `e7c1eab83b27d5d7c5d9e697225b8a2c056e532bc3b088b3b6fe73b1ce7fd013` |
| `runs/online-guessing-osd-policy-20261007/body-safe-step_clamp-v1.log` | `a54a60c5a7cc89cedc33666b144b91dfa5e5bb667069fc65b2804470b010eee7` |
| `runs/online-guessing-osd-policy-20261007/canary-body-repair-v2.json` | `355d4bdd98ace21928edd7c8725c8c494031fa0adff3c9e98c6cb469a78576b0` |
| `runs/online-guessing-osd-policy-20261007/canary-plan-v1.md` | `e8f1963e701afa218f3ef73f01efa8a9a5f8ce9c3ee8a8844db29f420de5e442` |
| `runs/online-guessing-osd-policy-20261007/candidate-event-v1-01-exit.json` | `495c6453d3cc53fa1858dcbdef354b9f8c09789b96df7915c5744672c465a962` |
| `runs/online-guessing-osd-policy-20261007/candidate-event-v1-01.log` | `13a0ab1af42370cfbc89670e54af3025127029f066e2df50d1324614ebcfb57f` |
| `runs/online-guessing-osd-policy-20261007/compiled-value-graph-v1-01-exit.json` | `377aa2f72a2daee9a5509eaac3d7d49156ceb8023a5c67d276bbc3c67ee70413` |
| `runs/online-guessing-osd-policy-20261007/compiled-value-graph-v1-01.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `runs/online-guessing-osd-policy-20261007/compiled-value-graph-v1.json` | `e75eec874ab1d7c438fd5acc9a3e1381339c3f45ad5c26668c5efd52283e4b0c` |
| `runs/online-guessing-osd-policy-20261007/compiled-worker-trial-v1-01-exit.json` | `71b5d9b725861153afcfa3b52db2f8976e5d0df0369e422b5cf1665bfd99075a` |
| `runs/online-guessing-osd-policy-20261007/compiled-worker-trial-v1-01.log` | `d45db130bbe85982b24ed7e296e7d645fa58497dc30f41b93c478567618b74ad` |
| `runs/online-guessing-osd-policy-20261007/first-leaf-guard-repair-v2.json` | `5ca8a9442501ff0fbcbeb8759ce61a0452dd013ac2f34374ec86bb710fdf3187` |
| `runs/online-guessing-osd-policy-20261007/first-public-leaf-fence-v1-01-exit.json` | `e7af00ffe982805a00ef8cc90fc8ee896e379324b2f8f5326145da36ca8deb0c` |
| `runs/online-guessing-osd-policy-20261007/first-public-leaf-fence-v1-01.log` | `aafa8df4f2cc6f8ea9c1b14161a8df6d623640f156f1d3af85bde3298e264601` |
| `runs/online-guessing-osd-policy-20261007/first-public-leaf-fence-v2-01-exit.json` | `18ec3b228e0323013dc84b73066344df921754e1e4a44917155e01ed476ca0ee` |
| `runs/online-guessing-osd-policy-20261007/first-public-leaf-fence-v2-01.log` | `fb7a151cc47c6e6caf53820a171071b89df2e4059765da7a3524286fa4c1b377` |
| `runs/online-guessing-osd-policy-20261007/first-public-leaf-focused-v1-01-exit.json` | `314eaae94b8952b3ba4920f4f6a0ddee67926d3ea843c0616f0e9d1787bfa0e9` |
| `runs/online-guessing-osd-policy-20261007/first-public-leaf-focused-v1-01.log` | `ef1e53cfacaaa5cdee6997a41e066da16bbdfb434fd8e237a7b159167d8f9498` |
| `runs/online-guessing-osd-policy-20261007/first-public-leaf-safe-v1-01-exit.json` | `2aed8e448aeeaabdb0e87476f9f5ffd6a84ff40a6adacaef2f06b03fc9fd63d5` |
| `runs/online-guessing-osd-policy-20261007/first-public-leaf-safe-v1-01.log` | `414ad963cdfbe488a28ba0057608ac152d9f8cc1c97fdcf9e224550526c6b1d6` |
| `runs/online-guessing-osd-policy-20261007/first-public-leaf-safe-v2-01-exit.json` | `71bd66cabeb75443c19d5ca5d2ed7a88479bfb3a7166e82e30288cbce9780315` |
| `runs/online-guessing-osd-policy-20261007/first-public-leaf-safe-v2-01.log` | `53b47a8e6f99b6d21b0140e40439053549c659e48ece6f2eca52bfcc0e7647c3` |
| `runs/online-guessing-osd-policy-20261007/full-public-fence-example_2_32-v1-exit.json` | `74f447f2034205948878acc984aaf8ff1b1e0c5ab6bd6e78edb858a942c5c776` |
| `runs/online-guessing-osd-policy-20261007/full-public-fence-example_2_32-v1.log` | `65b3b4395c1defe7a535efd0571b705f7be8caac61dd2b71fd24b8753d1bcf83` |
| `runs/online-guessing-osd-policy-20261007/full-public-fence-example_2_32_average_eventually-v1-exit.json` | `afe6acbb6081c7d2dea78a7f56f461b4bf0c0cb0cc059212c523f2507e7c55d9` |
| `runs/online-guessing-osd-policy-20261007/full-public-fence-example_2_32_average_eventually-v1.log` | `4da828a84077c710e8c5fe985e96bbd03093ee6ca23a962fa6a519dc2f3832c2` |
| `runs/online-guessing-osd-policy-20261007/full-public-fence-selected_bound-v1-exit.json` | `6d6e76333f02176cacd146858123c0894d72dba89eeb81710d52cda1b7ab3a73` |
| `runs/online-guessing-osd-policy-20261007/full-public-fence-selected_bound-v1.log` | `685655db4b5b7a0b49e72be1adc81f40d9c3271457313bbe532c12b24b24cd54` |
| `runs/online-guessing-osd-policy-20261007/full-public-fence-step_clamp-v1-exit.json` | `3d310ce5012b8e52b0907d038dbb0761f3ad9dcb3a9a75f254bc1755d3d9e255` |
| `runs/online-guessing-osd-policy-20261007/full-public-fence-step_clamp-v1.log` | `4e047850e51242b43b5ef60ccb62212447adbfe3baffc48e1ac630112db3f4f5` |
| `runs/online-guessing-osd-policy-20261007/full-public-focused-v1-01-exit.json` | `22be442aad42c19b5c49e7334df4b59f17f808b3611e1af4092f754780107b70` |
| `runs/online-guessing-osd-policy-20261007/full-public-focused-v1-01.log` | `f9888f4d171d281f7bf3ca5d8db0b9276b662d7c06b28c8cf383de444bdc6808` |
| `runs/online-guessing-osd-policy-20261007/full-public-safe-example_2_32-v1-exit.json` | `d86cbe718a3e65ee9785facad757391b75413aea8acefe6150ff49dad78e251d` |
| `runs/online-guessing-osd-policy-20261007/full-public-safe-example_2_32-v1.log` | `0ba32d436de3ac5ae4a855c336b767f6c2c28c5c30a2560f317e43cbc00a19ab` |
| `runs/online-guessing-osd-policy-20261007/full-public-safe-example_2_32_average_eventually-v1-exit.json` | `93a4aece6683ebb06b5348f05233d7ca5521f51767304a6d9eb19ec587780d56` |
| `runs/online-guessing-osd-policy-20261007/full-public-safe-example_2_32_average_eventually-v1.log` | `2a83890481ff232d2b7adc6a8dd87773bf1514693c8d97fac546ef943068257e` |
| `runs/online-guessing-osd-policy-20261007/full-public-safe-selected_bound-v1-exit.json` | `6cfbc862b3f1e9f62bbf512f45a41b7a6bdae90b3740711a5f24155ab3a736bf` |
| `runs/online-guessing-osd-policy-20261007/full-public-safe-selected_bound-v1.log` | `53b47a8e6f99b6d21b0140e40439053549c659e48ece6f2eca52bfcc0e7647c3` |
| `runs/online-guessing-osd-policy-20261007/full-public-safe-step_clamp-v1-exit.json` | `ec936a2d2ba222b66889f2209e1578be7496b5924fe8726171c9ecdbe8c53196` |
| `runs/online-guessing-osd-policy-20261007/full-public-safe-step_clamp-v1.log` | `a54a60c5a7cc89cedc33666b144b91dfa5e5bb667069fc65b2804470b010eee7` |
| `runs/online-guessing-osd-policy-20261007/leaves/all-axioms-v1.lean` | `b824f846e804b31252c29fa7a32599858767efedeb605bccb543010da28c7b0a` |
| `runs/online-guessing-osd-policy-20261007/leaves/all-public-types-v1.lean` | `86abfe0b2f1b3db7240bf9b8ce518a5daf1843ca3ea92d76fda0154dc36731cf` |
| `runs/online-guessing-osd-policy-20261007/leaves/export-actual-dependencies-v1.lean` | `622469ecca60c805ce05e069ff009c620e4bf8558b85a24c185d4dd7e07e13c5` |
| `runs/online-guessing-osd-policy-20261007/leaves/first-public-leaf-v1.lean.txt` | `94ed580049a9af6ad806ab00ac4db1f034d1fe1ff08d93456cb9387476b75b7b` |
| `runs/online-guessing-osd-policy-20261007/leaves/full-public-body-v1.lean.txt` | `ed32d846509d0dc34eb05ce6fad5d3af8aa6dbf92a8c8a78cc8859b0e42e6b0e` |
| `runs/online-guessing-osd-policy-20261007/leaves/whole-canary-before-first-build-v1.lean.txt` | `46b638199eb315a5c31e24c66cf3beb62538831b1894e328edb53eb235a9e3af` |
| `runs/online-guessing-osd-policy-20261007/leaves/whole-canary-body-v2.lean.txt` | `16591f7ee319275d2fe9399d6ad89b2aec179b97f0c80f12d5c2633428074658` |
| `runs/online-guessing-osd-policy-20261007/memory_digest.md` | `0650e62c43b6573c6b81144b410a7eb06d4d604747128a6a142061dc7ebb0f3c` |
| `runs/online-guessing-osd-policy-20261007/native-public-fences/example_2_32-full-v1.json` | `65b3b4395c1defe7a535efd0571b705f7be8caac61dd2b71fd24b8753d1bcf83` |
| `runs/online-guessing-osd-policy-20261007/native-public-fences/example_2_32_average_eventually-full-v1.json` | `4da828a84077c710e8c5fe985e96bbd03093ee6ca23a962fa6a519dc2f3832c2` |
| `runs/online-guessing-osd-policy-20261007/native-public-fences/selected_bound-full-v1.json` | `685655db4b5b7a0b49e72be1adc81f40d9c3271457313bbe532c12b24b24cd54` |
| `runs/online-guessing-osd-policy-20261007/native-public-fences/selected_bound-v1.json` | `aafa8df4f2cc6f8ea9c1b14161a8df6d623640f156f1d3af85bde3298e264601` |
| `runs/online-guessing-osd-policy-20261007/native-public-fences/selected_bound-v2.json` | `fb7a151cc47c6e6caf53820a171071b89df2e4059765da7a3524286fa4c1b377` |
| `runs/online-guessing-osd-policy-20261007/native-public-fences/step_clamp-full-v1.json` | `4e047850e51242b43b5ef60ccb62212447adbfe3baffc48e1ac630112db3f4f5` |
| `runs/online-guessing-osd-policy-20261007/proof-obligations-candidate-v1.json` | `ff478e3f18aca33189d06059e6cab73372beba395557b8776947240130dd2685` |
| `runs/online-guessing-osd-policy-20261007/proof-repair-record-v1-01-exit.json` | `b9d15e64b2052ea2bf3d738123a87be8fad6f292a603c63d126e1c7fffa80b98` |
| `runs/online-guessing-osd-policy-20261007/proof-repair-record-v1-01.log` | `11881a1a361655d62fd5eb81105a6c80e3024bc11bfcaac4a323dd128045abdd` |
| `runs/online-guessing-osd-policy-20261007/proof-repair-resumed-v1-01-exit.json` | `30c395dbc5551a77d7236d0ec6aa640506a166809c2126d68a4f545efdbb89b1` |
| `runs/online-guessing-osd-policy-20261007/proof-repair-resumed-v1-01.log` | `916a3f967c7447b1c111a1ca013c33f50c1afbd9c8c683e012cf6c461334b396` |
| `runs/online-guessing-osd-policy-20261007/proving-event-v1-01-exit.json` | `d46db33bb16f835a01702098d063b49a979acd32f5fe809f2d4219f0a01c9d22` |
| `runs/online-guessing-osd-policy-20261007/proving-event-v1-01.log` | `b02968859145f1374bdb1d0d50c856d1b6a7deba06ecf069296aafde472219e0` |
| `runs/online-guessing-osd-policy-20261007/proving-terminals-event-v1-01-exit.json` | `f8e1eb1e117f193fd0a6f6a7a45308945724fe948011ebf14ef64e165457a7c3` |
| `runs/online-guessing-osd-policy-20261007/proving-terminals-event-v1-01.log` | `b8eb81a9d61d84ca732b610427d7cde7020023e0dcf5e2a49ff78c29113b63b2` |
| `runs/online-guessing-osd-policy-20261007/public-canary-focused-v1-01-exit.json` | `5b7ac114adedf279a50bab7057895dbd38dee6ceeac7479b6c67cf01a590b2bc` |
| `runs/online-guessing-osd-policy-20261007/public-canary-focused-v1-01.log` | `0bff11ba2c0ef244a60fd658e7ccba77db8d9b2a1fd37bf02920b0bcd74bea30` |
| `runs/online-guessing-osd-policy-20261007/public-canary-focused-v2-01-exit.json` | `d0acb8015f7f1a561123d8ee03415d05b862c643c9698622914b9412dd723214` |
| `runs/online-guessing-osd-policy-20261007/public-canary-focused-v2-01.log` | `cec47e265665a94dc21a1f805ab3c7a541983e30753b6e9c410b8070fd76a522` |
| `runs/online-guessing-osd-policy-20261007/public-named-declarations-v1.json` | `78b71431608ba3f90d79ac8ff5570c206b68a430e1ab366303975db0dd1ded80` |
| `runs/online-guessing-osd-policy-20261007/public-terminal-focused-v1.json` | `cf92cd6af01c018e484fbf6ef368de44ceaabcf496a3b348d5e6a9b961f6f1cc` |
| `runs/online-guessing-osd-policy-20261007/source-contract-receipt-v1.json` | `ea1f272bb63e1cfb19ab78a4cc0c26a7fbf802967b7b104b9af24b7f85668640` |
| `runs/online-guessing-osd-policy-20261007/source-contract-review-inputs-v1.json` | `4c80cc827655ece3e7c8578ee9cee66ee5f5e4d9b0bd2c05beb213b640cfa8d3` |
| `runs/online-guessing-osd-policy-20261007/source-contract-review-packet-v1.md` | `7eebc69d779b8ebac20bdf4e07b0b9adfc9c2fad7dcf6950defef81b94c87614` |
| `runs/online-guessing-osd-policy-20261007/source-contract-review-v1.md` | `4536a18075e1b3286940e3036fee7618d719d8482806ea8ae97f600ee06eeac7` |
| `runs/online-guessing-osd-policy-20261007/stabilized-contract-v1.json` | `902a323535cfb5a4326dcd0936ca4fceae37eb6e945a3935e5649079e306c9d9` |
| `runs/online-guessing-osd-policy-20261007/stabilized-event-v1-01-exit.json` | `5631d37cb8a30482fb243445ff78be2eafe2c7c941ec34ea7a41c2db7b172187` |
| `runs/online-guessing-osd-policy-20261007/stabilized-event-v1-01.log` | `216a8cb2c4e14cb554612ddff551f9552ee385c851581e02baaf9533e33bc207` |
| `runs/online-guessing-osd-policy-20261007/value-pairs-before-first-export-v1.json` | `e17340c202c31ca594b8e7fe7afc9e3f4a3368cedd41837d56e265a9ae0712fc` |
| `runs/online-guessing-osd-policy-20261007/worker-first-leaf-v1.md` | `1791543cc108d8ff4f31fc9e596ec371d5f48b1448101b91c8eb28de8ffa9746` |
| `runs/online-guessing-osd-policy-20261007/worker-terminal-v1.md` | `2155fc580d27eaf973164d2960f644d9bb6de8846de85c7e14d1fe585fc97a0f` |
| `runs\online-guessing-osd-policy-20261007\body-review-packet-v1.md` | `c7b697bd7de53c76b17a5ec0c2bb235a2fea820fe47c25e33a074fde9522dbf0` |
| `runs\online-guessing-osd-policy-20261007\body-review-inputs-v1.json` | `95de0395eb8b18b5335005c85b88b015440589217b771396ee528f9a9ee37475` |
| `../research-online-ogd/tmp/pdfs/orabona-v10.pdf` | `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17` |
