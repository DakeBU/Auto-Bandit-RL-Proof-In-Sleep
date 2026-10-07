# Current linearization-public CONTRACT review v2

**Verdict: accepted-with-explicit-delta, CONTRACT stabilization only.** No blocking mathematical or metadata repair found in the effective v2/v3 packet. Future R1–R8 reader obligations remain mandatory and are not discharged here.

Actor `/root/source_reviewer`; requested GPT-6 Astra / medium, runtime_model_attested=false. Prior staged source-review history is disclosed. Root formalizer and osd_blind are distinct automated roles; this is not blind, human, external or runtime independence attestation.

All159 fixed inputs independently raw-hashed before and after. Original PDF SHA256 freshly confirmed `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17`. Actually viewed bound source pixels13/31/34; reread original PDF28 proper/global subgradient definition, PDF31 transfer/lemma and PDF34 Section2.3. The source sums actual support gaps on the SAME outputs and explicitly denies universal optimality of the reduction. No IID/probability premise is imported from the initial illustrative game.

All18 complete effective headers-v2 mechanically match actual public declaration headers. Original raw v1 extractor stopped at named argument E:=E and is not the accepted target. The later helper's nonexistent actual-context-v2 filename is auxiliary failure, repaired by using unchanged actual-context-v1. Retained errors do not count as mathematical progress. Neutral v3 actual elaboration exit0/10.312s and18 full closed-proposition rfl identities exit0/10.641s establish the supplied renaming/type bridge only, not proof validation or literature fidelity. Read the complete decoder NL/LaTeX, exact scoped definitions and actual full public module as contradiction/interface evidence; existing bodies predate this draft and receive no fresh BODY acceptance.

## Complete context and source deltas

The shared real finite-dimensional inner-product scoped E models source R^d, including zero dimension. Domain has nonempty closed convex carrier, no boundedness. No extra supplied CompleteSpace, positive dimension, gradient bound or learning-rate requirement is added. Intrinsic aliases/definitions can have weaker inferred class needs than this supplied scoped context; do not advertise the terminal scope as the minimal binder of every definition.

LinearPolicy accepts only t and Fin t vectors; Feasible quantifies ALL such histories. outputHistory reconstructs A at each strict vector prefix, including current output at last t. history is actual Nat.rec from Fin.elim0 appending p's current selection by Fin.snoc. p receives exactly finite past WHOLE losses, reconstructed outputs through current output, and current WHOLE loss. No u or B input. output=A(actualhistory); selected is this same p call. linearRun feeds A strict prefixes of g; linearLoss is the real inner product. regret is the finite sum of real projections of losses, whose faithful interpretation requires finiteness supplied by regularity/global supports.

Regular/SubdifferentiableOn means proper AND nonempty GLOBAL supports at every feasible point, not an assumed convex-regret inequality. Source properness is nowhere-bottom plus finite ambient witness. Given actual support at an ambient x, that witness rules out top at x, even outside V; feasible comparator has a support and is finite. This justifies the broader ambient core without silently assuming feasibility there. For source-valid OCO, Feasible A plus canonical feedback supplies the feasible actual run. Strong global-support regularity is the explicit source-interface condition; no claim every arbitrary convex EReal function is subdifferentiable on its entire closed domain.

The core guarantees are deterministic same-run reduction and transport. hB is universally quantified over every g and every feasible comparator for the SAME A at the fixed T. Its existence is not proved for arbitrary A. B may depend on the whole sequence; it is not an algorithmic input. Common fixed A,p prefix statements do not establish independence of externally chosen policies or randomized laws. T0 is an algebraic extension; no positive-horizon numerical rate, tuning or anytime assertion occurs.

## Per-target seven-slot scrutiny

### outputHistory_last — accepted-with-explicit-delta

- quantifiers: All A,t,Fin t vector histories h; no legality/regularity.
- assumptions: No hypotheses beyond scoped types.
- operation_information: Reconstruct A on successive strict vector prefixes.
- conclusion: Last reconstructed output equals A t h.
- constants_indices: Length t vectors versus t+1 outputs; Fin.last t; t0 included.
- source_delta_boundaries: Library structural identity; no independent initial point or source numbered theorem.
- objects: Full exact header above in supplied finite-dimensional real inner-product scoped context; Domain is shared nonempty closed convex carrier. Intrinsic definitions may need fewer classes than the scoped terminal.

### history_zero — accepted-with-explicit-delta

- quantifiers: All A,loss,p at zero.
- assumptions: None.
- operation_information: Nat.rec base history.
- conclusion: history0=Fin.elim0.
- constants_indices: Empty vector history; first output is A0(empty).
- source_delta_boundaries: Algebraic extension even for irregular losses/illegal p.
- objects: Full exact header above in supplied finite-dimensional real inner-product scoped context; Domain is shared nonempty closed convex carrier. Intrinsic definitions may need fewer classes than the scoped terminal.

### history_succ — accepted-with-explicit-delta

- quantifiers: All A,loss,p,t.
- assumptions: None.
- operation_information: Append selected current support after current output.
- conclusion: history(t+1)=Fin.snoc(history t)(selected t).
- constants_indices: New vector occupies index t.
- source_delta_boundaries: Identity does not itself establish support membership; no projection mandated for arbitrary A.
- objects: Full exact header above in supplied finite-dimensional real inner-product scoped context; Domain is shared nonempty closed convex carrier. Intrinsic definitions may need fewer classes than the scoped terminal.

### history_castSucc — accepted-with-explicit-delta

- quantifiers: Every i:Fin t, all A,loss,p,t.
- assumptions: Only old index bound encoded by Fin.
- operation_information: Read successor history at castSucc.
- conclusion: Old entries remain exactly unchanged.
- constants_indices: Excludes last new entry; t0 vacuous.
- source_delta_boundaries: Structural prefix preservation, not regret or legal feedback.
- objects: Full exact header above in supplied finite-dimensional real inner-product scoped context; Domain is shared nonempty closed convex carrier. Intrinsic definitions may need fewer classes than the scoped terminal.

### history_selected — accepted-with-explicit-delta

- quantifiers: Every earlier i<t on same A,loss,p run.
- assumptions: Fin t index only.
- operation_information: Identify stored entry with earlier selection.
- conclusion: history t i=selected i.val.
- constants_indices: Strictly past vectors only.
- source_delta_boundaries: Cannot substitute an unrelated vector sequence; identity not support guarantee.
- objects: Full exact header above in supplied finite-dimensional real inner-product scoped context; Domain is shared nonempty closed convex carrier. Intrinsic definitions may need fewer classes than the scoped terminal.

### output_linear_run — accepted-with-explicit-delta

- quantifiers: Every A,loss,p,t.
- assumptions: None.
- operation_information: Feed actual selected-vector prefix to SAME A.
- conclusion: output=linearRun A(selected A loss p).
- constants_indices: Same time, same earlier vectors; t0 included.
- source_delta_boundaries: Writing whole selected sequence does not make learner query future values.
- objects: Full exact header above in supplied finite-dimensional real inner-product scoped context; Domain is shared nonempty closed convex carrier. Intrinsic definitions may need fewer classes than the scoped terminal.

### outputHistory_played — accepted-with-explicit-delta

- quantifiers: Every i<=t through Fin(t+1).
- assumptions: None.
- operation_information: Reconstruct all past/current outputs from actual history.
- conclusion: outputHistory(actualhistory)i=actual output at i.
- constants_indices: Includes current last and initial index.
- source_delta_boundaries: Actual-run equality, not arbitrary history consistency assumption.
- objects: Full exact header above in supplied finite-dimensional real inner-product scoped context; Domain is shared nonempty closed convex carrier. Intrinsic definitions may need fewer classes than the scoped terminal.

### output_mem — accepted-with-explicit-delta

- quantifiers: All V,A,loss,p,t; all histories in Feasible premise.
- assumptions: Feasible V A.
- operation_information: Instantiate universal learner feasibility at actual vector history.
- conclusion: Actual output belongs to V.
- constants_indices: No horizon restriction; t0 included.
- source_delta_boundaries: Feasible is stronger off-path interface, not derived from an arbitrary learner; no bounded V.
- objects: Full exact header above in supplied finite-dimensional real inner-product scoped context; Domain is shared nonempty closed convex carrier. Intrinsic definitions may need fewer classes than the scoped terminal.

### history_prefix — accepted-with-explicit-delta

- quantifiers: Common fixed A,p; two whole loss sequences and time t.
- assumptions: Every whole loss function agrees for s<t.
- operation_information: Compare actual histories.
- conclusion: histories at t equal.
- constants_indices: Current loss and future unrestricted; t0 empty.
- source_delta_boundaries: Not equality merely of observed scalar losses, not external selection independence.
- objects: Full exact header above in supplied finite-dimensional real inner-product scoped context; Domain is shared nonempty closed convex carrier. Intrinsic definitions may need fewer classes than the scoped terminal.

### output_prefix — accepted-with-explicit-delta

- quantifiers: Common A,p, loss/lossprime and t.
- assumptions: Strict-past whole function equality.
- operation_information: Apply same learner to equal histories.
- conclusion: Current outputs equal.
- constants_indices: No current/future loss equality required.
- source_delta_boundaries: No randomized-law, finite-query execution or arbitrary-policy equivalence claim.
- objects: Full exact header above in supplied finite-dimensional real inner-product scoped context; Domain is shared nonempty closed convex carrier. Intrinsic definitions may need fewer classes than the scoped terminal.

### oracle_feedback — accepted-with-explicit-delta

- quantifiers: V,A,loss,p,T; optional law quantifies arbitrary off-path histories.
- assumptions: Feasible A; OracleLaw V p; every played loss SubdifferentiableOn V.
- operation_information: Instantiate universal optional law at actual reconstructed current output.
- conclusion: LegalFeedback on played t<T.
- constants_indices: T0 vacuous.
- source_delta_boundaries: Sufficient route only; OracleLaw is NOT mandatory in core comparison/transfer.
- objects: Full exact header above in supplied finite-dimensional real inner-product scoped context; Domain is shared nonempty closed convex carrier. Intrinsic definitions may need fewer classes than the scoped terminal.

### canonical_feedback — accepted-with-explicit-delta

- quantifiers: V,A,loss,T; policy fixed to canonicalPolicy.
- assumptions: Feasible A and played SubdifferentiableOn.
- operation_information: Canonical nonempty global support selection.
- conclusion: Actual canonical played legality.
- constants_indices: All t<T including ordinary T0 vacuity.
- source_delta_boundaries: Fallback0 cannot replace membership; no arbitrary-policy or executable-choice assertion.
- objects: Full exact header above in supplied finite-dimensional real inner-product scoped context; Domain is shared nonempty closed convex carrier. Intrinsic definitions may need fewer classes than the scoped terminal.

### trajectory_finite_loss — accepted-with-explicit-delta

- quantifiers: V,A,loss,p,T and t<T.
- assumptions: Feasible A, all played losses SubdifferentiableOn; no LegalFeedback needed.
- operation_information: Evaluate actual feasible output.
- conclusion: Loss equals embedding of its real value.
- constants_indices: Exact finite equality at played t.
- source_delta_boundaries: Proper+support on V justifies finiteness even if p illegal; not globally finite loss assumption.
- objects: Full exact header above in supplied finite-dimensional real inner-product scoped context; Domain is shared nonempty closed convex carrier. Intrinsic definitions may need fewer classes than the scoped terminal.

### support_gap — accepted-with-explicit-delta

- quantifiers: V,f and ambient x,g; feasible u.
- assumptions: SubdifferentiableOn V f, u in V, actual global g support at x.
- operation_information: Form finite real gap, apply actual support inequality.
- conclusion: f(x).toReal-f(u).toReal<=inner(g,x-u).
- constants_indices: Coefficient1, eta1 specialization only; no rate premise.
- source_delta_boundaries: No x in V; proper+given support proves ambient x finite, regularity proves u finite.
- objects: Full exact header above in supplied finite-dimensional real inner-product scoped context; Domain is shared nonempty closed convex carrier. Intrinsic definitions may need fewer classes than the scoped terminal.

### linearLoss_gap — accepted-with-explicit-delta

- quantifiers: All g,x,u.
- assumptions: Only intrinsic real inner-product context needed.
- operation_information: Subtract real linear losses.
- conclusion: linearLoss g x-linearLoss g u=inner(g,x-u).
- constants_indices: Coefficient1, exact equality, no time.
- source_delta_boundaries: Algebraic helper not OLO performance guarantee; no EReal conversion.
- objects: Full exact header above in supplied finite-dimensional real inner-product scoped context; Domain is shared nonempty closed convex carrier. Intrinsic definitions may need fewer classes than the scoped terminal.

### regret_comparison — accepted-with-explicit-delta

- quantifiers: V,A,loss,p,T,u on same actual sequence.
- assumptions: Played SubdifferentiableOn, played LegalFeedback, u in V; NO Feasible A/OracleLaw.
- operation_information: Sum global support gaps and identify SAME A induced linear run.
- conclusion: Nonlinear real regret<=linear comparator regret of actual selected sequence.
- constants_indices: range T; source1=Lean0; factor1; T0 zero.
- source_delta_boundaries: Ambient stronger core may output outside V; feasible/canonical adapter needed for source-valid OCO producer.
- objects: Full exact header above in supplied finite-dimensional real inner-product scoped context; Domain is shared nonempty closed convex carrier. Intrinsic definitions may need fewer classes than the scoped terminal.

### regret_transfer — accepted-with-explicit-delta

- quantifiers: Fix V,A,loss,p,T; hB covers EVERY g and EVERY feasible comparator for SAME A at fixed T.
- assumptions: Played regularity/legality; universal OLO hB; u in V.
- operation_information: Specialize universal linear guarantee to endogenous actual selected sequence.
- conclusion: regret<=B(selected A loss p)uT.
- constants_indices: No extra constant or residual; fixed T in premise and conclusion.
- source_delta_boundaries: B is evaluation-only, may depend on whole g/u/T; no sublinear guarantee for arbitrary A, no source universal optimality.
- objects: Full exact header above in supplied finite-dimensional real inner-product scoped context; Domain is shared nonempty closed convex carrier. Intrinsic definitions may need fewer classes than the scoped terminal.

### canonical_regret_comparison — accepted-with-explicit-delta

- quantifiers: V,A,loss,T,u; actual canonical policy.
- assumptions: Feasible A; played regularity; u in V.
- operation_information: Produce canonical legality then compare SAME learner/selected sequence.
- conclusion: Canonical nonlinear regret<=corresponding induced linear comparator regret.
- constants_indices: Exact factor1, all source rounds translated to range T; T0 included.
- source_delta_boundaries: Feasible source adapter, no numerical OLO guarantee or bounded domain assumption.
- objects: Full exact header above in supplied finite-dimensional real inner-product scoped context; Domain is shared nonempty closed convex carrier. Intrinsic definitions may need fewer classes than the scoped terminal.

## Future reader requirements

- R1: Attribute ONE unnumbered Section2.3 printed22/PDF34 reduction, not18 printed results; distinguish18 existing proofs/9definitions/3abbreviations and zero new mathematics/registry nodes.

- R2: Explain actual finite-vector learner A, Nat.rec/Fin.snoc, reconstructed all played outputs and current support only after current output; same selected sequence and SAME A on linear and nonlinear sides.

- R3: State proper global EReal supports/Regular, finite witness/noBottom and actual finite conversions before toReal; no unconditional totalized infinity regret or global loss-integrability/finite-value assumption.

- R4: Separate ambient core support_gap/regret_comparison/regret_transfer without Feasible A from feasible canonical/full-source OCO adapters; no boundedness or gradient norm/rate premise.

- R5: Played-only LegalFeedback suffices; optional off-path OracleLaw is only sufficient. Canonical noncomputable choice actually produces legality under feasibility/regularity; do not assume performance or assign a tie.

- R6: hB is universal over ALL vector sequences and ALL feasible comparators for SAME A at fixed T, and is an INPUT to transport; B is evaluation-only, not queried by A/p. No guarantee producer for arbitrary learner or universal optimality.

- R7: Common fixed exogenous deterministic A,p and strict-past WHOLE loss equality are prefix scope; source1=Lean0, x0=A0(empty), T0 empty. No randomized independence/measurability/finite-query executable/anytime certificate.

- R8: Preserve exact prior source/public/canary/reader snapshot history; fresh BODY/kernel/guards/value graph/rootTests/harness/currentreader/site/pixels/FINAL/native/PR remain separate. Remaining maintext/appendices/nineOTHERChapter1/null incompleteChapter2/unenumerated3–16/ACTIVE Goal remain required; no merge/live claim.

## Additional future format obligation (original R1–R8 unchanged)

Future reader serialization repair: frozen before-reader math has doubled literal TeX command backslashes (including rm/le/sum/langle/rangle); actual normalize_math_source only wraps delimiters and does not collapse them. Require an explicit versioned reader-scope addendum superseding preserve-math-strings solely for escaping, preserve originals and source meaning, then inspect actual rendered source formulas/pixels. This is not a Lean theorem or source mathematical repair.

This supplemental renderer inspection occurred before issuing this review. CONTRACT stabilization remains accepted-with-explicit-delta; future reader acceptance is withheld until this bounded format issue is repaired and visibly checked. No source target, proof, input or earlier-stage receipt was edited.

## Scope and repairs

Required mathematical repairs: none. Required blocking metadata repairs: none. Effective full-header extraction and v3 context/type bridge repair are satisfied; original failures remain historical. Current BODY, whole canary replay, named kernel/guards/actual compiled graph, combined root/Tests/harness, reader/site/FINAL/native acceptance and PR delivery are separate future gates. Existing18 proofs/9 definitions/3 abbreviations and25 canary proofs/8 definitions/2 abbreviations are reuse, not newly authored or currently BODY-certified. No chapter/whole Goal acceptance, merge/deploy/live or worktree retirement.

## Raw reviewed inventory

Every fixed file was read as raw bytes for integrity. Semantic reading focused on source/context/fullheaders/neutral bridge/decoder and actual public interfaces; binding prior dependency artifacts does not recursively reaccept their historical packages. Reader inputs are preserved before-snapshots; current live reader requires later separate review.

| Path | SHA256 |
|---|---|
| `BanditRLProof/OnlineLinearization.lean` | `ec231ef4d85c3b27744378d1c3d9f071b6177fa1535d5db440a787800111339e` |
| `Tests/OnlineLinearizationCanary.lean` | `0f62baa46017ec5fc3e8234248dbd2e03388eae62396689c8b7e44f93931f975` |
| `BanditRLProof.lean` | `7cdb1969bad2f7b42cfd7a25f6d15747d0d49178dadc244b70ab1f9b8c92c5ad` |
| `Tests.lean` | `2b3615efabe9c94eff5dade925783e7d0ebacd3139a7ab65a5d46ba2c695ef77` |
| `BanditRLProof/OnlineSubgradientPolicy.lean` | `ac8fbfb3eee3c92ebb79b44f33beec33b500105bb7e54df5176c14e886c2c662` |
| `BanditRLProof/OnlineSubgradientDescent.lean` | `6ba8586e1691babc2db3e0c0fcddb69b4236e16f9f192c464b4c04262e854f1c` |
| `BanditRLProof/OnlineSubgradientBasic.lean` | `af3d3f56e4a64cd8adbe47368caf5382e63b428f01da29a121c28c8014f352a5` |
| `BanditRLProof/OnlineClosedProper.lean` | `c66f00c33b45fb8a0e11583eeadf506e176c16166ce2af02f41f0674507cebe7` |
| `BanditRLProof/OnlineGradientDescent.lean` | `9300cb2735da9f125e404f78b86509df47fe65a5f4d89abc469e071bdffdb871` |
| `BanditRLProof/OnlineLearningRegret.lean` | `231eda88cb1c45bf3bc9209bfbdd696fbfbe8a64b00303113a23cbc4dff3ca5b` |
| `lean-toolchain` | `b15a57f8ea4c890197465ce1156667ae13d9ed4ab8a9f263a920bf010d967d82` |
| `lakefile.lean` | `0164f3b5b5bdcbb237ab15ae8b44da83e183f4b97d5f3832aa4a57f27dc69d45` |
| `lake-manifest.json` | `87c3e616f86244550ef39e7415186b11c1d4cf4bef20173196a619d9d4d48f48` |
| `runs/active_frontier.json` | `567e5873aa2549a83f2820d758069213808da822a93087129877385a1addf7c3` |
| `docs/contracts/online-book-v1/source-inventory.json` | `a2a504cf40d73f9c5e36f00fc1ef3b949ccaf5a558ab603c1c2a86007f30efa7` |
| `research-wiki/contribution-contracts/ONLINE-LINEARIZATION-20261004.json` | `c4543b5ef9754d9b4f0a6af099449ff0ffb26c88d99016dd27b497ae4956a6f1` |
| `runs/online-linearization-20261004/accepted-decision.json` | `7a3402d64a5f488ff6ba2a7047413ae9cc5ea1c3b398bb9f541d5ae619a067e6` |
| `runs/online-linearization-20261004/pr-delivery.json` | `7a7301c6d2783004cd6032e32f638e29d58983325e751be8524da15401eddf7d` |
| `runs/online-guessing-public-20261007/accepted-decision-v1.json` | `2f53f40e8b95b256c87c8767d319328e7720ea0eddb951dae1491d7236fd7f01` |
| `runs/online-guessing-public-20261007/delivery-obligations-overlay-v1.json` | `ee39ed758615cbd48af8e710d2fdb04e82836dd762e22f045546ca43f4a4afd0` |
| `E:/ABRL/worktrees/research-online-book/runs/online-linearization-public-20261007/snapshots/before-website--content--readings.json.txt` | `b0519ca7e882e1fa36d2f5345a23ecc95b6d3126aef2cf66f67a8764dfd97098` |
| `E:/ABRL/worktrees/research-online-book/runs/online-linearization-public-20261007/snapshots/before-website--content--highlights.json.txt` | `b904acf7bd4ed1bf7c8060d5ab61177cdf9514ff20a33954eb0b9ba05aadab37` |
| `E:/ABRL/worktrees/research-online-book/runs/online-linearization-public-20261007/snapshots/before-website--content--chapters.json.txt` | `12a416e16b5841aed61dc07ccbccd8100797cbb58754ddbd4293cee7d3e80526` |
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
| `docs/contracts/online-linearization-public-v1/actual-context-v1.txt` | `4fd10a10fbdd8e89c2d1d82299766f420311feae5ea299954598b4791e785e9e` |
| `docs/contracts/online-linearization-public-v1/contract-manifest-v1.json` | `1ed484b4853092ab6c0edfe6fcb303f01e6483bcabfffe0a4a210d30416a9631` |
| `docs/contracts/online-linearization-public-v1/contract-manifest-v2.json` | `10be5a87913111d6511728e163049195f40d3041b389f86e3215415d58f3e11f` |
| `docs/contracts/online-linearization-public-v1/contract-v1.md` | `babca0d9924ce6606c2dc0c4266f26db8c8f00a9e7916b3aaf8fb3f3eb41bdf1` |
| `docs/contracts/online-linearization-public-v1/contract-v2.md` | `d2253fe500f6cda0c12a901e0969fd8ae026213309dfd28c19506b8eb22b3c4a` |
| `docs/contracts/online-linearization-public-v1/conversion-window-v1.md` | `54de42636e2d6b52c1732e2b943906762cbf91618e7d9f11e1ab994f8b456906` |
| `docs/contracts/online-linearization-public-v1/dependency-DAG-v1.json` | `abd9f0f2b08832f1f1a4428ed1b0f7a765f7c1642e4e39a167ce048e56472937` |
| `docs/contracts/online-linearization-public-v1/headers-v1.json` | `80c68e56215b2bf8bac6d0a8b7c78a1840d01afdfa10e54d00483d4295056097` |
| `docs/contracts/online-linearization-public-v1/headers-v2.json` | `50dbc20daae76a93c46d5968c631b6ecb1289dc2867d4dfb3d3b7e6cae3ca48f` |
| `docs/contracts/online-linearization-public-v1/native-statement-fingerprints-v1.json` | `2dc38da87d57b685f9782cf5c3d3fe1927cda914a06b6e755251a2328253b427` |
| `docs/contracts/online-linearization-public-v1/native-statement-fingerprints-v2.json` | `2dc38da87d57b685f9782cf5c3d3fe1927cda914a06b6e755251a2328253b427` |
| `docs/contracts/online-linearization-public-v1/raw-statement-fingerprints-v1.json` | `9368dab07c8a440fd40430166bca592d7195285830e9417017c57f9a7efc8fdd` |
| `docs/contracts/online-linearization-public-v1/raw-statement-fingerprints-v2.json` | `e3856a096d6bfe979e551933bc5a2817fa6ba2d68e5b604475f49cbccdd6faaa` |
| `docs/contracts/online-linearization-public-v1/semantic-signature-v1.json` | `9f557dbf0c926d986c520cd084a5fa3a0d942c385d35524c643a25ad8da927d3` |
| `docs/contracts/online-linearization-public-v1/source-card-v1.json` | `b09b7da6893846a8effbc159d1cc07ecac58874bd96ea12f383a2b5e223a0c2e` |
| `runs/online-linearization-public-20261007/.gitattributes` | `705fd4d6451a31d36b3df7de96f83f30ac976c9b4a6d1e51671d8e2f33e2d0da` |
| `runs/online-linearization-public-20261007/00_context.md` | `c678794eaaa4afe01a66cbcee4438e07d8e207043e5dd7938b8d4c3fbec8b3df` |
| `runs/online-linearization-public-20261007/10_upper_director-v1.md` | `5c5712b5609113c1d612c7a26b7d893c79a331a065eeec39a8f17ad846765924` |
| `runs/online-linearization-public-20261007/20_architect-v1.md` | `433e77d8ebb40041a4e46889273e310e0fb65d668d74473346807303f920e08e` |
| `runs/online-linearization-public-20261007/base-PR183-fresh-v1.json` | `0b1f62be4cf4b043ff2616f84c56c7cd049f2e0afb6f4f163f4cf6030b1b74f6` |
| `runs/online-linearization-public-20261007/blind-decoder-receipt-v3.json` | `88c14a3f3a817ef33350e28816d0f005f2e35a2ba41f943898ca4db1068cdab7` |
| `runs/online-linearization-public-20261007/blind-decoder-v3.md` | `4e8a006f16653c109d7e7a09c21eef3da0bdf7e816e92862de2f2aa0d75294ad` |
| `runs/online-linearization-public-20261007/blind-packet-v3.md` | `fc85b55ec3c3d4243bc8d765d5a21c87f8da85870eac723aab7fd848fbb704bf` |
| `runs/online-linearization-public-20261007/canonical-worktree-audit-v1.json` | `ba458304ea32a6bd3f81a1c212b8f63a6d8f7270bea68bc42b45fbe2be282657` |
| `runs/online-linearization-public-20261007/closed-type-comparison-v3-exit.json` | `29d692252bf1b4670ccb304f91269980a5e3f0a6507535f03d117f27a010d8cf` |
| `runs/online-linearization-public-20261007/closed-type-comparison-v3.json` | `360a4f4eecf20a8340044516eca124994d411ced8b53e82ed49304cbbd404d1a` |
| `runs/online-linearization-public-20261007/closed-type-comparison-v3.log` | `272b958750c028e538dcfb191e2ef365891969234c49008b11f51e4f896b7699` |
| `runs/online-linearization-public-20261007/draft-event-v1-exit.json` | `7d13fe67c3ab56aee87a10b7265e6f75d77f3c49023d02bd7af64d33d05ec40c` |
| `runs/online-linearization-public-20261007/draft-event-v1.log` | `ac9c69ada71a75ce0112edbb4778aafd4a01afab756189cd28e9e69d2b92f4c2` |
| `runs/online-linearization-public-20261007/draft-extractor-repair-v2.json` | `c10a0262d523541038bb4b5b1aa3e797adbab0db1750b7e4f467455b102b1aad` |
| `runs/online-linearization-public-20261007/draft-freeze-v1.json` | `63d196aa2535b7a30f5442bd592fd6fa59febe7b8343f25f207c356959cdc706` |
| `runs/online-linearization-public-20261007/draft-freeze-v2.json` | `0598899ed0aaca4080afdb563d21850678dd23e74601160cb82f0523d6984266` |
| `runs/online-linearization-public-20261007/draft-v2-event-exit.json` | `eb17c27629c68e2237572c2f27eb4859ce9ebfe60dd3d1542bc70398e51e42e7` |
| `runs/online-linearization-public-20261007/draft-v2-event.log` | `396751ccde1f8bfb5756e3a2629d5fffe6aadf057a423fb4b7b6790c19ac8f0b` |
| `runs/online-linearization-public-20261007/fresh-fetch-v1-01-exit.json` | `db958934ccfc68460bb2714f001ce1c47e49c20ab7157c29e44dba069fe52adc` |
| `runs/online-linearization-public-20261007/fresh-fetch-v1-01.log` | `ff06435234be0304d52e60deff7224ba6ebf9c461f171bbd562c8fbe05c25c05` |
| `runs/online-linearization-public-20261007/help-frontier-refresh-v1-exit.json` | `49253d0ffad8317d4e12659dd3ea25c23b194ccd2c423c92a726126812a8b868` |
| `runs/online-linearization-public-20261007/help-frontier-refresh-v1.log` | `bff73ff554907d7c5dd50b99f2491f5675e93afb29829e402ec383fb52fe3cdc` |
| `runs/online-linearization-public-20261007/help-frontier-shadow-v1-exit.json` | `2e47a043aa2fdceec705fbd928fc003b5d3e7e52e97bb17b85460ffd11157534` |
| `runs/online-linearization-public-20261007/help-frontier-shadow-v1.log` | `ad548f6e24b3214fbf5796c632caa24debbaa21c6622f7dab8abe268f521de7d` |
| `runs/online-linearization-public-20261007/help-lifecycle-event-v1-exit.json` | `edb92cdef23e05737503788a9dad64cdbab51db475ea8b4fabf4a59315844584` |
| `runs/online-linearization-public-20261007/help-lifecycle-event-v1.log` | `b1e8b438a9b725793b9888d206e98a971ace3df200ec90ed9cb63eab26b28507` |
| `runs/online-linearization-public-20261007/help-memory-record-v1-exit.json` | `86d611ade2d432bd1891c3a6b044b0d5fb9ff1978cfce97ade150f2403b0ad2b` |
| `runs/online-linearization-public-20261007/help-memory-record-v1.log` | `89e8a7b2bb8d4fd593f0705289ca3c4c63015e48d0e8c9cbe5b71cf2c7cc44f4` |
| `runs/online-linearization-public-20261007/help-new-task-v1-exit.json` | `9f466748e9baca497e8492f79a03d5babdbc5bb7b8963ce973387efa3cf3d9a7` |
| `runs/online-linearization-public-20261007/help-new-task-v1.log` | `25eb9342c3094bee57187630bd149d2c522fc9f7ac7e65bebe5c198eba60ed99` |
| `runs/online-linearization-public-20261007/help-retrieval-record-v1-exit.json` | `b9e7f9ffc89d76d80b05e5fcc061c45ceaa0fb79a20d99b49d8ace90c890dcb4` |
| `runs/online-linearization-public-20261007/help-retrieval-record-v1.log` | `73ac93f120215511ff0370d7ce100a9d0e83598ad882bcc5773cd1dc889b5321` |
| `runs/online-linearization-public-20261007/help-root-v1-exit.json` | `ef4a3e842fb9fe51a2e28919a8d03c6452946900b6421ff78de1462abcc3f2eb` |
| `runs/online-linearization-public-20261007/help-root-v1.log` | `daacf23e36eec4898dce3b3de02a07b71fb0f80f08e33e8dfe00722e7572970c` |
| `runs/online-linearization-public-20261007/help-safe-verify-v1-exit.json` | `6023f69536a78e220f320cc341451c6739a49a6b407891e4d5656c47e7cc5d39` |
| `runs/online-linearization-public-20261007/help-safe-verify-v1.log` | `1773541c625f225e5a9abc61985c3ad19e871cf31aa0cf89cc440b3d8398862c` |
| `runs/online-linearization-public-20261007/help-statement-fence-v1-exit.json` | `1c2eb1b8d3273ad75abc75206521adb1dd04ff296b28e36c0f76d7ed51def5ff` |
| `runs/online-linearization-public-20261007/help-statement-fence-v1.log` | `4f4fca9dfaac7a7c3de8025d3d0f7c4ba58d1f4b33feb08d19e12229942dba75` |
| `runs/online-linearization-public-20261007/help-trial-log-v1-exit.json` | `53a0cd38153a0f202cc18c313f6d57467bb466930dd6e39f3e934b23b8302606` |
| `runs/online-linearization-public-20261007/help-trial-log-v1.log` | `ea7bd7e4d64216b46f554a90e02a3d58b4fcbe72766c2f7b316b656b94d19b32` |
| `runs/online-linearization-public-20261007/historical-PR150-fresh-v1.json` | `1d47813788ee1f6fd6d84c74360d5b259a85b746aebe09591f2ef144024ade29` |
| `runs/online-linearization-public-20261007/leaves/closed-type-comparison-v3.lean` | `327f3def389c8533ae5d4ce97aeea6a3e4f605738c4d7d0370d774e40c4904f6` |
| `runs/online-linearization-public-20261007/leaves/neutral-propositions-v3.lean` | `485c3287ccf0620f17c02d8bba10a5c920d3038547ee3db24d16f8da35cd9a44` |
| `runs/online-linearization-public-20261007/local-API-search-v1-exit.json` | `ccec0ce0f19050260d739efadda057a494e5a26104f29ef08cc35187af97d3fe` |
| `runs/online-linearization-public-20261007/local-API-search-v1.log` | `35e07e80dc45466ee3c37f37212c5106a8075cec16162a808b62de49d810b24b` |
| `runs/online-linearization-public-20261007/local-API-search-v2-exit.json` | `9df442c9f1b94bd6bff09dbef8d898a195810509b0deb73cf268415a71955c47` |
| `runs/online-linearization-public-20261007/local-API-search-v2.log` | `35e07e80dc45466ee3c37f37212c5106a8075cec16162a808b62de49d810b24b` |
| `runs/online-linearization-public-20261007/local-API-search-v3-exit.json` | `aabacaa0535f7928d6bf28571fdd885e7ab843357c89a3d53687c167a04585b8` |
| `runs/online-linearization-public-20261007/local-API-search-v3.log` | `f71a3c3444c991d2d10e93df645eb06132a178a96d0a2fd736a583ac6edc7d33` |
| `runs/online-linearization-public-20261007/mathlib-API-search-v1-exit.json` | `55e81023e4f2b2eae170c7f140e2979f5013b69cec5194c30b69dd72fd19a75c` |
| `runs/online-linearization-public-20261007/mathlib-API-search-v1.log` | `2490af058537d7b7857771ea7e834cabf19cd7c3742058a5da6a54531c498ba9` |
| `runs/online-linearization-public-20261007/mathlib-API-search-v2-exit.json` | `070929893e01fff63ab04aa81231745851d35236cf5e996946712328bfad01f0` |
| `runs/online-linearization-public-20261007/mathlib-API-search-v2.log` | `2490af058537d7b7857771ea7e834cabf19cd7c3742058a5da6a54531c498ba9` |
| `runs/online-linearization-public-20261007/mathlib-API-search-v3-exit.json` | `55e81023e4f2b2eae170c7f140e2979f5013b69cec5194c30b69dd72fd19a75c` |
| `runs/online-linearization-public-20261007/mathlib-API-search-v3.log` | `2490af058537d7b7857771ea7e834cabf19cd7c3742058a5da6a54531c498ba9` |
| `runs/online-linearization-public-20261007/memory-digest-draft-v1.md` | `ee7da6b6d408e48e54f6532d8d939d54c7633580db14515c8062d9e8d3fe823c` |
| `runs/online-linearization-public-20261007/neutral-map-v3.json` | `9438b9c8dcf2e9eebe7eaf114e7d7f82c46cc44eb012e9cbb333446fe9652c67` |
| `runs/online-linearization-public-20261007/neutral-propositions-v3-exit.json` | `0f657330f3eaeb358621913ef2d55afa43d00a16ea51d2caabcd22bf65ebb94c` |
| `runs/online-linearization-public-20261007/neutral-propositions-v3.log` | `dcd325a34cf32b3111778a224a7f0819e03d3b1e593065febaaffa9040d2d946` |
| `runs/online-linearization-public-20261007/new-task-v1-exit.json` | `59d21a831036ef5ee68e2009d2dc47027045d2fca6b1c080677be59ced3b774f` |
| `runs/online-linearization-public-20261007/new-task-v1.log` | `16531a31d78b306f745ed2b64856c004551a0c4d958972afe58adb1edcbb485b` |
| `runs/online-linearization-public-20261007/paper-boundary-v1.json` | `dae89e7ae9e0499b4d371a595aea19637b9e6430ce98331ca4ae4388b5747155` |
| `runs/online-linearization-public-20261007/proof-obligations-draft-v1.json` | `52ecca069fc2044d24df5970bf1168776ec1323f9db10d15fa03413369b90e40` |
| `runs/online-linearization-public-20261007/reuse-decision-v1.md` | `24a2de8218d486e104c695fb4256ed319dc1f10db6d297fa72654714a14b8678` |
| `runs/online-linearization-public-20261007/reuse-decision-v2.md` | `24a2de8218d486e104c695fb4256ed319dc1f10db6d297fa72654714a14b8678` |
| `runs/online-linearization-public-20261007/reuse-decision-v3.md` | `24a2de8218d486e104c695fb4256ed319dc1f10db6d297fa72654714a14b8678` |
| `runs/online-linearization-public-20261007/source-pdf13-v1.png` | `228ea769f7cec2ba5fe2d5e416b4ac5f60c93ec38f83a2dd7a537c2a51d2c5f4` |
| `runs/online-linearization-public-20261007/source-pdf13-v1.txt` | `b16d82b563558afaaa14776c6015a78be9e0daa3d888a9a0593c057a54d2288b` |
| `runs/online-linearization-public-20261007/source-pdf14-v1.txt` | `3f9d01aee6e81504b7ca2ef0d9657bc1ee30f36eb54a957b8018c4d0c3e2ac66` |
| `runs/online-linearization-public-20261007/source-pdf15-v1.txt` | `037b6d907a868c339b881162333f6e56352cbebf285902eb6ed628ff4f8bd947` |
| `runs/online-linearization-public-20261007/source-pdf28-v1.txt` | `a9d4910e2c687a25babd24d5b4c30f4e6c4d1fdc4018c29ad239c327bacfd87c` |
| `runs/online-linearization-public-20261007/source-pdf31-v1.png` | `c1cb49ac038e88055cb4651f70755c456ccbc817a70c5a06c818f5967676bfa2` |
| `runs/online-linearization-public-20261007/source-pdf31-v1.txt` | `7709a706da7b5320555f5ef19e07fa798affde6a077363425b929c07af0b9a99` |
| `runs/online-linearization-public-20261007/source-pdf32-v1.txt` | `3cb9fb0c18b5b9c63c280944188334305bd9a042fed58fad67e797b6d7b76bdd` |
| `runs/online-linearization-public-20261007/source-pdf33-v1.txt` | `bd875a0b37e762b0caa50f88527507ec96e6938b49683a4e3a09aa2c9c47b911` |
| `runs/online-linearization-public-20261007/source-pdf34-v1.png` | `265645dc6c0d4afbe72c0bc566cb77621908f84a624a641dea329a87fbc2ae95` |
| `runs/online-linearization-public-20261007/source-pdf34-v1.txt` | `82fd99a632a8f7a940e16e58a6bca8e8f81c68bf715db535aa7c39b28df81910` |
| `runs/online-linearization-public-20261007/source-pixel-inspection-v1.json` | `0779243614c027bb8e92284f20031d8ed5b6f707c611c1f2298e7ae03c965c3a` |
| `runs/online-linearization-public-20261007/source-render-v1.json` | `90ee7381ead8fff48b9f145554cd36b191760fec0e783898116de7a0079ef0e1` |
| `runs/online-linearization-public-20261007/tool-failure-record-v1.json` | `3dc4c08d31f8607df3de5df49bcccc8415d05fdd853ff1d93f68c1cb0209c443` |
| `tasks/ONLINE-LINEARIZATION-PUBLIC-20261007.md` | `e08e1887cafa9dc03b34301558ada7cf3a0c74c6634f07aa095b480e71524cb5` |
| `conversion-windows/ONLINE-LINEARIZATION-PUBLIC-20261007.md` | `e08e1887cafa9dc03b34301558ada7cf3a0c74c6634f07aa095b480e71524cb5` |
| `proof-obligations/ONLINE-LINEARIZATION-PUBLIC-20261007.md` | `e08e1887cafa9dc03b34301558ada7cf3a0c74c6634f07aa095b480e71524cb5` |
| `runs/online-linearization-public-20261007/source-contract-packet-v2.md` | `7481285aa207655f7a02b61f40eaab19e74a91788ebb5e40dff2548f8fff2b2e` |
| `runs/online-linearization-public-20261007/source-contract-inputs-v2.json` | `ef786a001bb28bea06ce089a104f081a6872cf83500c1f21d4b792624908dc73` |
| `website/scripts/build_site.py` | `f6cface76e1393fef186ab63ae521c14af11878a0b892b8acfbef390ae380a4f` |
