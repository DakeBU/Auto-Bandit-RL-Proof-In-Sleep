# Final reader and evidence review — Example 2.32

Verdict: **accepted-with-explicit-delta** for the bounded canonical known-horizon absolute-loss OSD package to proceed to immutable binding and local acceptance. No required semantic repair found. This is not the later byte/HEAD gate or PR delivery decision.

Actor: `/root/source_reviewer`, distinct automated source reviewer. Requested model GPT-6 Astra, reasoning medium; runtime model identity is not independently verified. External human review: false. The review uses actual source, declarations, reader content and gate artifacts, not agreement with previous verdicts as mathematical evidence.

Checkout: `E:/ABRL/worktrees/research-online-book`, branch `codex/research-online-guessing-osd`, inspected candidate HEAD `19fef82eaeb093507417cc39777fd8846320091f`. Exact stacked base is `9f594406a8cb405fd31573bf94530d5d8569be27`, recorded as PR147 OPEN/draft and unmerged. New final evidence was untracked at review; this is not a clean-tree claim. Checkout retained.

## Seven semantic slots

1. **Objects and domain.** Source Example 2.32, printed20/physical32, uses the Chapter1 guessing game with predictions and labels in [0,1], absolute loss |x-y|. The actual shared module embeds this finite real value in EReal. Translation and support helpers quantify over all real x,y, an explicit strengthening; the source performance wrapper retains initial feasibility and labels in [0,1]. No infinity-toReal shortcut is used to manufacture a finite regret. The genuine loss, shared unitInterval Domain and actual projected iterate are reused.
2. **Assumptions.** Positive T is retained for eta=1/sqrt(T), and all comparator points lie in [0,1]. Properness/subdifferentiability and the bound on actual selected supports are proved from absolute loss. No differentiability, a chosen zero tie, assumed trajectory energy, assumed step inequality, or optimizer is supplied as a premise. The label restriction in the source wrapper is intentionally retained although the stronger all-real support bound makes it unused in its body. T=0 is covered only by structural canaries, not smuggled into the positive-horizon tuning theorem.
3. **Quantifiers.** The shifted support statement is exact global set equality: {1} above the label, inclusive [-1,1] at equality, {-1} below. Full necessity and sufficiency hold for every real test point. The performance theorem quantifies every comparator on the same run. The eventual statement fixes an arbitrary comparator and positive epsilon, then asserts an eventual upper bound. Neither the source prose nor the Lean result is interpreted as an absolute-regret bound.
4. **Information and algorithm.** Source Algorithm2.2 outputs before observing current loss. The shared noncomputable canonical selector sees the current loss and current prediction; it has no future-label or comparator argument. The structural prefix theorem and the actual future-input canary prove that changing labels/eta from t onward cannot change output t. The clamp identity is actual Euclidean projection. A canonical current choice is one permitted implementation; it does not quantify all legal/history-adaptive support policies, constitute an executable oracle, or close that mandatory Chapter2 interface.
5. **Guarantees and horizon.** The finite theorem obtains actual real regret <=sqrt(T) with eta=1/sqrt(T), not a counterfactual trajectory using a retrospectively selected gradient norm. The additional average result is one-sided eventual upper control over a family of known-horizon runs. Signed Tendsto0, absolute Big-O, and one anytime trajectory are not proved. The source's O(sqrt(T)) wording is faithfully represented as a regret upper guarantee with explicit finite constant.
6. **Producers and dependencies.** Translation reduces global support to the already proved absolute-value characterization; the full tie interval then bounds every actual support. Shared selector correctness feeds the same-run support bound; the actual OSD tuned theorem supplies the finite inequality; positive sqrt and its growth supply the eventual consequence. Prefix and clamp are actual recursive/projection facts. All12 actual PUBLIC-file fence headers and premise arrays were reviewed against frozen v2, not inferred from draft-path safe_verify passes. All27 canary native headers were independently recomputed again and match their recorded hashes. The16 compiled proof-value checks distinguish actual dependencies from curated teaching links.
7. **Scope, source and presentation.** Pinned original PDF was independently rehashed as `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17`; physical13–15,27,31–32 were read in this continuous review and physical32 freshly re-extracted for this final stage. Four source cards correctly use printed20/PDF32 and explain the earlier game/tuning context. The full generated chapter, shared module and Book HTML were semantically inspected including all folded statements and explanatory sections. Chapter2 remains partial/count null/accepted false; Chapters3–16 enumeration and older26-path migration remain required. The source inventory explicitly retains the generic legal/history-adaptive family as required and draft.

## Actual bodies, canaries and reader

The earlier complete public-body inspection remains applicable: all126 previously reviewed raw rows were independently rehashed with zero drift, and the three prior report bindings still match. The review does not replace body inspection with compilation. Public roots are reviewed for their new imports; shared dependencies are reviewed for the relevant definitions/interfaces, not every unrelated theorem.

The actual canaries use labels 0,1,0,1 and outputs 1,1/2,1,1/2,1, with selected supports 1,-1,1,-1. They prove real regret1, energy4, nonzero terminal1/4, fixed-bound RHS1 and the same eta=1/2 for horizon4 with all-comparator bound2. A separate raw5/4 overshoot really clamps to1. Future labels999 and eta=-99 do not alter the earlier output. Tie membership remains full-interval membership, not an assertion that the canonical choice is zero. These checks materially exercise the implementation.

All13 required canonical surfaces in the inventory were read and raw-bound below: public module/canary and both roots; books, chapters, readings, highlights; generator and checker; source inventory, coverage and contribution contract. Unrelated JSON entries/modules are not newly certified. The generated chapter's four primary mathematical displays, exact folded statements, pseudocode, three worked-example parts, remaining producer statements and explicit boundaries agree with the source/public code. Eight auxiliary notes use the generic “No mathematical statement recorded” fallback while immediately retaining their exact Lean statements; this is a nonblocking presentation limitation, not missing public targets. This reviewer inspected full HTML semantics, not lower-fold screenshot pixels. The visual receipt is the root actor's first-viewport-only observation; the screenshot itself is not claimed as independently viewed here.

The generator's frequency-ordered shard-index repair preserves the schema and each entry's shard lookup. Independently decoding the actual FINAL04 index and retained pre-repair index yields identical11668 entries (ID/kind/status/shard/optional label fields), while final size1496536 is below the unchanged1500000-byte checker threshold. No entries were removed and no size guard was weakened. Both generator/checker add this chapter to required pseudocode registration. The prior equivalence receipt concerns an earlier generated timestamp; current final bytes were checked separately.

## Evidence and provenance checks

- Focused actual public module/canary commands: exit0,3322/3323 jobs. Actual named axiom audit covers47 names and contains only the standard three axioms or none. Rejected compiler recovery output is not accepted evidence.
- Combined root9082 and Tests9218 jobs succeeded. Final full-harness02 actually exits0 with466 tests and7 existing skips; its log says check passed. This is observed command evidence, not a fresh rerun by this reviewer.
- Native graph checker passes16 actual proof-value checks; scoped graph13 nodes,383 boundary nodes,1014 edges. Full exported counts are19615 project nodes and996588 edges. These counts do not imply whole-project semantic review.
- Final site04 build/check both exit0,935 pages/834 modules/10691 declarations/236 highlights/11811 Lean links. Generated source_commit is19fef82eaeb093507417cc39777fd8846320091f and lean_verified is true.
- `registry-final04.json` was compared to the actual generated registry: current raw SHA256 is `65d72a931019a74ae1716c490506cb9e787169acf51a361379e66cf0932aa148`, exactly matching the receipt. All12 scoped canonical source nodes are unique and match frozen native hashes/compiled status/Online Learning Book membership. No stale-registry substitution is accepted.
- Contributor02 actually passes against exact9f594406a8cb405fd31573bf94530d5d8569be27 and covers its8 production-classified paths. This review separately reads the additional five mandatory canonical surfaces. The checker classification is not claimed to include all13.
- Scoped shadowv2 has no mismatches and would_mutate=false. Its task-local leaf remains gate-pending. The initial recorded-None shadow was not a valid pointer comparison. Actual run trials contain the bounded public reviewer event, recorded by root from the distinct review; no new trial was appended here. Global `runs/active_frontier.json` is byte-preserved relative to the stacked base and remains historical SGB. Memory/retrieval digests are scoped evidence, not enforcement of the whole workflow.

Native v1 CARD-ID premise misuse, failed comment repair, the fence.file versus --lean-file limitation, failed prefix rewrite, first public import failure, first canary energy failure, unresolved mathlib teaching-link site01 failure and strict index-size site02 failure all remain rejected historical evidence. Their later repairs do not change the frozen source mathematics. No claim is made that every attempt passed; fullharness01/contributor01 were earlier passing evidence, followed by final02 checks after publication changes.

## Decision and remaining obligations

No blocking source/body/reader/evidence mismatch found. Accepted-with-explicit-delta means acceptance of one legal noncomputable canonical current-choice implementation, stronger all-real helper statements, zero-based recursion corresponding to source rounds1..T, exact finite upper regret, and the additional one-sided horizon-family eventual consequence. It does not silently close the source's entire arbitrary legal/history-adaptive policy family.

The fixed inventory lists275 paths. Its verifier was read, but immutable capture, committed worktree/HEAD binding and PR delivery are subsequent gates and are not certified by this receipt. Final acceptance metadata must remain a separate artifact rather than mutate these reviewed bytes. PR/base being draft and unmerged, no main/live/deployment or whole Chapter2/book/Goal completion is asserted. No source, contract, production, prior receipt, trial or shadow was edited by this review.

## Raw inspected-file receipt

Rows include content inspected in the preceding continuous source/body stages and rehashed unchanged here, plus the actual final scoped reads. Large logs are reviewed at relevant errors/declarations/terminal evidence; hashing their whole bytes does not claim line-by-line semantic certification of unrelated replayed output. PDF inspection is limited to the listed pages; registry/JSON inspections are limited to the stated package scope. All digests below use actual raw bytes without JSON reserialization or newline normalization.

| Path | Raw SHA256 |
|---|---|
| `../research-online-ogd/tmp/pdfs/orabona-v10.pdf` | `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17` |
| `BanditRLProof.lean` | `fe9b92913aa2966ca131d97eeed9f12d86ab1c7b2e7b22ce354ac721a57472a0` |
| `BanditRLProof/OnlineClosedProper.lean` | `9a5fcfb9e26a2a35d8e5bb7ef7b7a7dfd65a7f1c8daab03faebb51e41d54e7c6` |
| `BanditRLProof/OnlineGradientDescent.lean` | `e7edba540c2f60032bb4a34aaf0768b3107b94276b67b6f41fc289009c8924c1` |
| `BanditRLProof/OnlineGuessingOGD.lean` | `6e99965d95e7016bc40c2f39e51f7dff4bf381c42b028e39584f703302eda8bd` |
| `BanditRLProof/OnlineGuessingSubgradient.lean` | `95d206190d443939115037f9bf6d0eeb1e3229f3ae52eb4150927fbe69e89348` |
| `BanditRLProof/OnlineSubgradientAbsolute.lean` | `17157c976889f078d02f183b55edf2821e29efa5aa32d4bfff309c2b3713db0c` |
| `BanditRLProof/OnlineSubgradientBasic.lean` | `4c17a466091b88d90451be897a2f01afa204b41933191244e0093e48396d1962` |
| `BanditRLProof/OnlineSubgradientDescent.lean` | `6ba8586e1691babc2db3e0c0fcddb69b4236e16f9f192c464b4c04262e854f1c` |
| `Tests.lean` | `026449ea4aa7655ec7d91b419ad60055dbc78e10781e8bc6493add98c5fa812c` |
| `Tests/OnlineGuessingSubgradientCanary.lean` | `b6a6e3f5c019172e2ee46d3caf03fcbc65d9bbe3a90474b03532ca560f849a61` |
| `docs/contracts/online-book-v1/coverage.json` | `48eccdcafa2e5a9a1dfe013f8eafd60ca8f063c8a19c3ea7f2de44c4a3ff1129` |
| `docs/contracts/online-book-v1/source-inventory.json` | `49b5c020c6d636425b4c887c8d7c53c2517fa8d6291747dcdf17e7a4b332a891` |
| `docs/contracts/online-guessing-osd-v1/context.txt` | `deb0e9a941ba4b4d47b8bb786462ef7440bef3c10803adf695caffb043e2f799` |
| `docs/contracts/online-guessing-osd-v1/contract-manifest.json` | `b1d1d0d25a6b710f749737bbf1e58ca2fc2fcc98fb935bef526ca843503c371d` |
| `docs/contracts/online-guessing-osd-v1/contract.md` | `3b236291e115bc6cc627fcd9b827293eccabc352b2f64221dbdc5c4159f52aaf` |
| `docs/contracts/online-guessing-osd-v1/current_subgradient_bound-header.txt` | `cf33e00553af8f12b3fb7cc16d9667093d031c33c48f5eb537ac920088ac7b01` |
| `docs/contracts/online-guessing-osd-v1/current_subgradient_bound.json` | `4dbcd582cabb166461b00314f5428be3c562cc7251a059e2230a00d671c4d3e3` |
| `docs/contracts/online-guessing-osd-v1/example_2_32-header.txt` | `c783a2dc477402bf38fd856d55570133c5324206a2ab189d41561fab8d03c3ac` |
| `docs/contracts/online-guessing-osd-v1/example_2_32.json` | `b51f3c0671d78988ba358c92b9b4790b59974d824a65668a78e9ad1043b61d06` |
| `docs/contracts/online-guessing-osd-v1/example_2_32_average_eventually-header.txt` | `0cd31eb16ead30a23bed6ffa30c7c0952d69f37270f5740cc55f995870e16439` |
| `docs/contracts/online-guessing-osd-v1/example_2_32_average_eventually.json` | `9eb36a77d2fb1b97d849c49c4ad86f838f1f8255c9d29e73c5b22f45ba7c1e34` |
| `docs/contracts/online-guessing-osd-v1/example_2_32_subdifferential-header.txt` | `61d8e03bcb2e643daee7b008f5d3bc3908a02a4339dd9f92fa5af002bdbc6d2c` |
| `docs/contracts/online-guessing-osd-v1/example_2_32_subdifferential.json` | `e287c2ed89ca0e4f3f4c59f0b95d953bb187be1a4f2d09ae0392407c1aea828c` |
| `docs/contracts/online-guessing-osd-v1/guessing_prefix-header.txt` | `85bd7478cc9b46e4ddcb882e03e904834cd07c7bc623ecdeb0bf5a23f0b3b77d` |
| `docs/contracts/online-guessing-osd-v1/guessing_prefix.json` | `b9782c4f0191ec5a884f3471f69ef41aa7386a4106d2df270f6cdd062a11cc60` |
| `docs/contracts/online-guessing-osd-v1/loss_on_unitInterval-header.txt` | `bc224e1366aa5de2f5eb46311b3134c56b391cb598d137c914acc183db715064` |
| `docs/contracts/online-guessing-osd-v1/loss_on_unitInterval.json` | `6f494a3958af3d95bbc255e21230cecd365c92f889006e9d3e985735ef88b046` |
| `docs/contracts/online-guessing-osd-v1/loss_step_clamp-header.txt` | `f41c0649d2b82da6bd391a1bd69b03d5efabc6bc8a8f8bcae529b0f10c555001` |
| `docs/contracts/online-guessing-osd-v1/loss_step_clamp.json` | `20cf4696a13bf4e5f2f40309b8296954e044ec416da1c3acd9a98db7391a9613` |
| `docs/contracts/online-guessing-osd-v1/loss_subdifferential_translate-header.txt` | `3e303b7cb3bb4d4fd51349d19ed4c30ca952d8d57ced97fc74ba266ef7fcb811` |
| `docs/contracts/online-guessing-osd-v1/loss_subdifferential_translate.json` | `7d16d3f25a0cf06e7ca447651408b82515638322c4bdb06b5e06cf0b2faea3be` |
| `docs/contracts/online-guessing-osd-v1/loss_subgradient_bound-header.txt` | `934b033137d815b54dd7973a328f2fffe8933908e0437b8358ea02c168edfe3d` |
| `docs/contracts/online-guessing-osd-v1/loss_subgradient_bound.json` | `98335caa7f1149b998c959ad4fedd44f2b48654712812b9afcb712fc65cb22ec` |
| `docs/contracts/online-guessing-osd-v1/loss_subgradient_negative-header.txt` | `5745e4574dfaaf95ca5ea2e87220307b4e8401505750d7eb8eb49eb645361f4f` |
| `docs/contracts/online-guessing-osd-v1/loss_subgradient_negative.json` | `61ed853fa8ac292f6147f9bbcf7ff819351c3ad3193d338107553f1560f76b5b` |
| `docs/contracts/online-guessing-osd-v1/loss_subgradient_positive-header.txt` | `eb6f103874810ecfbbe56892bc55e73f5f9de60c0ba0482b421a32dddc0b131f` |
| `docs/contracts/online-guessing-osd-v1/loss_subgradient_positive.json` | `8a85b389d9219679900e837098e322af7f7d7780c04340d927863ff48b5fae49` |
| `docs/contracts/online-guessing-osd-v1/loss_subgradient_zero-header.txt` | `ef40090cc45c6b5f9f8533128d513def4c209a25c33aacf3100405f386f6ae99` |
| `docs/contracts/online-guessing-osd-v1/loss_subgradient_zero.json` | `918ab9f31624ea291033f6c2e74551e80a98b5384dff1d687774ac2342bde953` |
| `docs/contracts/online-guessing-osd-v2/context.txt` | `deb0e9a941ba4b4d47b8bb786462ef7440bef3c10803adf695caffb043e2f799` |
| `docs/contracts/online-guessing-osd-v2/contract-manifest.json` | `0217e348f8b54a0f4275f0479679495d42bb7dd4c31e89a0459250d083d758c5` |
| `docs/contracts/online-guessing-osd-v2/contract.md` | `3b236291e115bc6cc627fcd9b827293eccabc352b2f64221dbdc5c4159f52aaf` |
| `docs/contracts/online-guessing-osd-v2/current_subgradient_bound-header.txt` | `cf33e00553af8f12b3fb7cc16d9667093d031c33c48f5eb537ac920088ac7b01` |
| `docs/contracts/online-guessing-osd-v2/current_subgradient_bound.json` | `3c3692e46cb28fc1e20dae92f12c3926434316583bcb3fb9dc8a89dc04493864` |
| `docs/contracts/online-guessing-osd-v2/example_2_32-header.txt` | `c783a2dc477402bf38fd856d55570133c5324206a2ab189d41561fab8d03c3ac` |
| `docs/contracts/online-guessing-osd-v2/example_2_32.json` | `37b667b6625b999b648b38ec7f900a02650506e79a4e2c3b88d504b1107a9372` |
| `docs/contracts/online-guessing-osd-v2/example_2_32_average_eventually-header.txt` | `0cd31eb16ead30a23bed6ffa30c7c0952d69f37270f5740cc55f995870e16439` |
| `docs/contracts/online-guessing-osd-v2/example_2_32_average_eventually.json` | `c9170e57c1ee2aa0fe9d3b231381ee50161569cd07890d28373b10d3a6f132a0` |
| `docs/contracts/online-guessing-osd-v2/example_2_32_subdifferential-header.txt` | `61d8e03bcb2e643daee7b008f5d3bc3908a02a4339dd9f92fa5af002bdbc6d2c` |
| `docs/contracts/online-guessing-osd-v2/example_2_32_subdifferential.json` | `403ce58318ef11469d8f0bdfca7aaf9d8c4059e8ec275ac0d9bb153f9898bb67` |
| `docs/contracts/online-guessing-osd-v2/guessing_prefix-header.txt` | `85bd7478cc9b46e4ddcb882e03e904834cd07c7bc623ecdeb0bf5a23f0b3b77d` |
| `docs/contracts/online-guessing-osd-v2/guessing_prefix.json` | `2569ed94fd9770df79b1a58cbe0147e61c383374e267b8df524e4ce40d71e32c` |
| `docs/contracts/online-guessing-osd-v2/loss_on_unitInterval-header.txt` | `bc224e1366aa5de2f5eb46311b3134c56b391cb598d137c914acc183db715064` |
| `docs/contracts/online-guessing-osd-v2/loss_on_unitInterval.json` | `fda6228de3601836ccb503b74f188b6f59c17ff6ac70e556b8b19ff5a15f520d` |
| `docs/contracts/online-guessing-osd-v2/loss_step_clamp-header.txt` | `f41c0649d2b82da6bd391a1bd69b03d5efabc6bc8a8f8bcae529b0f10c555001` |
| `docs/contracts/online-guessing-osd-v2/loss_step_clamp.json` | `eac997b03f6046613cecb13713317aa98ec62e0a78270b672e6b847fd98a5983` |
| `docs/contracts/online-guessing-osd-v2/loss_subdifferential_translate-header.txt` | `3e303b7cb3bb4d4fd51349d19ed4c30ca952d8d57ced97fc74ba266ef7fcb811` |
| `docs/contracts/online-guessing-osd-v2/loss_subdifferential_translate.json` | `02577dff73add937a5297a5b76a6d6a5cb266286697f6065bdf38d1e1691a967` |
| `docs/contracts/online-guessing-osd-v2/loss_subgradient_bound-header.txt` | `934b033137d815b54dd7973a328f2fffe8933908e0437b8358ea02c168edfe3d` |
| `docs/contracts/online-guessing-osd-v2/loss_subgradient_bound.json` | `1b3945d42a72dd994066784d2648d7e9fe364b7a3d9b8a786a64ef43e8b6de56` |
| `docs/contracts/online-guessing-osd-v2/loss_subgradient_negative-header.txt` | `5745e4574dfaaf95ca5ea2e87220307b4e8401505750d7eb8eb49eb645361f4f` |
| `docs/contracts/online-guessing-osd-v2/loss_subgradient_negative.json` | `89858cd6fda10ed8cf486d41f41f38983620f862a10d69a16a94587e0275c201` |
| `docs/contracts/online-guessing-osd-v2/loss_subgradient_positive-header.txt` | `eb6f103874810ecfbbe56892bc55e73f5f9de60c0ba0482b421a32dddc0b131f` |
| `docs/contracts/online-guessing-osd-v2/loss_subgradient_positive.json` | `79314f67136e4f8c929b18e0c5113bfc9555f1d9ad43739a05d2fe79d04cce54` |
| `docs/contracts/online-guessing-osd-v2/loss_subgradient_zero-header.txt` | `ef40090cc45c6b5f9f8533128d513def4c209a25c33aacf3100405f386f6ae99` |
| `docs/contracts/online-guessing-osd-v2/loss_subgradient_zero.json` | `de7452d7de17c99da5123bc1d723d3ea9237b9e69b77bd56d7b7cbf875ddc3be` |
| `docs/contracts/online-guessing-osd-v2/repair.md` | `50ad25fc643d68de4bde832bcc4b7ec160de0640ae43ef2c4355615f839a3d84` |
| `research-wiki/contribution-contracts/ONLINE-GUESSING-OSD-20261004.json` | `388e8d2338a4d31ee8a309de3b2748c40ed1310867d9d8455e00c3c40fe3bfc1` |
| `runs/active_frontier.json` | `567e5873aa2549a83f2820d758069213808da822a93087129877385a1addf7c3` |
| `runs/online-guessing-osd-20261004/active-frontier.json` | `0a2c08979c7c00b3a7a1ce79001a24f4a71148707cf29cd54c53646883e5c279` |
| `runs/online-guessing-osd-20261004/actual-public-candidate-bindings.json` | `3341773622f8c9d642d2daf4d325d0dbb1f86512a31227da7acc8308f4af0197` |
| `runs/online-guessing-osd-20261004/axiom-audit.json` | `db8e688e02022c4d48e492dbce82b72173f68677760f1eb78b6c46253ade7d31` |
| `runs/online-guessing-osd-20261004/binding-inventory.json` | `7c603e676450b6421a9885e8df5e971eeb018b9009540803f721f02d7906f8c7` |
| `runs/online-guessing-osd-20261004/blind-packet-v1.md` | `e0a04970ec0994b389a73eafe91beb46e42aa1e1bef6ce3eb749e86422614334` |
| `runs/online-guessing-osd-20261004/blind-receipt-v1.json` | `535087909b1c9390bb9a4c129abf25e91b5124194c220c1d89996e9f262b2e58` |
| `runs/online-guessing-osd-20261004/blind-reconstruction-v1.md` | `86a41d995bd948a796d13ae1e871a5e43b5b6cb53ee9561b66b9b6b23cebde3b` |
| `runs/online-guessing-osd-20261004/canary-energy-body-repair.md` | `5990412c93ffd31e8b0a8f3aa9f04f8a086d909054a49d62b1047baf62f2b254` |
| `runs/online-guessing-osd-20261004/canary-focused-01-exit.json` | `7f1be73a3f716f96a4a5dd1d1c46174f57e923f2cea3977ed2e69fed7de3f817` |
| `runs/online-guessing-osd-20261004/canary-focused-01.log` | `bd8f9f4f049d3e5f24096bcff689f2e7f854c65661d942ff8dc3d78a64120261` |
| `runs/online-guessing-osd-20261004/canary-focused-02-exit.json` | `db35b834075aedad90505b65778ffac7c17d7621b8baeed3035d7a9040e133ee` |
| `runs/online-guessing-osd-20261004/canary-focused-02.log` | `462ad906f2b5608ecb5e4c1db9c0bffe0c829be73f2a5cc12afe015935608f8c` |
| `runs/online-guessing-osd-20261004/candidate-memory-digest.md` | `d8decd1f3a4cce99bc507d9cc2896ad2e4771a5c3949189552af63e337f62330` |
| `runs/online-guessing-osd-20261004/candidate-retrieval-index.md` | `a970c6163164eeab5c5732ad9ce834b3d1295e291fa8676ef822dcd1a42f3315` |
| `runs/online-guessing-osd-20261004/candidate-technical-gates.json` | `54eecc7686e7cc859338b893ad6b2899c599a35e5247ddef37f974ffe860a20f` |
| `runs/online-guessing-osd-20261004/compiled-dependencies.json` | `25a6d65c377aba367709e10b4823f539ee521dc6c13ec3f16e1a8346d3994445` |
| `runs/online-guessing-osd-20261004/context-probe-01-exit.json` | `dfd7da82e3b44fa43ca2372c5d4deb59f46f14be574b5cc29cc3630c763b11d1` |
| `runs/online-guessing-osd-20261004/context-probe-01.log` | `80226337d75675f43835e9727f1fb58956ea014df5efeae8cbb0f564d6470800` |
| `runs/online-guessing-osd-20261004/contributor-gate-02-exit.json` | `259d60249ee8690ab47dbc41db129b033155afd91dd9acd24b4db73fa6269ce8` |
| `runs/online-guessing-osd-20261004/contributor-gate-02.log` | `c47f01393b670b778fb088356f6f76e8f8217c9a0403ddb803cb6335379db501` |
| `runs/online-guessing-osd-20261004/current-historical-osd-boundary.md` | `f3f8d4903d405b48035628ad5f61d1dfc4c8a54321a45ca6abee293169c356fc` |
| `runs/online-guessing-osd-20261004/draft-freeze.json` | `ff3ab0b29d9e8fc0d3a03b6a21c970786afdf438a2426047ae23ca6626ef3559` |
| `runs/online-guessing-osd-20261004/final-reader-packet.md` | `eec6ab36f9b8b2fe095b925a7cc7e3078fbf4b79ccf39de541081abbcdf43ff1` |
| `runs/online-guessing-osd-20261004/full-harness-02-exit.json` | `b96d9420fdcac21801eb7816ecfc39e607fe3479c6b2e4147effdae1eda64b11` |
| `runs/online-guessing-osd-20261004/full-harness-02.log` | `62720705c41e83190fada824f7235508a82bf22e0305f6771c2d47be74002a7f` |
| `runs/online-guessing-osd-20261004/graph-check-exit.json` | `c05d074734c6de7b64cd623e1fa0f154ae29113e4161378106112f4574856b40` |
| `runs/online-guessing-osd-20261004/graph-check.log` | `938bf688e9aef7a3aa33c3c066994682461bbc1efaac36cf043e856b063265b9` |
| `runs/online-guessing-osd-20261004/guessing-performance-01-exit.json` | `b994ea4326672a3c050f54680bf9336079e4406980a80e0ea2d5f757766b2c83` |
| `runs/online-guessing-osd-20261004/guessing-performance-01.log` | `b16e8fcb37a69f3ae2454b508aee896b0729815cfd9e73f9a5c4971a44d439d8` |
| `runs/online-guessing-osd-20261004/leaves/canary-01.lean` | `eee4c0e913d3f69f5f66638b6c3ab13e62fc5c8e36314fd95f9a9b6c8324c9c1` |
| `runs/online-guessing-osd-20261004/leaves/guessing-performance-02.lean` | `53b245859e91320d29a3e1cc8f0e279a33a1d45eb7faaf3732d8fbda666c4cfb` |
| `runs/online-guessing-osd-20261004/leaves/public-import-order-01.lean` | `1543764ae3f8b686a844aa748df9f7c059ce0de8c824e56db63ce578b63cd4dc` |
| `runs/online-guessing-osd-20261004/leaves/public-names-axioms.lean` | `024870579263ec1ebab6ab4720294fcf5ea976017df839d3649e290cd8c3a857` |
| `runs/online-guessing-osd-20261004/native-fence-assumption-repair-v2.md` | `50ad25fc643d68de4bde832bcc4b7ec160de0640ae43ef2c4355615f839a3d84` |
| `runs/online-guessing-osd-20261004/native-safe-verify-file-scope-correction.md` | `2405da0096d97ad71faf1c8a90df41ebb3d357b52ddc56011cc07d7c419a5fa1` |
| `runs/online-guessing-osd-20261004/performance-prefix-body-repair.md` | `075b06c10264c4096baae34e1b38122bffd0a8a4336b1052f7a5e9092f31c280` |
| `runs/online-guessing-osd-20261004/piecewise-math-layout.md` | `9875828a6aa9054a70ef8a21771ed408e1fc843882da3fe21b84c248f94bccb3` |
| `runs/online-guessing-osd-20261004/proof-obligations.json` | `87f1233a9c60de650ee9219d1c70a3b48866b56099c880f1039c9e76070239ae` |
| `runs/online-guessing-osd-20261004/public-body-receipt.json` | `17472f4b8c37281196d402b6551ae997dfa482670ed84fe787bd14fc008d5e83` |
| `runs/online-guessing-osd-20261004/public-body-review-packet.md` | `4ce1270db33d8686fa97891e4ac81b1813b1c4b050ab765e59f06643880675bf` |
| `runs/online-guessing-osd-20261004/public-body-review.md` | `4b77025a16edb61d8e0891b454b4d7f983575a5a069f1b938ca8eea8e5fb8e1f` |
| `runs/online-guessing-osd-20261004/public-canary-fingerprints.json` | `10a61f20e3471767a0b1c87690a59d1c91bab0827df5fcc2faa41dbe08195a46` |
| `runs/online-guessing-osd-20261004/public-candidate-fences/current_subgradient_bound.json` | `31b65699744b289b8a6a1fd572c385da08d0ab30c6c0184411c66401d4e3f1a1` |
| `runs/online-guessing-osd-20261004/public-candidate-fences/example_2_32.json` | `3578338a77918c00c7ec81e455d6a5156c81d23bbc640c2641b28636db3af0aa` |
| `runs/online-guessing-osd-20261004/public-candidate-fences/example_2_32_average_eventually.json` | `c38301a28fe1ef5f2f017ba5bf80c326c60d005bf176523da095493a13c9afec` |
| `runs/online-guessing-osd-20261004/public-candidate-fences/example_2_32_subdifferential.json` | `1f2d4b875ab30c28a33acc62951cc6b6ea39093bb47e1c2878b506c1d7726f33` |
| `runs/online-guessing-osd-20261004/public-candidate-fences/guessing_prefix.json` | `82ed7d4f83f0a954d3e5a6a9f0350e1fc9094b711564f1ee190a317d6b08a802` |
| `runs/online-guessing-osd-20261004/public-candidate-fences/loss_on_unitInterval.json` | `f613acceb2a81d55e6df3f637d52d29fd5cdcb6a13f12be5607c0d6b4ed88ad3` |
| `runs/online-guessing-osd-20261004/public-candidate-fences/loss_step_clamp.json` | `f4ea99bdf8b74b6f689b2157f1a39c5341a1a1fd07a7e6cb9f79a232661c76be` |
| `runs/online-guessing-osd-20261004/public-candidate-fences/loss_subdifferential_translate.json` | `a349e8668b36e3e4a6bcb689cc66ee6cb9b44d437814d4a1cb28192793e6b357` |
| `runs/online-guessing-osd-20261004/public-candidate-fences/loss_subgradient_bound.json` | `6687260ff3c3ace1049012db817f028c1da950155351f6b7bca5b8d91e39e3b0` |
| `runs/online-guessing-osd-20261004/public-candidate-fences/loss_subgradient_negative.json` | `2af09cb037046e577719b5a4820dcbda8d9d722dc0c5226a702344a63bd686eb` |
| `runs/online-guessing-osd-20261004/public-candidate-fences/loss_subgradient_positive.json` | `fb7fc653f65e495415c0b71da9ac895e699fc983519c46f179c65476ab346676` |
| `runs/online-guessing-osd-20261004/public-candidate-fences/loss_subgradient_zero.json` | `008c9235ccd85660fc7d80b23687ff792a0a050f106edcb11e9d966da9152269` |
| `runs/online-guessing-osd-20261004/public-focused-01-exit.json` | `b5f7b8e30d4eca3f20cd7357b8fd1aed2e62f476b280c3f2d3cbdae8e421789f` |
| `runs/online-guessing-osd-20261004/public-focused-01.log` | `dfb776bdbd524337291f15a4d913092c6bf0cbe9843d0e44f1fe731a40361017` |
| `runs/online-guessing-osd-20261004/public-focused-02-exit.json` | `1c4378d6774411b1042fbf83e7e0e3d6867478565aa1b73a81d42599b6b9451b` |
| `runs/online-guessing-osd-20261004/public-focused-02.log` | `111c65872dbc0184c447f2354705c4111a73a618846b9d3a04e4cee06bacf741` |
| `runs/online-guessing-osd-20261004/public-import-order-repair.md` | `9de3f93195c85e171c95af33765649f37f6b92ef9a4e7c9b101b4c52db7d3907` |
| `runs/online-guessing-osd-20261004/public-names-axioms-exit.json` | `4d8666a832eaccf08c9ce34994faf0477d9bb76def9594c87e0437087510eb0f` |
| `runs/online-guessing-osd-20261004/public-names-axioms.log` | `36fb8ba44cc4ffa55a35e227a858c650d6a51ba28018ebf54f858673f4fb23df` |
| `runs/online-guessing-osd-20261004/public-reviewer-native-trial.json` | `a606356483c1678388dda743fb20694c24c2ef9a347fc9c3def9891ce576703b` |
| `runs/online-guessing-osd-20261004/public-terminal-retrieval-exit.json` | `cc1f6a8cdd52dc3102b85f20f1aea2e2185d44ebc9d62afee175c7f37e7f9d09` |
| `runs/online-guessing-osd-20261004/public-terminal-retrieval.txt` | `3b85470404b026830c14befce66bbe8c9874cf294b1e66b29155c5844808178f` |
| `runs/online-guessing-osd-20261004/registry-final04.json` | `b52c0be85c8bb4ef11c91ad87531462dcc22f5d5dd69526fe8ddad12bc95cc04` |
| `runs/online-guessing-osd-20261004/root-01-exit.json` | `7b802949ec4075358ed4fc1ec6b75a1cef970f1b4db5cdd6b6c413c655db5f21` |
| `runs/online-guessing-osd-20261004/root-01.log` | `2011a02ffa9f5c51f2d86b6e7729ee8a6d5c151b40e3671990394d096ae80154` |
| `runs/online-guessing-osd-20261004/scoped-frontier-comparison.md` | `3a8ba32f73a46372053665d8e4dfc932b7ab7fd85d404b514bc3d08b30445120` |
| `runs/online-guessing-osd-20261004/scoped-frontier-shadow-v2.json` | `0c9ffe4d76b3a5abc3ad1e921a7d81c6751c86307ea8d41dcd3655d1fe028c16` |
| `runs/online-guessing-osd-20261004/scoped-memory-digest.md` | `5820595e3d4b4217a992ea4e5833d1d39fbfd86ece105a210857e43924809872` |
| `runs/online-guessing-osd-20261004/search-index-equivalence.json` | `bb6e8e30ec55b7e1a5d08e8b3c9eb0e5d6e7e5e53c0782330f13a8d6a1bfad0c` |
| `runs/online-guessing-osd-20261004/signature-probe-01-exit.json` | `24dda6fd3ab68f0852e17e97c1cd81cb1f19bfe44e29cf053bceef7111d286f9` |
| `runs/online-guessing-osd-20261004/signature-probe-01.log` | `169cbb43fd05f3060fe3818d4d7860b0ee8210b7b4d11e4c7f21b1cc02854cbc` |
| `runs/online-guessing-osd-20261004/site-build-01-exit.json` | `610f32d705843386b1df0825f220036b22c2459d072940bf3aa75be0525d2acc` |
| `runs/online-guessing-osd-20261004/site-build-01.log` | `50920af417c6faa1dfbc677c7836f135172dbfb0f9d87a8d147919c435e860dd` |
| `runs/online-guessing-osd-20261004/site-build-04-exit.json` | `0f4ec0e432fb54828edd168edb6a4e053f1ff80f9e1b1d4ab104afaec1b4ea6e` |
| `runs/online-guessing-osd-20261004/site-build-04.log` | `5a080db58dcf6fd602b41f688ac55a5fd41cacccc8bf12d6bccb76ddb9900dc0` |
| `runs/online-guessing-osd-20261004/site-check-02-exit.json` | `7ddc346397d38a70567ff8efe8053864a87480b423673f34e6e0a812b4999a09` |
| `runs/online-guessing-osd-20261004/site-check-02.log` | `03041ced66d897dc24cfa3963937f9ee6a663ecc82f2e250eac9bd0345e1805f` |
| `runs/online-guessing-osd-20261004/site-check-04-exit.json` | `55f3d01892866d7ae7650d3377280a6b53decad7fb1b1ddf46bdf420c2094000` |
| `runs/online-guessing-osd-20261004/site-check-04.log` | `d8ab580fef6751e7528f3446f01024795d700d0e6630811d10f57040a7be564f` |
| `runs/online-guessing-osd-20261004/site-reader-snapshot.json` | `0b3eb21595d21b2b188a7c38d2c95e4a117ce26e0def013c70af0352838815f2` |
| `runs/online-guessing-osd-20261004/site-registry-dependency-repair.md` | `2b13ebeba10dce266ee44d1c2a3ec76765e877d19ad14231b2745694db465ebb` |
| `runs/online-guessing-osd-20261004/site-search-index-repair.md` | `d39e4d4dd4e0355e9f6c17ba61997478dd1ed34b0d3258fce5c1243462961666` |
| `runs/online-guessing-osd-20261004/source-card.md` | `2e2cb00aafd26d924d00fb2f64017bab36ef56291883a92e41749d52a4257761` |
| `runs/online-guessing-osd-20261004/source-contract-receipt-v1.json` | `344eb7dd83273e4ac50a0eb1ffc7c3a92785245d751c56c998f77f031051cee5` |
| `runs/online-guessing-osd-20261004/source-contract-receipt-v2.json` | `cd0f6dafed54d7936356450e5451a20674342234bfcb40714bd539af216e6770` |
| `runs/online-guessing-osd-20261004/source-contract-review-v1.md` | `d4f9db1040dae2600a5e7d8b9715df828d4fe9f314e93deb20d2eec74bb3d232` |
| `runs/online-guessing-osd-20261004/source-contract-review-v2.md` | `8ac49326b41c2150bed5d29b89efce7164ca571697c721897c8c7475d0eeb614` |
| `runs/online-guessing-osd-20261004/source-pages.txt` | `619e7cf94f45a4ede0a4bd377dd79892b7cc09bf56f7f44247eb14bdf2937980` |
| `runs/online-guessing-osd-20261004/source-review-packet-v1.md` | `75f963e32555c6134125cad7e7c02c74ed905cefab689bf34d938c12eab29aa5` |
| `runs/online-guessing-osd-20261004/source-review-packet-v2.md` | `f664cd8bea4e77b83be7fcc990d7fba6df707bbba9f162104b53235abbcb160a` |
| `runs/online-guessing-osd-20261004/stacked-base-current.json` | `76748727c9fd421596e0cd03b8ce4deb25e6ac31a2885f10a21447801c4dc51c` |
| `runs/online-guessing-osd-20261004/support-fence-01-exit.json` | `a5c801492c1837136248ecd81d6ead1a13547ee6339576bbf2f587cc3d8adba3` |
| `runs/online-guessing-osd-20261004/support-fence-01.log` | `0cb81b6e032a36427fbd27949c51bd76de2cadfe97c4a55c7468bc29f11b4f55` |
| `runs/online-guessing-osd-20261004/support-fence-02-exit.json` | `8eff2b20bba292063686fcf7b1419195a7a7ceb522b29d24fd4698536a59f65e` |
| `runs/online-guessing-osd-20261004/support-fence-02.log` | `0cb81b6e032a36427fbd27949c51bd76de2cadfe97c4a55c7468bc29f11b4f55` |
| `runs/online-guessing-osd-20261004/support-fence-provenance-repair.md` | `cbc3d61d007e2e9b709f1e2c57f25f06aa80a8d3084b7d7dd7e25b1d0fc3a0e4` |
| `runs/online-guessing-osd-20261004/support-fence-v2-verification.json` | `65869131da82da67c179b5d9e93756861850b26d57d93630c894a3a64eea3595` |
| `runs/online-guessing-osd-20261004/tests-01-exit.json` | `bfa6d4e2ad28a7de7340c02950482bae5e68ee2c002cf47e96dc778c43070564` |
| `runs/online-guessing-osd-20261004/tests-01.log` | `cd51703c1753fe236091ba673de02c1a5b5545a092aa85eaf61f2bb11d540541` |
| `runs/online-guessing-osd-20261004/trials.jsonl` | `1e1524565e8c31b95848aa4dbc1f2b7544a212600877527e41a0de1598799704` |
| `runs/online-guessing-osd-20261004/verify-proof-graph.py` | `2f54757f55039f5d33641d25995a46a97b6a8a5dca3b357ee55f4de290167440` |
| `runs/online-guessing-osd-20261004/verify-roundtrip-bindings.py` | `8f274dea60d1e2469f59879099a5399b9bb3f1f6fae8da809898cadd0e53af1a` |
| `runs/online-guessing-osd-20261004/visual-review-image.json` | `51616406b29bdce78f73f6fcf504fbc9bf007b90e85b7d86b4940a51b192e0f9` |
| `runs/online-guessing-osd-20261004/visual-review.md` | `2b1baf10bb511fba998d211846a946cac505d081a09d441c125f701d64b5489c` |
| `runs/online-guessing-osd-20261004/workflow-audit.json` | `2c498f0b618a02dc9e293f802ed5be08473f91de44dc1b24cc0ac4661c0a1943` |
| `tmp/guessing-search-index-site02.json` | `7650318d52c8054221b6162d0bdb8f721c6724f9f2c8692b95f3b6da959afa3d` |
| `tmp/online-guessing-osd-context-v1.lean` | `9b887d85174707df878093452e564c0a2212e52fea8724fd389b802a456c4051` |
| `tmp/online-guessing-osd-signatures-v1.lean` | `40f0a1b5a8bff679e072e39ffa3084b1563c789838c7eb26a241eb7c681902a9` |
| `tools/abrl_lifecycle.py` | `7615541e66a372e939ea2d18684ce78a8f3d8f1202894840ef7fdfdc703c4310` |
| `tools/bandit.py` | `d4a5a27189b200ac977e5b6b3ce3bce5880dff1b7530461aab6860352199da9c` |
| `website/_site/books/online-learning/index.html` | `6acf9fd8f7ed619c9d4416b981c48dfb1a326a1ff8e696dd02a303658e93f354` |
| `website/_site/books/registry.json` | `65d72a931019a74ae1716c490506cb9e787169acf51a361379e66cf0932aa148` |
| `website/_site/chapters/online-guessing-osd/index.html` | `9bcb9781f1f12bf0b53c7255d878c8d9f30990583ae664dbda16f4af48e14bfe` |
| `website/_site/lean-graph/search-index.json` | `e5d61b39a3ab1b93def68315ef667a70bf7124e84b0449371b4e1ec02f9f5d6f` |
| `website/_site/modules/banditrlproof-onlineguessingsubgradient/index.html` | `9b11cc4f5b26276deffecde1e9a1c1650fee5f80c9746dc1e1ee69bdc88bc28e` |
| `website/content/books.json` | `85782c00f5cfcb80596ec631f802ac7132bd86e71368ae3c1ba9d6e5247045b2` |
| `website/content/chapters.json` | `e69a8c1b7e4eb7d56fb2b591c59ee1fcf8f19f7cb8ed7e099b37cf1f56a3f654` |
| `website/content/highlights.json` | `ca10705c1dc5d2eaeeab70ac6373cb33a6ae624a9f06affc047d378471ee6494` |
| `website/content/readings.json` | `68317453ac75218e987fd5a741cf46fe5f899059fba9fe2ecbb1d0de1ef3c399` |
| `website/scripts/build_site.py` | `8e45a4a9f3151860840a69279c21fcf55a4254e4d47e688e5198e14db6aa9def` |
| `website/scripts/check_site.py` | `f6d6a83f2b097f2b5848beccd13faaed29275ae7f65d1ed1de8e9d661db962a2` |
