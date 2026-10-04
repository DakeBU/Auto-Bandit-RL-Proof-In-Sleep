# Example2.32 v2 native-fence metadata contract review

Verdict: **accepted-with-explicit-delta**, only for the v2 contract metadata repair. No source/body/public/package acceptance is implied. Actor `/root/source_reviewer`; requested GPT-6 Astra / medium; distinct automated review, external_human=false. Runtime model identity not independently verified. No production/contract/old evidence edits, trial or shadow mutation performed.

All48 actual-read v1 rows were independently rehashed: zero drift, including original PDF (`cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17`), original blind packet/report/receipt, imported APIs and probes. The original PDF pages13–15,27,31–32 and all twelve mathematical targets were read in this continuous review. Freshly read all28 v2 contract-directory files, new review packet and repair record, old failed native logs/exits and failed comment-repair explanation, v2 native-verification evidence, and actual scoped implementation of normalization/header extraction/fence creation/safe verification and CLI plumbing. Whole code files are raw-bound; unrelated CLI behavior is not audited.

## Actual guard semantics and repair

`normalize_statement` collapses whitespace. `lean_declaration_header` strips comments and extracts the declaration through its top-level assignment. `make_statement_fence` stores the normalized whole header/hash and supplied assumption strings. `safe_verify` compares the extracted whole-header hash, then checks that each normalized source_assumptions string occurs in that header. It additionally scans selected Lean files for forbidden declarations. The CLI forwards these fields; no inspected guard change or worktree diff was present.

The v1 provenance identifier was never a Lean premise and is absent from the normalized header. Both retained01/02 native checks correctly failed despite matching statement hashes. A top-of-file comment cannot repair this header-only test. The earlier comment-repair note's interpretation is incorrect and remains rejected history. This review does not reinterpret either failed command as passed.

V2 preserves **all twelve raw header files and the raw context byte-for-byte**, the exact normalized statements and native hashes. I independently recomputed each normalized-header SHA256 and compared v1/v2/manifest values. The new arrays contain13 actual conditional premise fragments: positive and negative hxy (one each), actual-support hg (one), selected-query hx (one), strict eta/label prefix (two), finite performance hx1/T/played labels (three), and eventual hx1/all-time labels/comparator/epsilon (four). Every fragment occurs in its exact header and expresses a real hypothesis, not a provenance label. Five genuinely unconditional targets have empty arrays: translation, matched-point interval, combined branches, proper/subdifferentiable loss, and clamp. Their full typed parameters, branch conditions and conclusions are still bound by the unchanged whole-header fingerprints. Provenance remains separately recorded. The finite performance comparator restriction occurs inside its quantified conclusion and is covered by that full header/hash, even though it is not duplicated as an assumption-string array item.

## Additional verification-scope finding

**Do not treat the observed v2 native pass as actual candidate-header verification.** The actual implementation extracts the header from `root / fence['file']`; `--lean-file` only selects forbidden-token scan files. Current v2 fences still name `tmp/online-guessing-osd-target-v1.lean`. Therefore `support-fence-v2-verification.json`, despite naming `guessing-support-02.lean` in --lean-file, compares the target-file header, not that candidate's header. This does not invalidate the repaired contract metadata, which is this review's sole scope. Before any body/public acceptance, require fresh evidence binding the actual candidate path with the same immutable statement/hash and these premise fragments, or independently extract/compare every actual candidate header against the frozen target. Preserve the current evidence and avoid describing it as already satisfying that body fence obligation. No candidate body or its compilation was independently reviewed here.

## Seven-slot preservation audit

1. Objects remain scalar finite absolute loss embedded in EReal and the actual shared [0,1] projection domain; properness is produced, not a new assumed finite-loss surrogate.
2. All-real translation and three full global-support equalities remain unchanged, with closed [-1,1] at equality and both necessity/sufficiency required. Conditional sign/support premises are now correctly represented in metadata.
3. Actual canonical current-function/current-point selection and strict-prefix recursion remain the same; no zero tie-break, executable oracle or universal adaptive-support interface has been added.
4. The actual clamp and source algorithm identities remain unchanged. Metadata substring checks are not proofs of choice correctness, projection or actual body consumption.
5. Finite regret still uses one horizon-specific actual trajectory and all feasible comparators, with source labels and initialization in [0,1]. No comparator enters the algorithm.
6. eta=1/sqrt(T), T>0, same-run selected norm bound1 and diameter1 remain unchanged; no future-gradient optimization or anytime interpretation. All unrestricted helper degeneracies remain.
7. The eventual conclusion remains one-sided upper control for a horizon family, not signed Tendsto0/absolute BigO. The explicit canonical implementation, helper generalizations and finite-real embedding deltas from v1 remain. Universal legal/adaptive support-family audit and Chapter2/book completion remain open.

## Decision and mandatory next work

No further mathematical target repair is required for v2 stabilization. V1 remains an accepted source-mathematical contract with misconfigured native assumption metadata; this separate v2 review repairs that metadata and preserves the failed guards. The reported eight compiled bodies are not accepted by this contract review. Actual body/canary/source comparison, candidate-path fence evidence described above, public/root/Tests/full harness/axioms/dependency/reader/registry/binding/PR gates remain separate. No merged/live, wholechapter/book or external-human claim is made.

## Raw reviewed files

| Path | Raw SHA256 |
| --- | --- |
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
| `runs/online-guessing-osd-20261004/source-review-packet-v1.md` | `75f963e32555c6134125cad7e7c02c74ed905cefab689bf34d938c12eab29aa5` |
| `runs/online-guessing-osd-20261004/source-card.md` | `2e2cb00aafd26d924d00fb2f64017bab36ef56291883a92e41749d52a4257761` |
| `runs/online-guessing-osd-20261004/source-pages.txt` | `619e7cf94f45a4ede0a4bd377dd79892b7cc09bf56f7f44247eb14bdf2937980` |
| `runs/online-guessing-osd-20261004/proof-obligations.json` | `87f1233a9c60de650ee9219d1c70a3b48866b56099c880f1039c9e76070239ae` |
| `runs/online-guessing-osd-20261004/draft-freeze.json` | `ff3ab0b29d9e8fc0d3a03b6a21c970786afdf438a2426047ae23ca6626ef3559` |
| `runs/online-guessing-osd-20261004/blind-packet-v1.md` | `e0a04970ec0994b389a73eafe91beb46e42aa1e1bef6ce3eb749e86422614334` |
| `runs/online-guessing-osd-20261004/blind-reconstruction-v1.md` | `86a41d995bd948a796d13ae1e871a5e43b5b6cb53ee9561b66b9b6b23cebde3b` |
| `runs/online-guessing-osd-20261004/blind-receipt-v1.json` | `535087909b1c9390bb9a4c129abf25e91b5124194c220c1d89996e9f262b2e58` |
| `runs/online-guessing-osd-20261004/context-probe-01.log` | `80226337d75675f43835e9727f1fb58956ea014df5efeae8cbb0f564d6470800` |
| `runs/online-guessing-osd-20261004/context-probe-01-exit.json` | `dfd7da82e3b44fa43ca2372c5d4deb59f46f14be574b5cc29cc3630c763b11d1` |
| `runs/online-guessing-osd-20261004/signature-probe-01.log` | `169cbb43fd05f3060fe3818d4d7860b0ee8210b7b4d11e4c7f21b1cc02854cbc` |
| `runs/online-guessing-osd-20261004/signature-probe-01-exit.json` | `24dda6fd3ab68f0852e17e97c1cd81cb1f19bfe44e29cf053bceef7111d286f9` |
| `tmp/online-guessing-osd-context-v1.lean` | `9b887d85174707df878093452e564c0a2212e52fea8724fd389b802a456c4051` |
| `tmp/online-guessing-osd-signatures-v1.lean` | `40f0a1b5a8bff679e072e39ffa3084b1563c789838c7eb26a241eb7c681902a9` |
| `BanditRLProof/OnlineSubgradientDescent.lean` | `6ba8586e1691babc2db3e0c0fcddb69b4236e16f9f192c464b4c04262e854f1c` |
| `BanditRLProof/OnlineGuessingOGD.lean` | `6e99965d95e7016bc40c2f39e51f7dff4bf381c42b028e39584f703302eda8bd` |
| `BanditRLProof/OnlineSubgradientBasic.lean` | `4c17a466091b88d90451be897a2f01afa204b41933191244e0093e48396d1962` |
| `BanditRLProof/OnlineClosedProper.lean` | `9a5fcfb9e26a2a35d8e5bb7ef7b7a7dfd65a7f1c8daab03faebb51e41d54e7c6` |
| `BanditRLProof/OnlineGradientDescent.lean` | `e7edba540c2f60032bb4a34aaf0768b3107b94276b67b6f41fc289009c8924c1` |
| `BanditRLProof/OnlineSubgradientAbsolute.lean` | `17157c976889f078d02f183b55edf2821e29efa5aa32d4bfff309c2b3713db0c` |
| `../research-online-ogd/tmp/pdfs/orabona-v10.pdf` | `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17` |
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
| `tools/abrl_lifecycle.py` | `7615541e66a372e939ea2d18684ce78a8f3d8f1202894840ef7fdfdc703c4310` |
| `tools/bandit.py` | `d4a5a27189b200ac977e5b6b3ce3bce5880dff1b7530461aab6860352199da9c` |
| `runs/online-guessing-osd-20261004/source-contract-review-v1.md` | `d4f9db1040dae2600a5e7d8b9715df828d4fe9f314e93deb20d2eec74bb3d232` |
| `runs/online-guessing-osd-20261004/source-contract-receipt-v1.json` | `344eb7dd83273e4ac50a0eb1ffc7c3a92785245d751c56c998f77f031051cee5` |
| `runs/online-guessing-osd-20261004/source-review-packet-v2.md` | `f664cd8bea4e77b83be7fcc990d7fba6df707bbba9f162104b53235abbcb160a` |
| `runs/online-guessing-osd-20261004/native-fence-assumption-repair-v2.md` | `50ad25fc643d68de4bde832bcc4b7ec160de0640ae43ef2c4355615f839a3d84` |
| `runs/online-guessing-osd-20261004/support-fence-01.log` | `0cb81b6e032a36427fbd27949c51bd76de2cadfe97c4a55c7468bc29f11b4f55` |
| `runs/online-guessing-osd-20261004/support-fence-01-exit.json` | `a5c801492c1837136248ecd81d6ead1a13547ee6339576bbf2f587cc3d8adba3` |
| `runs/online-guessing-osd-20261004/support-fence-02.log` | `0cb81b6e032a36427fbd27949c51bd76de2cadfe97c4a55c7468bc29f11b4f55` |
| `runs/online-guessing-osd-20261004/support-fence-02-exit.json` | `8eff2b20bba292063686fcf7b1419195a7a7ceb522b29d24fd4698536a59f65e` |
| `runs/online-guessing-osd-20261004/support-fence-provenance-repair.md` | `cbc3d61d007e2e9b709f1e2c57f25f06aa80a8d3084b7d7dd7e25b1d0fc3a0e4` |
| `runs/online-guessing-osd-20261004/support-fence-v2-verification.json` | `65869131da82da67c179b5d9e93756861850b26d57d93630c894a3a64eea3595` |
