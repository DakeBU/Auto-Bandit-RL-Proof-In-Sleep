# Online Learning Chapter 1

Task id: `ONLINE-BOOK-CH1`
Kind: `theorem`
Status: `candidate`
Harness: `hierarchical`

Total Goal is chapters 1-16. Current Chapter 1 terminal is Theorem 1.3 with the specified causal running-average predictor and exact 4+4 log T guarantee. Foundations include regret/information semantics and the expected squared-loss motivation. Inventory: docs/contracts/online-book-v1/source-inventory.json. Chapter 1 is not accepted.

Lemma 1.2 is focused-compiled, native fence passed; root/Tests/full harness/site and complete Chapter 1 semantic review remain pending. New module is not yet imported by the public root. The old fixed-step OGD package remains a separate accepted package on open PR #116. This branch is stacked on its exact head.

Candidate update: all seven source groups have compiled interfaces; latest root/Tests pass8998jobs, full contract checker passes24interfaces/9contexts. Local full harness remains failed (9Pythonerrors); external complete gate and PR delivery remain pending. See chapter-one-completion-audit.md and full-gate-repair.md.
