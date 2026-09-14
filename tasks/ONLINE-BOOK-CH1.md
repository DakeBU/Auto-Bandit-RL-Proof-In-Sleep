# Online Learning Chapter 1

Task id: `ONLINE-BOOK-CH1`
Kind: `theorem`
Status: `repair`
Harness: `hierarchical`

Total Goal is chapters 1-16. Current Chapter 1 terminal is Theorem 1.3 with the specified causal running-average predictor and exact 4+4 log T guarantee. Foundations include regret/information semantics and the expected squared-loss motivation. Inventory: docs/contracts/online-book-v1/source-inventory.json. Chapter 1 is not accepted.

Initial leaf history: Lemma 1.2 passed its focused build and native fence before public integration. The final candidate now imports all nine modules through the public root and has passed root/Tests, semantic review, contract, axiom, dependency and site checks. The full harness remains failed. The old fixed-step OGD package remains a separate accepted package on open PR #116. This branch is stacked on its exact head.

Candidate update: all seven source groups have compiled interfaces; latest root/Tests pass8998jobs, full contract checker passes24interfaces/9contexts. Local full harness remains failed (9Pythonerrors); external complete gate and PR delivery remain pending. See chapter-one-completion-audit.md and full-gate-repair.md.
