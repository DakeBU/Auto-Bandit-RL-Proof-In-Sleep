# Version 2 draft-contract repair review: Theorem 2.22

Verdict: **accepted-with-explicit-delta for full-source contract coverage**. This accepts the repaired statement specification only. It does **not** accept a proof of either full terminal, certify compilation, or claim a completed source theorem.

Reviewer: the separate automated actor `/root/source_reviewer`, requested GPT-6 Astra / medium, dated 2026-10-03. This is not external-human review. The original `draft-source-review.md` remains preserved: its missing-gradient-endpoint finding was valid for version 1. This receipt supersedes only that contract-coverage rejection for the version 2 files bound below.

## Read inventory and source binding

All seven files below were read in full from `E:/ABRL/worktrees/research-online-book`; SHA256 values bind their raw bytes.

| File | SHA256 |
| --- | --- |
| `docs/contracts/online-subgradient-differentiability-v2/context.txt` | `0638affef80952cde5777ece5cdcf2fa8ec46efd2c3ada2c670de2b0df8f5348` |
| `docs/contracts/online-subgradient-differentiability-v2/full-header.txt` | `7029e22ec2d7e84879a3c97109e5d17709372628fa516b309c2d5391ef5e94b9` |
| `docs/contracts/online-subgradient-differentiability-v2/interior-header.txt` | `051a7e1df02b4405a9dcebc5a48a586aee4a9f909ff862e28fb5ea4deb66f9dd` |
| `docs/contracts/online-subgradient-differentiability-v2/gradient-header.txt` | `fd8f6b3d690b24692f0ab8462f8ab9a842b9381c96717da81c217ecf9254381e` |
| `docs/contracts/online-subgradient-differentiability-v2/contract.md` | `9a44687bb43edd524ec3dcbca227410d507295681d19ca731463ffb03a9d64fe` |
| `runs/online-subgradient-differentiability-20261003/blind-packet-v2.txt` | `62137daa802f8946f6c435fb1b66ac1bc7bd2ef130489464a984cfd4cc7e9bad` |
| `runs/online-subgradient-differentiability-20261003/blind-reconstruction-v2.md` | `89e90ba9abad3c07c3c7150f50fff62cef83b97a56ed4c22dc408285ca3d56a9` |

The source is the same original Orabona arXiv:1912.13213v10 PDF freshly hashed and page-extracted during the immediately preceding version 1 review: `E:/ABRL/worktrees/research-online-ogd/tmp/pdfs/orabona-v10.pdf`, SHA256 `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17`; Theorem 2.22, printed page 17 / PDF page 29. Its conclusions are differentiability iff singleton subdifferential, together with identification of that singleton element as the gradient. No different source or theorem interpretation was introduced for the repair.

## Exact repair and seven-slot check

Version 2 preserves the context, equivalence header and singleton-to-interior header byte-for-byte: their hashes match version 1. It adds `theorem_2_22_gradient`, universally quantified over a real h which agrees with f in an ambient neighborhood of x and is differentiable there at x, concluding `SourceSubdifferential f x = {gradient h x}`.

| Slot | Repair assessment |
| --- | --- |
| 1. Objects/spaces | Finite-dimensional real inner-product geometry remains the coordinate-free Euclidean presentation. f is EReal-valued; h is an actual real-valued local representative with arbitrary irrelevant extension away from x. No global real-valuedness of f is added. |
| 2. Quantifiers | h is universally quantified subject to local agreement and differentiability. The endpoint applies to every admissible representative rather than an unrelated existential witness. The singleton identifies one vector supporting f against all ambient y, with uniqueness. |
| 3. Assumptions | Extended convexity and finiteness at x remain the source assumptions. The companion adds only the hypotheses specifying the actual differentiable representative whose gradient it identifies. No explicit properness, interior, closedness, boundedness, or global convexity of h is added. The companion's finite-x premise is redundant under local equality but harmless and source-aligned. |
| 4. Conclusions | The new singleton equality supplies both support by the actual derivative-representing gradient and uniqueness. Together with the unchanged equivalence this covers the source's gradient-identification clause, closing the v1 omission. |
| 5. Normalization | `gradient h x` is the derivative's representing vector, not a support witness renamed as gradient. The existing support definition retains the correct inner-product displacement y-x and coefficient one. |
| 6. Probability/feedback | No probability, feedback, stopping, regret, or stochastic-selection claims are introduced. |
| 7. Boundaries | Neighborhood equality includes x and a full ambient neighborhood; it is neither punctured nor relative-domain agreement. Infinite values away from that neighborhood remain admissible. All boundary exclusions must be derived by the unchanged full theorem, not enforced by a new interior premise. Finite dimension, including dimension zero, remains explicit. |

For two admissible representatives h and k, this endpoint equates the same subdifferential to both singleton gradients, so their gradients agree. It therefore expresses representative independence directly through universal quantification; no extra choice-defined gradient object is necessary for this contract. On the singleton side of the equivalence, obtaining a differentiable representative and then applying the companion will identify the existing singleton witness with its gradient. This logical composition covers the complete intended source conclusion without strengthening the full theorem's assumptions.

The source-blind version 2 reconstruction correctly recognizes the new universal h quantifier, global support, representative independence, and absence of added properness/interior assumptions. It matches the actual header. Its standard interpretation of gradient as the derivative-representing vector is appropriate for this finite-dimensional real inner-product context.

## Remaining scope and status

Required semantic contract repairs: **none** for version 2. The existing document title still says v1 while its appended repair section explicitly records version 2; this is an editorial label, not a mathematical contract change. The versioned folder, byte bindings and repair section unambiguously identify the reviewed specification.

The original full equivalence and new gradient identity remain proof obligations. The earlier scratch singleton-to-interior leaf alone proves neither full endpoint. No later continuity prerequisite was inspected or accepted in this repair review. Any eventual source-facing acceptance must bind actual proved public declarations for both endpoints, the reused definitions, and separate compiler/integration evidence. Theorem 2.22 and Chapter 2 must remain incomplete until those obligations are met.
