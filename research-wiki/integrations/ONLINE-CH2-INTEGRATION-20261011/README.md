# Bounded Online Learning Chapter 2 integration

This packet integrates six modules into the existing BanditRLProof library and shared Book registry: extended-real convexity, affine/norm examples, first-order convexity, fixed and variable projected gradient descent, and the repaired source-facing regularity interface. It contains 57 declarations, six canary modules, three reading entries and 29 highlights. These are not 57 numbered source theorems and do not complete Chapter 2.

The frozen source is Francesco Orabona, *Online Learning: A Modern Introduction Using Convex Optimization*, arXiv:1912.13213v10, printed pages 9–15 (PDF pages 21–27). The source PDF SHA256 is `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17`. Scope covers Definitions 2.2–2.3 and selected domain/indicator consequences, Theorem 2.4, Examples 2.5–2.6, Theorem 2.7, Algorithm 2.1, Proposition 2.11, Lemma 2.12, both branches of Theorem 2.13 and Eq. 2.1.

## Retained provenance and one well-definedness repair

The production source is frozen at `8045070bf1ee53c83778d04eb168f8ad6f728b59`; source-facing repairs and later independent audits came from PRs #154, #156 and #158. Ten of the twelve production/canary files retain the frozen source exactly after CRLF-to-LF normalization. One canary additionally normalizes only trailing empty lines. In OnlineGradientDescent, the only proof addition is `project_existsUnique`, placed before the unchanged projection choice; trailing empty lines are also normalized. All previous declarations and proof code remain intact. The new theorem was separately source-blind decoded and source reviewed; its code matches the reviewed probe after renaming.

The retained modules contain 56 declarations. The new unique-minimizer theorem adds one declaration; it is a proved definition obligation rather than a new numbered result attributed to Orabona. Existence comes from the Hilbert projection theorem. The two minimizer variational inequalities force the squared separation to be zero. `project_spec` binds the unchanged selected projection to the same uniquely satisfied predicate.

## Source and implementation routes

The independently accepted source inventory keeps external Rockafellar citations and the source's unproved projection existence-and-uniqueness assertion explicit. In the printed route, projection uses the minimizer-to-variational direction of Theorem 2.8 with a convex differentiable quadratic objective. The implementation uses Mathlib's Hilbert variational characterization; these routes are not conflated.

Projection and square expansion give one-step progress. Supporting-gradient convexity converts it to regret. A fixed positive rate uses ordinary telescoping, keeps exact initial/terminal distances and needs no diameter bound. Positive nonincreasing rates use a separate weighted telescope and finite distance control. Both retain the negative terminal residual. Known positive D, G and T permit the prescribed rate D/(G sqrt(T)); future gradients and unknown comparator distances are not presented as available online inputs.

## Visible differences and remaining scope

- Abstract real modules, normed spaces and complete real Hilbert spaces explicitly generalize the printed Euclidean setting.
- General epigraph convexity permits both infinities; Theorem 2.4 and ordinary indicator addition retain no-bottom where required. Theorem 2.7 retains ambient interior, local finite representation and every ambient comparator, including positive infinity.
- The repaired source interface uses convexity on the feasible set and differentiability of a supplied ambient extension on an open neighborhood. Extension existence or independence on thin domains is not proved. The older convex-open `RegularLoss` interface remains a labelled stronger library API; it is not accepted as an unrestricted source anchor.
- Fixed-rate zero-round behavior is a stated formal extension. Variable-rate and tuned endpoints retain their positive-horizon requirements. Tuned rates additionally require D>0 and G>0.
- Closure constructions, the separate finite-loss/domain-of-sum consequence, interior optimality, Jensen, FTL failure and later routes require separate integration. No optimality lower bound, executable projection, stochastic guarantee or whole-book completion is asserted.

## Validation and retained records

The byte-bound candidate passed the combined library, Tests, proof-graph-exporter compilation, strict placeholder scan, Python harness, verified site build and site check. Desktop/mobile page checks inspected the three proof bridges, MathJax output, folded Lean and horizontal overflow. [review-binding.json](review-binding.json) records candidate hashes, separate review roles and hashes of the retained maintenance evidence. Raw private audit records remain in maintenance.

An initial longer checkout hit a Windows output-path limit in unchanged RL code. The final gate used a shorter detached validation checkout with identical candidate bytes and preserved the original failed receipt. This is an environment repair, not a mathematical refutation or a skipped gate.

Exact-head CI, merge and deployment are separate events. This packet does not by itself certify that every file in an original PR has been superseded, nor authorize deleting an active branch. Purification and the full exposition seal remain separately tracked rather than inferred from merge or compilation.

## Immutable historical review receipts

- [online-ogd-migration-20261005 / blind-receipt](https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/blob/8045070bf1ee53c83778d04eb168f8ad6f728b59/runs/online-ogd-migration-20261005/blind-receipt-v2.json)
- [online-ogd-migration-20261005 / source-contract-receipt](https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/blob/8045070bf1ee53c83778d04eb168f8ad6f728b59/runs/online-ogd-migration-20261005/source-contract-receipt-v2.json)
- [online-ogd-migration-20261005 / public-body-receipt](https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/blob/8045070bf1ee53c83778d04eb168f8ad6f728b59/runs/online-ogd-migration-20261005/public-body-receipt-v2.json)
- [online-ogd-migration-20261005 / final-reader-receipt](https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/blob/8045070bf1ee53c83778d04eb168f8ad6f728b59/runs/online-ogd-migration-20261005/final-reader-receipt-v2.json)
- [online-convex-migration-20261005 / blind-receipt](https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/blob/8045070bf1ee53c83778d04eb168f8ad6f728b59/runs/online-convex-migration-20261005/blind-receipt-v1.json)
- [online-convex-migration-20261005 / source-contract-receipt](https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/blob/8045070bf1ee53c83778d04eb168f8ad6f728b59/runs/online-convex-migration-20261005/source-contract-receipt-v1.json)
- [online-convex-migration-20261005 / public-body-receipt](https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/blob/8045070bf1ee53c83778d04eb168f8ad6f728b59/runs/online-convex-migration-20261005/public-body-receipt-v1.json)
- [online-convex-migration-20261005 / final-reader-receipt](https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/blob/8045070bf1ee53c83778d04eb168f8ad6f728b59/runs/online-convex-migration-20261005/final-reader-receipt-v1.json)
- [online-first-order-migration-20261005 / blind-receipt](https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/blob/8045070bf1ee53c83778d04eb168f8ad6f728b59/runs/online-first-order-migration-20261005/blind-receipt-v1.json)
- [online-first-order-migration-20261005 / source-contract-receipt](https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/blob/8045070bf1ee53c83778d04eb168f8ad6f728b59/runs/online-first-order-migration-20261005/source-contract-receipt-v1.json)
- [online-first-order-migration-20261005 / public-body-receipt](https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/blob/8045070bf1ee53c83778d04eb168f8ad6f728b59/runs/online-first-order-migration-20261005/public-body-receipt-v1.json)
- [online-first-order-migration-20261005 / final-reader-receipt](https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/blob/8045070bf1ee53c83778d04eb168f8ad6f728b59/runs/online-first-order-migration-20261005/final-reader-receipt-v1.json)
