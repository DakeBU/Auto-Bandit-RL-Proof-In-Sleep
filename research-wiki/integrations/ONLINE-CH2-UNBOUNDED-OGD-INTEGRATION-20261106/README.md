# Decreasing-step OGD on an unbounded domain

On the full Euclidean space, polynomially decreasing step sizes can force superlinear regret. For each admissible exponent and sufficiently large horizon, choose a unit direction and use its negative as the loss gradient for the first half of the rounds, rounding up. Reverse the gradient for the remaining rounds. Gradient descent and subgradient descent start at zero and follow identical iterates on these losses. Orabona's Theorem 5.4 supplies the subgradient regret lower bound, which therefore also holds for this gradient run against zero.

The scalar two-round test computes regret one below the theorem’s horizon threshold. A separate 64-round example in two dimensions applies the theorem and proves three numerical bounds for the same loss sequence.

[Chapter 2 remark](https://arxiv.org/pdf/1912.13213v10#page=26) · [Theorem 5.4 and proof](https://arxiv.org/pdf/1912.13213v10#page=64) · [Statement and checked proof](statement-and-proof.json)

## Chapter coverage

The new OGD theorem and two previously established OSD statements resolve one required forward container. Seven remain open. The historical freeze has 172 overlapping target rows. Its 31 later statement branches belong to ten historical owners. Whole-chapter proof coverage remains partial.

[Three source rows and open obligations](source-target-reconciliation.json) · [Original PR220 paths](original-path-continuations.json) · [Historical records](historical-delivery.json)
