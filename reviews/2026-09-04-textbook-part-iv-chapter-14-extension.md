# Chapter 14 whole-body extension review

Task: `TEXTBOOK-PART-IV-CHAPTER-14-INFORMATION-THEORY-SPINE`

Review date: 2026-09-04

## Scope reviewed

- Official author PDF, displayed Chapter 14 pp. 186--197 / physical PDF
  pp. 195--206, with required body window §14.1--§14.2 through physical PDF
  p. 200.
- `BanditRLProof/LowerBounds/InformationTheory.lean` and the root-import
  Chapter 14 canary.
- Frozen task/window/obligation boundaries, research cards, synchronized proof
  export, results/highlights, and textbook-spine page data.

## Statement and proof audit

- `BinaryPrefixCode` retains injectivity and prefix freedom and adds the
  necessary nonempty-codeword contract. The latter prevents the singleton
  empty-codeword counterexample to unique decoding of repeated messages.
- `uniquelyDecodable_range` proves equality of message lists from equality of
  their flattened encodings; it does not assume the result later consumed by
  `kraft_inequality`.
- Entropy definitions use the exact finite sums in bits/nats. Their local
  theorems cover unit conversion and nonnegativity, not an optimal-code
  existence or Huffman theorem.
- `relativeEntropy_trim_le` quantifies over arbitrary `m ≤ m₀` and finite
  measures. It splits infinite KL, derives AC/integrability only in the finite
  branch, uses `toReal_rnDeriv_trim`, applies conditional Jensen to the convex
  KL integrand, and transports integrals through `Measure.trim`.
- KL direction remains `D(P,Q)`. No mutual-AC or probability-normalization
  premise was added to the full data-processing theorem.
- The existing event DPI and Bretagnolle--Huber terminal are unchanged in
  semantics. The complement remains under `Q`, and infinite KL retains scale
  zero.

## Evidence-status audit

The new declarations are eligible for `compiled` only after the focused and
root-import gates below pass. Chapter status must remain `partial`. The exact
required body blockers are:

1. Eq. (14.2) Huffman optimum and the `H₂(P) ≤ L* ≤ H₂(P)+1` theorem;
2. block/arithmetic source-coding achievability and converse;
3. Eq. (14.4) for an arbitrary finite alphabet beyond the compiled Bernoulli
   specialization;
4. Eq. (14.5) finite-discretisation supremum and its equality with RN KL;
5. the general common-density formula and measure-level overlap/affinity proof
   nodes;
6. the arbitrary positive-variance Gaussian formula and displayed testing
   application, including `3/10` and `3/20` consequences.

The adaptive same-policy history-KL decomposition remains Chapter 15 evidence
and is not counted as Chapter 14 completion.

## P0--P3 findings

- P0: none.
- P1: none.
- P2: none.
- P3: none.

No evidence-supported issue was found in the new statement signatures or proof
routes. The remaining items above are coverage blockers, not defects in the
compiled slice.

## Verification record

- Focused module build: pending final gate record.
- Root import and typed canary: pending final gate record.
- Full repository harness and site checks: pending final gate record.
- Browser inspection: pending final gate record.
