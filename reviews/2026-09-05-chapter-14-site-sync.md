# Chapter 14 local site evidence synchronization

The textbook spine, result ledger and Kraft teaching note now distinguish
the compiled coding terminals from the earlier definition-only milestone.
The existing Python static-site generator and hosting configuration are
preserved; no Sites project was created and no public deployment was made.

## Content boundary

- Added source-mapped terminal links for recursive Huffman optimality, its
  entropy sandwich, the named arithmetic block-code rate and universal converse.
- Added the common-density KL formula, source Jensen/affinity and overlap
  steps, positive-variance Gaussian KL/testing, and supporting body adapters.
- Preserved the nonempty singleton convention, power-of-two-only uniform
  fixed-length optimality with a ternary counterexample, classical exact-real
  arithmetic construction, unrounded cross entropy, and finite-alphabet-only
  finite-KL/absolute-continuity equivalence.
- Kept whole-chapter status `partial`, Chapter 15 history decomposition
  out of Chapter 14, and focused compilation distinct from the final gate.

## Validation

`python website/scripts/build_site.py --output tmp/ch14-site` succeeded:
633 modules, 8432 declarations, zero placeholders. This first local preview
deliberately omits `--lean-verified` while the final source-inclusive gate
is running. The generator records dirty source; it is not publication evidence.

The corresponding `check_site.py --output tmp/ch14-site --allow-unverified`
reported five SGB compiled-label failures: the checker still requires these
unrelated compiled labels even in allow-unverified mode. No Chapter 14 content
error was reported, but this first check did not pass.

The a47106a gate subsequently completed its Lean aggregate successfully
(8951 jobs). A current diff against that snapshot is empty for BanditRLProof,
Tests, both root imports, lakefile.toml and lean-toolchain. Rebuilding with
`--lean-verified` and rerunning the normal checker both succeeded:
687 HTML pages, 633 modules, 8432 declarations, 9231 Lean source links;
internal links/anchors, mathematical fallbacks and Pages workflow checks pass.
This validates the content committed in 93f1610, although the preview build
started before that commit and still records its predecessor with dirty source.
The full-harness tests subsequently passed at a47106a (400 tests, 7 skipped,
226.925s). Browser verification and remote publication are not claimed.
Do not promote the chapter based only on this synchronization.
