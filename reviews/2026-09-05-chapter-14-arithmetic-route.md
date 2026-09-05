# Chapter 14 arithmetic coding route

Source: local author PDF, author p.187 (physical p.196), text extraction
`tmp/pdfs/chapter14-pages195-206.txt`, lines 91-97. The named arithmetic
scheme approaches entropy per symbol; the existing arbitrary block-code
family does not establish this named construction.

Route: use a finite ordered alphabet, cumulative probability offsets, and
recursive affine subdivision of [0,1]. Prove interval width equals the
word probability, containment in [0,1], and disjoint interiors for distinct
same-length words. Then select a dyadic subinterval inside each positive
width interval and encode its binary address. The dyadic selection needs a
constant overhead bound; after block normalization this overhead vanishes.
Zero-probability words require an explicit convention/support treatment,
not a hidden positivity assumption on the original distribution.

First leaf uses Finset.filter cumulative sums, `Finset.sum_insert`,
`Finset.sum_le_sum_of_subset_of_nonneg`, and affine interval recursion.
It does not yet select output bits or prove the named scheme's rate.

First result: ArithmeticIntervals compiled (2675 jobs). The actual recursive
interval has width equal to the product word mass, stays ordered inside
[0,1] for normalized nonnegative masses, and symbol partition cells are
ordered/disjoint in their interiors. Zero masses are allowed in these leaves.
One initial error was the orientation of `add_le_add_left`, repaired with
componentwise `add_le_add`. No target weakening was needed. Word-interval
separation, dyadic output construction and rate bounds remain to be proved.

Typed canary passed and all three axiom audits contain only propext,
Classical.choice and Quot.sound. This first arithmetic leaf is focused-only,
not yet aggregate-imported; it is not covered by the running Huffman gate.
