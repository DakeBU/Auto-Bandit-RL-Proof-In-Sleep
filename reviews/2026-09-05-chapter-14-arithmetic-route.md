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

Word-separation route: use the cumulative-offset inequality and tail bounds
to separate words with distinct leading symbols. For identical heads, the
nonnegative affine map preserves the inductive tail separation. Induction
on equal word lengths gives either endpoint ordering for any unequal words;
an interior point common to both then contradicts either ordering. Zero-width
cells are allowed and have empty interior; no strict positivity is needed.

Grid selection route (Mathlib-candidate scalar leaf): choose m=ceil(L/delta)
using Nat.le_ceil and Nat.ceil_lt_add_one for L>=0, delta>0. Multiplication
by delta gives L<=m*delta and (m+1)*delta<L+2*delta<=U. With
delta=2^(-n), this will supply a dyadic subinterval. Local retrieval for ceil
found no matching interval-selection terminal; installed floor/semiring APIs
provide the two exact rounding inequalities. No new dependency is required.

Separation/grid result: focused build and canary pass. Distinct equal-length
word intervals have ordered endpoints, so an interior point identifies the
word uniquely. `exists_grid_cell_inside` proves the explicit ceil-based cell
selection for any positive grid spacing with twice-spacing width budget.
All new audits use only propext/Classical.choice/Quot.sound. The binary-address
representation, prefix-freeness and rate theorem remain open; these interval
lemmas alone are not a completed arithmetic encoder. Aggregate gate remains
the independent dff13cb Huffman check; arithmetic leaves are focused-only.
