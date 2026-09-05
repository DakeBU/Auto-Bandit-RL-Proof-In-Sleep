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

Binary-address route: define the natural value of a big-endian Bool list,
prove value < 2^length, and construct each index m<2^n by splitting at
2^(n-1). The append value formula expresses a prefix's dyadic cell containing
its descendants. Define real cell endpoints as value/2^length and
(value+1)/2^length. This directly represents the grid cells already selected,
not an unrelated existential prefix-code construction.

Binary-address result: DyadicAddresses builds (2676 jobs), with a typed
canary and standard-only axiom audits. `exists_binaryAddress` represents
every bounded grid index at exactly n bits; append arithmetic proves
`dyadicAddress_prefix_contained`. `exists_dyadicAddress_inside` combines
the earlier ceil grid selection with this representation to return an actual
Bool list whose cell is inside [L,U], under the explicit twice-grid-width
budget. Real endpoint definitions are noncomputable; natural address values
are computable. No arithmetic prefix-code/rate terminal is claimed yet.
This focused-only module remains outside the running dff13cb full gate.

Prefix-code assembly route: for an injectively labeled family of equal-length
messages with assigned bit lengths satisfying the dyadic width budget, choose
the actual binary address in each arithmetic cell. If one address prefixes
another, the midpoint of the latter cell lies strictly inside both source
cells, so interval uniqueness forces equal messages and equal labels. The
strict upper endpoint bound excludes the empty binary word (whose upper
endpoint is 1). This produces a BinaryPrefixCode with exact assigned lengths.
The width-budget hypothesis is an intermediate interface, not a new premise
for the final source theorem; later length allocation/support handling must
discharge it for arbitrary distributions including zero masses.

Length-allocation route: `arithmeticLength mass = shannonLength mass + 1`.
The extra bit changes the twice-grid-width budget into the existing strict
Shannon Kraft-weight inequality. For 0<mass<=1 the pointwise code length is
at most log2(1/mass)+2. This positive-cell leaf will be applied on the support;
the final distribution theorem must explicitly cover zero-mass messages.

Assembly/length result: ArithmeticPrefixCode compiled (2677 jobs), its typed
canary passed, and all four audited declarations use only standard axioms.
The chosen cell addresses form an actual BinaryPrefixCode with exact assigned
lengths under the width interface. `arithmeticLength_width_budget` discharges
that interface for positive mass; `arithmeticLength_le_information_add_two`
gives the constant-two pointwise overhead. The nonempty-codeword condition
is proved, not assumed. Still required: support/zero-mass extension and
product-source expected-length/rate terminal. These leaves are focused-only.

Zero-mass extension route: encode positive-mass symbols as false followed by
their arithmetic support code, and other symbols as true followed by an
arbitrary total fallback prefix code. Distinct first bits separate branches;
within each branch prefix freedom comes from the respective code. For a
nonnegative normalized law all outside-support terms have weight zero. A
positive-symbol information+2 bound therefore becomes a full-alphabet
expected-length bound H2+3. This explicit one-bit support/escape tag is a
constant-overhead arithmetic variant, whose overhead vanishes per block.
Fallback can be supplied by the already proved total Huffman constructor;
it is never used on a positive-probability message. Local API: cons_prefix_cons.

Zero-safe result: ArithmeticZeroExtension builds (2685 jobs), with passing
typed canary and standard-only axiom reports. `exists_zeroSafe_arithmeticCode`
constructs the positive support code from the actual arithmetic intervals,
uses exact arithmetic lengths, and extends it to all messages using the tag.
It proves expected length <= H2(q)+3 for a normalized equal-length message
family whose probabilities are the products of source probabilities. No
full-support assumption on p or q is imposed. A total Huffman fallback is
used only on zero-mass messages. This is not a claim about an executable or
finite-precision arithmetic implementation. SourceBlock/list conversion and
the asymptotic rate terminal still need connecting; aggregate check pending.

Block-rate route: recursively convert SourceBlock to a List, proving exact
length, injectivity, and probability-product agreement. Instantiate the
zero-safe arithmetic constructor for SourceBlock (Fin k) n. Name the resulting
tagged arithmetic code family, retain its explicit construction, and derive
n*H2 <= expected length <= n*H2+3. For n+1 symbols squeeze the normalized
rate between H2 and H2+3/(n+1). Reuse the universal prefix-code converse,
not the previous arbitrary-code achievability theorem.

Block-rate result: ArithmeticBlockCoding builds (2686 jobs). The named
`arithmeticBlockCode` is the previously constructed interval-address/support-
tag code, not a choice from the generic entropy-sandwich existence theorem.
`arithmeticBlockCode_rate_tendsto_entropy` proves its expected rate converges
to H2 for every normalized nonnegative distribution on Fin k, zeros included.
The finite-n bound has total overhead 3, and the universal prefix-code
converse supplies the matching lower limit. Initial failures were the
empty-block instance and an unconstrained PUnit universe; exposing PUnit and
pinning this finite alphabet block to universe zero fixed elaboration without
changing the mathematical scope. All arithmetic modules and canaries are
now aggregate-imported; a full gate and source/export audit remain required.

Typed block-rate canary passed. SourceBlock/list injectivity has no axioms;
the finite length/rate and convergence audits use only propext,
Classical.choice and Quot.sound. Retrieval/task-memory/blueprint refreshed.
