# Chapter 14 optimal coding route

Source TXT-LATTIMORE-SZEPESVARI-2020, Eq. (14.1) and the Huffman optimality
claim on author p. 187. Actual prefix-code existence and the entropy sandwich
are compiled, but neither minimizer existence nor algorithm optimality follows
from that alone.

Begin with exact relabeling and exchange: an alphabet equivalence preserves
BinaryPrefixCode, and swapping a,b changes expected length by
(p(a)-p(b))*(length(b)-length(a)). This gives the greedy-exchange inequality
needed to move least-probability symbols to deepest leaves. Cards:
MLIB-FINSET-SUMS and MLIB-ORDER-ALGEBRA; APIs Equiv.swap, finite sum of
single-point indicators, and existing code fields. Code-specific wrappers
are project-local. Define optimality against every valid code explicitly;
conditional consequences do not count as existence or Huffman correctness.
Next required structure is the deepest-sibling/tree contraction argument,
with the singleton nonempty-codeword convention handled separately.

Focused result: PrefixCodeExchange builds (2,674 jobs) and its typed canary
passes. The exact swap cost, cost-nonincreasing exchange, length-order
necessary condition, and conditional entropy sandwich use only standard
propext/Classical.choice/Quot.sound. A separate theorem proves every valid
code has expected length at least one under a normalized nonnegative law;
the singleton one-bit code is a genuine global optimum under the repository's
nonempty-word convention. The Unit probability-one canary exercises that
base case. None of this asserts a general minimizer or Huffman algorithm
correctness. Root/aggregate verification for this module remains pending;
the ongoing full check at d256f27 covers the earlier block-coding additions.

Sibling expansion route: a code on Option alpha has one designated merged
symbol none. Keep each some(a) word unchanged and replace none by its word
followed by false/true, obtaining a code on alpha + Bool. Prefix comparison
of any extended codewords first identifies their parent via the old code's
prefix freedom; the two new children are separated by their final bit.
With child weights q,r, prove cost(expanded)=cost(merged with q+r)+q+r.
This is a concrete legal expansion and algebraic recurrence, not a proof
that the two least weights can always be made siblings in an optimum.

Sibling expansion now focused-builds (2,675 jobs) and passes the typed cost
recurrence and child-length canaries. The parent-prefix lemma uses only
propext, the prefix-free proof uses propext/Quot.sound, and the cost identity
uses standard propext/Classical.choice/Quot.sound. There are no own warnings.
The merged leaf is nonempty under the existing code structure; the special
two-symbol root case still needs its separate treatment when assembling
Huffman induction. No root/aggregate integration is claimed for this module.

Contraction route: given two actual sibling words w++[false], w++[true]
in a code on alpha+Bool, replace them by w as the none leaf of Option alpha.
Require w nonempty to respect the local code contract. If w prefixes another
word, inspect the suffix's first bit: either that word equals w and prefixes
a child, or one child prefixes that word. Both contradict original prefix
freedom. The reverse prefix direction follows by extension to either child.
Then prove the reverse exact cost recurrence. Empty-root/two-symbol handling
remains separate; no hidden nonempty assumption is introduced in that case.

Contraction and the two-symbol root optimum now focused-build (2,675 jobs)
and pass typed canaries, including a zero-probability child at the root.
Prefix proofs use propext only; cost/root-optimum proofs use the standard
propext/Classical.choice/Quot.sound set. No own warnings remain. The explicit
one-bit root code supplies the exceptional two-symbol base without an empty
codeword. Exchange and sibling modules/canaries are now registered with the
root/Tests target for the next full gate; the general least-weight-sibling
normalization and Huffman induction remain open.

Deepest-leaf normalization route: write a maximum-length word as parent++[b].
If the other child parent++[!b] is absent, no other codeword can extend the
parent: maximality bounds the remaining suffix to length at most one, and
the only two children are either the original leaf or its absent sibling.
Nor can any other word prefix the parent, since it would prefix the original
leaf. Thus replacing the deepest word by its nonempty parent preserves
prefix freedom and reduces expected length by its nonnegative weight.
Root/singleton exceptions stay explicit. This is preparation for normalizing
an arbitrary competitor, not an assumption that an optimum already exists.

The deepest-parent incomparability, legal word replacement/pruning, exact
cost decrement p(a), and nonincreasing-cost result now focused-build
(2,676 jobs). Zero weights are explicitly permitted; no strict probability
premise is used. Parent nonemptiness and longest-word/absent-sibling
conditions remain explicit. The next termination measure is total natural
codeword length, so zero-cost pruning still makes structural progress.
The current full gate at 7b8e73f does not include this new pruning module.

Normalization termination route: among codes with expected cost at most a
given competitor, choose one minimizing the natural sum of codeword lengths
(Nat.find, with the original code as witness). A deepest absent-sibling
pruning would decrease that sum by one while retaining the cost bound, a
contradiction. For a nontrivial alphabet an absent sibling cannot occur at
an empty parent: [] prefixes every other codeword, contradicting the already
proved incomparability lemma. Thus a normalized no-worse competitor has
deepest siblings, without assuming existence of a globally optimal code.

Normalization now focused-builds (2,676 jobs) and passes its full typed
canary. `exists_no_worse_deepest_sibling_pair` exposes distinct labels, the
common parent and opposite final bits, maximal depth, and cost domination
of the supplied competitor. The natural-length minimality argument handles
zero weights. All new axiom reports use only standard propext/Classical.choice/
Quot.sound. The condition Nontrivial alpha is explicit; the singleton base
was proved separately. No Huffman algorithm or global cost-minimizer is yet
claimed, and pruning remains outside the ongoing 7b8e73f full gate.

Least-weight exchange route: first normalize a competitor to deepest siblings
x,y. Swap the least-weight label a into x. The other sibling's new label is
swap(a,x)(y), which cannot equal a. Swap the second-least label b into that
position; the second swap fixes a. Both exchanges are cost-nonincreasing
because their target words have maximum length and the target labels obey
the relevant weight inequalities. Return exact sibling words for a,b without
assuming any optimum. Equiv.swap involution handles coincident original and
desired labels; ties and zero weights stay allowed.

Full-gate result for 7b8e73f: the short-path checkout passed the complete
`tools/bandit.py check`, including 400 Python tests (7 skipped, 196.237s).
Log: `C:/a14/tmp/ch14-sibling-full-check.log`. This covers Exchange/Siblings
integration, not the later Pruning/Greedy leaves.

Greedy-choice result: `PrefixCodeGreedy.lean` compiled (2677 jobs).
`exists_no_worse_least_weight_siblings` returns a real prefix code placing
the specified two least-weight labels at deepest sibling leaves, with cost
no greater than any supplied competitor. Weak weight inequalities admit
ties and zero weights; normalization is not required. Two involutive label
swaps preserve prefix-freeness and the second fixes the first chosen label.
This proves the greedy-choice transformation, not recursive Huffman
optimality or the arithmetic-coding algorithm. The chapter remains partial.

The typed Greedy canary passed; both axiom reports contain only propext,
Classical.choice, and Quot.sound. Retrieval, task memory and blueprint were
refreshed. This leaf is focused-validated only, not yet root-integrated.

Recursive optimality-step route: specialize the greedy choice to an alphabet
alpha + Bool, with false and true the two least weights. If the returned
final bits are reversed, exchange those two equal-length leaves at zero cost.
For nonempty alpha the parent cannot be empty (it would prefix an inl leaf).
Contract the competitor, invoke optimality of the merged Option alpha code,
and use both exact cost recurrences to prove optimality of its expansion.
The nonempty-alpha condition represents the recursive case of at least three
symbols; singleton and two-symbol roots are separate base cases, not omitted
exceptions. Local APIs: PrefixCodeGreedy, contractSibling, expandSibling,
expectedCodeLength_swap, sibling_parent_not_prefix_other.

Induction-step result: `HuffmanStep.lean` builds (2678 jobs), and its typed
canary passes with only propext/Classical.choice/Quot.sound. The initial
compiler failure was missing automatic Nontrivial (alpha + Bool) synthesis;
an explicit false/true witness repairs the instance without strengthening
the target. The theorem `IsOptimalPrefixCode.expand_least_weights` proves
global optimality of expansion from global optimality of the smaller merged
code. It does not assume optimality of the desired expanded code. No mass
normalization is needed. A complete recursive construction and its terminal
existence/optimality theorem are still required. Pruning, Greedy, HuffmanStep
and their canaries are now added to the aggregate imports for the next gate.

Alphabet-reduction route: transport expected lengths and global optimality
along an arbitrary finite alphabet equivalence using Equiv.sum_comp. Split
two distinct selected symbols from their complement subtype, with an explicit
equivalence from complement + Bool to the original alphabet. This supplies
the relabeling interface needed by cardinality recursion; it does not replace
the recursive Huffman construction with mere minimizer existence.

Alphabet-reduction result: HuffmanAlphabet builds (2679 jobs) and its typed
canary passes. Exact expected-cost transport and global-optimality transport
hold for any finite alphabet equivalence. The explicit split equivalence
and `huffman_merged_card_lt` establish recursive size decrease; finite minima
on univ and univ.erase give `exists_two_least_weights`, allowing ties. A
simplifier equality branch initially retained b=a; explicit hab.symm closes
it without new assumptions. All four audited theorem reports use only the
standard propext/Classical.choice/Quot.sound axioms. This module is not yet
aggregate-imported and is outside the running 7daa2b9 full gate.

Recursive-construction route: define a noncomputable Huffman constructor on
arbitrary finite alphabets and nonnegative real weights. Return a code paired
with its proved optimality, not a chosen unspecified minimizer. The body
chooses two least labels, uses the explicit split equivalence, recursively
constructs the merged Option-remainder code, and expands/relabels it. The
termination measure is alphabet cardinality. Zero/one symbols use the
one-bit singleton code; exactly two use the one-bit binary root. General
one-bit optimality follows directly from positive codeword lengths, without
normalization. Noncomputability is from ordering/choosing real weights, not
an oracle for optimal codes. APIs are the existing greedy/step/alphabet leaves.

Construction result: `HuffmanConstruction.lean` builds (2680 jobs). The
constructor recursively calls itself on the merged alphabet, terminates by
`huffman_merged_card_lt`, and returns expansion/relabeling of that smaller
code. Its optimality proof follows the established greedy step. The initial
errors were length-nonzero arithmetic exposure and classical decidability
in the termination tactic; both were repaired without changing the target.
`huffmanCode_optimal` compares against every prefix code, and
`huffmanCode_entropy_sandwich` proves Eq. (14.2) for normalized masses.
The constructor handles empty/singleton and exactly-two cases separately,
preserving the local nonempty-codeword convention. Aggregate imports now
include Alphabet/Construction and their canaries; their full gate is pending.

The Construction typed canary passed. The recursive constructor, global
optimality theorem and entropy-sandwich theorem all report only propext,
Classical.choice and Quot.sound. Retrieval/task-memory/blueprint refreshed.
