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
