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
