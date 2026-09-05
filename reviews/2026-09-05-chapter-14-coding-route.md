# Chapter 14 coding lower-bound route

Source TXT-LATTIMORE-SZEPESVARI-2020, Eq. (14.2), author p. 187.
The next required leaf is the entropy lower bound for every valid prefix code,
not an assumption of optimality. Reuse BinaryPrefixCode.kraft_inequality and
its injective codebook to obtain sum_i 2^(-length_i)<=1. For each positive p_i,
apply log(t)<=t-1 with t=2^(-length_i)/p_i, multiply by p_i, and sum.
Handle p_i=0 separately. Normalization cancels the Kraft remainder and division
by positive log(2) gives H2<=expected length. No positive-mass-only alphabet
restriction is permitted. This does not establish code existence, Huffman
optimality, the upper half of Eq. (14.2), or block/arithmetic source coding.

APIs: Real.log_le_sub_one_of_pos, log_div, log_pow, Finset.sum_image;
cards MLIB-REAL-LOG-SQRT, MLIB-FINSET-SUMS, MLIB-KRAFT-MCMILLAN.
Generic scalar bound is a Mathlib-candidate; prefix-code consumer project-local.

Both declarations now pass direct Lean checking. The proof uses exactly the
recorded route, including the p=0 branch and the injective codebook sum.
No optimality assumption is introduced. Focused/aggregate integration evidence
is separate from this direct compiler result.

Focused build passed (2,671 jobs) and the typed canary passed, including the
zero-mass scalar branch. Both axiom sets contain only propext, Classical.choice,
and Quot.sound. The module and root-import canary are registered for the next
full gate. Neither Shannon/Huffman upper bound nor optimality is claimed.
