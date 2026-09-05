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

## Shannon numerical length leaf

No Kraft converse or prefix-code constructor was found in the installed
Mathlib coding modules. Before building that combinatorial constructor,
prove the numerical ceiling bound: lengths ceil(log(1/p)/log 2) (clamped
below by one to match the local nonempty-word contract) have expected length
at most H2+1. Treat p=0 separately so zero-probability symbols remain allowed.
This is only a proposed length assignment, not a BinaryPrefixCode or proof
of existence/optimality. APIs: Nat.ceil_lt_add_one, Nat.le_ceil, log_nonneg,
finite weighted sums. The zero-probability codeword allocation and the
Kraft converse still require explicit construction, not assumed lengths.

Construction audit: ordinary ceilings can saturate Kraft capacity on dyadic
positive masses, preventing direct insertion of zero-mass symbols. Use the
strict Shannon length floor(log(1/p)/log 2)+1 instead. It retains the same
H2+1 bound and leaves strictly positive Kraft slack on the positive support.
Zero-mass symbols will need a separate sufficiently long assignment; their
default numerical length here is not claimed realizable. This is a recorded
mathematical reason for changing the numerical adapter, not a target change.

The strict Shannon numerical module focused-builds (2,672 jobs), and its typed
canary passes, including the p=1 length and the expected-length bound allowing
zero masses. The three audited proof leaves use only propext, Classical.choice,
and Quot.sound. `shannonLength_kraft_weight_lt` proves strict slack pointwise
on positive masses. This module is not yet root-integrated and does not supply
codewords, zero-mass allocation, or the missing optimality/source-coding claims.
