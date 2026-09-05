# Fixed-length coding source adapter

Source p.187 states that ceil(log2 N) bits suffice. Use Nat.clog 2 N, the
integer ceiling logarithm, with its exact capacity property N<=2^clog.
Enumerate an arbitrary finite alphabet via Fintype.equivFin and choose the
already proved fixed-width binary representation of each index. Equal-length
prefixes are equal words, and numeric values recover the original labels.
Require a positive bit length for the local nonempty-word convention. The
N>=2 terminal yields ceil-log length; singleton remains an explicit one-bit
exception. Do not claim uniform fixed-length optimality for non-power-of-two N.
Local APIs: exists_binaryAddress, List.IsPrefix.eq_of_length, Nat.le_pow_clog.

Focused result: FixedLengthCoding builds (2677 jobs), including exact expected
length n for every normalized mass function. Arbitrary finite alphabets are
handled by equivalence with Fin(card), with no probability positivity premise.
The ceiling-log terminal explicitly requires card>=2, preserving the local
singleton nonempty-word convention. Uniform-distribution optimality is not
claimed for arbitrary cardinality. Aggregate verification remains pending.

Typed canary passed, including a concrete five-symbol three-bit code and
the arbitrary-alphabet ceiling-log result. Axiom reports are standard-only.
FixedLengthCoding, CrossEntropy and RelativeEntropyNonMetric plus their
canaries are now aggregate-imported for the next full gate.

Uniform-law qualification route: for card=2^n, uniform entropy is exactly n
and an n-bit code attains the entropy lower bound, hence is globally optimal.
For three symbols, explicitly construct words 0,10,11 with mean 5/3 under
the uniform law, so no constant-two-bit code is optimal. This formalizes the
boundary of the source's informal uniform-length statement, rather than
trying to prove the false arbitrary-cardinality interpretation.

Uniform result: UniformCoding builds (2679 jobs), with a passing typed canary
and standard-only axiom audits. `fixedLength_uniformPowerTwo_optimal` proves
the precise power-of-two case; `uniform_three_fixedLength_not_optimal` proves
the exact counterexample via the concrete 0,10,11 code. The only initial
compiler issue was a redundant field_simp after simp had already closed the
entropy identity. These focused-only leaves are outside the d325147 gate.
