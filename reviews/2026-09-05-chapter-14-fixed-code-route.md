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
