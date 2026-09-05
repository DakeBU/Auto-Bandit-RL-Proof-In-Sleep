# Boxed unique-decoding assertion audit

Author p.186 states that all uniquely decodable codes have equivalent prefix
codes. Its reference to Note 1 does not remove this assertion from the required
body window. For the finite alphabet in this section, retain every symbol's
codeword length, hence every expected-length cost.

Current local evidence is incomplete: InformationTheory proves prefix implies
unique decodability and Kraft, but PrefixCodeConstruction exposes only the
strict Kraft converse (<1). A uniquely decodable code can have Kraft sum =1.
No complete equal-length unique-decoding-to-prefix adapter was found in these
coding modules and canaries. This is a genuine additional proof gap.

Next route: generalize the greedy finite Kraft construction to <=1. Removing
the maximal-length symbol removes a positive Kraft weight, making the residual
sum <1, so the existing avoiding-prefix construction applies unchanged.
Preserve the old strict theorem as a wrapper. Then use Mathlib Kraft--McMillan
on an injective finite encoder with uniquely decodable range and package the
equal-length prefix code. Before tactics, retrieve the exact Mathlib signatures
and nonempty-word consequence. The general converse is a Mathlib-candidate;
the source-facing finite encoder adapter is project-local.

The separate body sentence about shorter words for more probable symbols is
already covered by IsOptimalPrefixCode.length_antitone in PrefixCodeExchange
and its typed Exchange canary. It is now explicit in the evidence matrix.

Whole-chapter promotion remains unproved after the arithmetic-identity gate:
the boxed assertion also needs its compiled local adapter and canary.
