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

Retrieval packet: MLIB-KRAFT-MCMILLAN and TXT-LATTIMORE-SZEPESVARI-2020;
search-memory kraft and list-lean-decls exists_binaryPrefixCode_of_kraft
--statement confirm only the strict local converse. Installed Mathlib exposes
UniquelyDecodable.epsilon_not_mem and kraft_mcmillan_inequality for a finite
codeword set. Use Finset.sum_erase_add to prove the residual strict bound and
Finset.sum_image with encoder injectivity to transfer Kraft to symbol lengths.
No proof weapon, extra import, or external theorem assumption is needed.

Implementation: exists_prefix_encoding_of_kraft_le_one and its BinaryPrefixCode
packaging now compile, retaining strict versions as compatibility wrappers.
exists_prefixCode_of_uniquelyDecodable derives positive lengths from
epsilon_not_mem, transfers the finite codebook Kraft sum by injectivity and
constructs a prefix code with every original length. No nonempty-word or strict
Kraft premise was added to the source adapter. Focused build: 2673 jobs.
Root-import canary initially could not run in the long-path workspace because
BanditRLProof.olean is absent; this is a build-artifact failure, not a proof
failure. The original root import is retained for the short-path full gate.
Direct-module typed checks pass for both the equality-budget Bool example
and arbitrary finite uniquely decodable encoder. All three new declarations
report only propext, Classical.choice and Quot.sound.

Full 3d7c9a1 gate passed: Tests 8951 jobs, 400 Python tests, 7 skipped,
178.901s; C:/a14/tmp/ch14-kraft-equivalence-full-check.log. This includes the
original root-import canary, strict-wrapper consumers and the equality-budget
example. The long-workspace missing-root-artifact issue did not recur in the
short validation checkout. The boxed assertion's local proof gate is closed.
