# FINITE-BINARY-KRAFT-CONVERSE

- Proposed names: exists_prefix_encoding_of_kraft_le_one and
  exists_binaryPrefixCode_of_kraft_le_one.
- Area/namespace: finite coding theory; InformationTheory candidate.
- Statement: finite prescribed lengths with binary Kraft sum <=1 admit
  prefix-free injective encoding with those lengths; the nonempty-codeword
  packaging additionally requires positive lengths.
- Imports/APIs: existing PrefixCodeConstruction imports; finite maximal image,
  sum_erase_add, finite prefix-avoiding word construction, image sums.
- Route: erase a maximal-length symbol; its positive Kraft weight makes the
  residual sum <1; recurse and insert an available maximal-length word.
- Regularity: finite alphabet, decidable equality; no strict Kraft budget.
- Source: TXT-LATTIMORE-SZEPESVARI-2020, Chapter 14 boxed assertion.
- Task: TEXTBOOK-PART-IV-CHAPTER-14-INFORMATION-THEORY-SPINE.
- Status: locally compiled, not upstreamed; aggregate validation pending.
- Consumer: exists_prefixCode_of_uniquelyDecodable derives positive lengths
  from Mathlib epsilon_not_mem and Kraft from kraft_mcmillan_inequality.
- Failure signal: adding strict Kraft <1 loses complete codebooks and is not
  sufficient for the boxed source assertion.
