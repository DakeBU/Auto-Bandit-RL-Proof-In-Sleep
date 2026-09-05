import BanditRLProof.LowerBounds.HuffmanAlphabet

namespace BanditRLProof.TextbookPartIVChapter14HuffmanAlphabetCanary

open LowerBounds

example {α : Type*} [Fintype α] [DecidableEq α] (a b : α) (hab : a ≠ b) :
    Fintype.card (Option (HuffmanRemainder a b)) < Fintype.card α :=
  huffman_merged_card_lt a b hab

#print axioms LowerBounds.expectedCodeLength_relabel
#print axioms LowerBounds.IsOptimalPrefixCode.relabel
#print axioms LowerBounds.huffman_merged_card_lt
#print axioms LowerBounds.exists_two_least_weights

end BanditRLProof.TextbookPartIVChapter14HuffmanAlphabetCanary
