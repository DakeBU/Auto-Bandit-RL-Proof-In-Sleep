# Private explicit source clarifications after first topology review

The original source file and signature seals remain unchanged. This is a separate
clarification ledger, not a rewritten source or retrospectively pre-proof artifact.

1. The original phrase "real query horizon T" was ambiguous: the sealed budget
   consumer uses T : Nat, an actual integer number of oracle calls. This is a
   specialization of a real-valued budget bound, not a proof of every real-T
   variant. The user requested a count of calls. No random stopping guarantee.
2. The native root is Hellinger on nested finite traces. To connect it faithfully
   to the existing list law, need actual PMF masses equal ofReal density, hence
   toReal masses equal density, and an injective history map (with length n).
   Prove these bridges, rather than infer distance invariance from pushforward
   equality alone. The finite-trace root is not yet a literal infinite-List tsum
   Hellinger theorem; no such expression is used in the advertised statement.
3. The uniform weighted-cost bridge must use the existing historyQueryCost
   definition, not a parallel unconnected count. The append recurrence is an
   implementation ingredient. Both forward and inverse calls retain their
   original syntactic accounting.

These clarifications do not change any frozen root signature. New internal
provider proofs supply the missing bridges; they do not add root hypotheses.
