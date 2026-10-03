# Site registry repair

site-build01 rejected an external Mathlib name in the local-only highlight dependency list. Remove InnerProductSpace.toDual_symm_apply from that display list; its actual proof dependency remains recorded by the compiled graph, and the reader retains the Riesz argument. No theorem, canary, frozen header or reviewed reader bytes changed. Rerun site gate; preserve original failure.

site-build02 then rejected the teaching-route helper because it lacked a highlight entry. Add an explicit helper highlight with the precise contact equality and normed-space assumptions. Reader bytes and Lean remain unchanged.
