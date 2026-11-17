# Chapter 1 source acceptance freeze (draft)

Status: `SOURCE_FREEZE_PENDING_INDEPENDENT_REVIEW`.

This packet proposes the original 17 mandatory source objects from Orabona, *Online Learning: A Modern Introduction Using Convex Optimization*, arXiv:1912.13213v10. It covers printed pages 1–7 / PDF pages 13–19 and all 60 source-region dispositions. History and independent Exercises 1.1–1.2 have separate scope. Formal main-text results remain mandatory when proofs are omitted or assigned to the reader.

Start with [source-freeze.json](source-freeze.json): exact requirements and necessary dependencies, including causal logarithmic lower bound and arbitrary-initialization performance. Unknown internal helper count does not block freezing these targets. The count is not a completion percentage.

- [paragraph-coverage.json](paragraph-coverage.json): full-page dispositions and source topology.
- [statement-bindings.json](statement-bindings.json): 53 repository header fingerprints and separate external Mathlib dependency. Headers are not compiler evidence.
- [no-regret-source-adjudication.json](no-regret-source-adjudication.json): ordinary-limit criterion, upper-epsilon condition, best-in-hindsight limit and dyadic nonimplication. No repair is needed to represent the literal definition.
- [provenance.json](provenance.json): historical states, bibliographic correction addendum and separate successor evidence.
- [publication-plan.json](publication-plan.json): independent review and publication gates.

Base commit: `ee8c0b805c785220ee31799012325f4179dad875`. PDF SHA256: `cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17`.

The contract author has not approved this durable freeze. Current proof-body, runtime, canary, combined-project, site and rendered-reader acceptance remain pending until exact evidence is attached and reviewed. No chapter/book completion, source correction approval, commit, merge or live-publication claim follows. Existing historical status fields are preserved.
