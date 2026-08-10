# Contributing to the ABRL open formalization community

Thank you for helping connect mathematical research to checked Lean artifacts.
The public repository accepts teaching corrections, theorem-to-code mappings,
and structured lemma proposals. The upstream ABRL research tree is currently
private, so maintainers perform the final core-library integration and publish
the result in a later verified snapshot.

## Before substantial work

Open a **Lemma proposal** issue before starting a large formalization. State
the mathematical source, exact claim, intended domain, important assumptions,
and expected relationship to the existing catalog. This avoids duplicating a
route or proving a statement with the wrong interface.

## Contribution paths

1. For prose, links, or small corrections, open an issue or a focused pull
   request.
2. For a new result, use the Research IDE's **Export lemma packet** button or
   create `community/entries/<id>.json` from
   `community/contribution.schema.json`.
3. Use a lowercase kebab-case ID and matching filename.
4. Fill in source provenance and contributor credit. Remove
   `draft_missing_fields` before requesting final review.
5. Keep status honest. `lean-checked` requires compiler evidence;
   `integrated` is assigned only after the result enters the indexed ABRL tree
   and passes the full project gate.

## Review criteria

Reviewers check mathematical equivalence among the plain-English, LaTeX, and
Lean statements; visible assumptions; provenance; namespace and API fit;
dependencies; compiler evidence; explanatory value; and attribution. Lean code
that compiles only as `example : True` is a scaffold, not a formalization of
the submitted theorem.

## Credit and license

Packets retain contributor name, preferred credit, and source provenance.
By intentionally submitting a contribution with `license.agreed` set to
`true`, you license that contribution under the repository's MIT License and
confirm that you have the right to submit it. Do not include copyrighted prose
or code that you are not allowed to redistribute.

Participation also requires following the [Code of Conduct](CODE_OF_CONDUCT.md)
and [Governance](GOVERNANCE.md).
