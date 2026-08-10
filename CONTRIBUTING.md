# Contributing to BanditRLlib

Thank you for helping connect mathematical research to checked Lean artifacts.
This repository accepts teaching corrections, theorem-to-code mappings, and
structured lemma proposals for the BanditRLlib library.

## Before substantial work

Open a **Lemma proposal** issue before starting a large formalization. State the
mathematical source, exact claim, intended domain, important assumptions, and
expected relationship to the existing declaration catalogue.

## Contribution paths

1. For prose, links, or small corrections, open a focused issue or pull request.
2. For a new result, use the website's **Export lemma packet** button or create
   `website/community/entries/<id>.json` from
   `website/community/contribution.schema.json`.
3. Use a lowercase kebab-case ID and matching filename.
4. Fill source provenance, retrieval evidence, unresolved obligations, and
   contributor credit; remove `draft_missing_fields` before final review.
5. Keep status honest. Compilation is not semantic review or a completed proof.
   `integrated` is assigned only after the result is merged to `main` and passes
   the full ABRL project gate.

## Review criteria

Reviewers compare the plain-English, LaTeX, and Lean statements; assumptions;
provenance; namespace and API fit; dependencies; compiler evidence; explanatory
value; and attribution. `example : True` is only a scaffold, not a translation.

## Credit and license

Packets retain contributor identity and specific contribution scope. Community
credit does not automatically imply ABRL paper authorship. By submitting with
`license.agreed` set to `true`, you license your intentional contribution under
the repository's MIT License and confirm that you have the right to submit it.

Follow the [Code of Conduct](CODE_OF_CONDUCT.md) and
[Governance](GOVERNANCE.md).
