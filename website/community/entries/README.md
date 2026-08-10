# Community lemma packets

Each accepted file in this directory is one machine-readable lemma proposal.
Use a lowercase kebab-case filename matching the packet's `id`, for example
`probability-conditional-hoeffding.json`.

Start with the Live Formalization export or the schema at
`../contribution.schema.json`. Before opening a pull request:

- provide a real mathematical source or mark the result as original;
- make the plain-English, LaTeX, and Lean statements describe the same claim;
- list imports and important dependencies;
- keep the status honest: a local draft is `proposed`, not `integrated`;
- fill in contributor credit and accept the repository's MIT contribution
  terms;
- remove `draft_missing_fields` once every listed item has been supplied.

The public workflow validates packets and builds `../registry.json`. A packet
can be Lean-checked without being integrated into BanditRLlib on `main`; the
website keeps those states separate.
