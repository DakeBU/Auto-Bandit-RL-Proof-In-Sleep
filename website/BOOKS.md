# Books and the shared Lean registry

Canonical website source is `research/website` in the ABRL hub. The hub's
`website` path is a junction. Edit content, generator and static assets, never
`_site`. The anonymous snapshot and manuscripts have independent release rules.

## Reading views

`content/books.json` registers book identity, bibliography, reading-map status
and ordered chapter references. `chapters.json`, `readings.json` and
`textbook_spine.json` remain the owners of existing chapter content and source
contracts. `banditrlwiki.json` owns setting families, comparison cases, new topic
placeholders and their twelve-field result contract. There is no second theorem
ledger in a book or topic record.

| Prior entry | Current navigation | Preserved route |
| --- | --- | --- |
| Learn / Book Map | Books / Bandit Book / Teaching routes | `learning/index.html`, `chapters/<slug>/index.html` |
| Textbook Spine / Part IV | Books / Bandit Book / Source chapters 13–17 | `textbook-spine/index.html`, `textbook-spine/<slug>/index.html` |
| Finite-horizon RL | Shared by Bandit Book and RL Book | `chapters/finite-horizon-rl/index.html` |
| EXP3 and Tsallis-FTRL | Shared by Bandit Book and Online Learning Book | Original chapter and declaration URLs |
| Setting atlas | BanditRLwiki / Settings and methods | Existing family, case, paper and frontier URLs |

The homepage retains `#primary-textbook`, `#textbook-spine`, `#book-map` and
`#reading-order`, including native disclosure expansion on fragment navigation.
No old route is replaced by an inaccessible client-only redirect. The new entry
pages are `books/index.html` and `books/<book-id>/index.html`. Planned topics use
`banditrlwiki/topics/<topic-id>/index.html`. Small themes such as multi-objective
optimization remain Extended Chapters; conformal prediction has its own planned
book, without an invented source or coverage count.

## Canonical node protocol, version 1

`scripts/book_registry.py` resolves the content references against the existing
source index on every build. `books/registry.json` is a generated reference
registry, not a hand-maintained inventory. It records commit, build gate, node
status, compact-statement SHA-256, canonical page and membership. Statements,
source locations, imports and teaching content remain in the existing index.

* `declaration:<source-qualified Lean name>` preserves the IDs already used by
  the Lean Graph; navigation regrouping cannot change them. Current private
  source names have `identity_basis=source-private-name`: they are not claimed
  to be the compiler's mangled private constant names. A collision fails the
  build, rather than silently merging records. Compiler-name normalization and
  renames require an explicit reviewed ID migration and retained URL aliases.
* `teaching:<slug>` and `spine:<slug>` identify reading references. They resolve
  to the existing graph's `chapter:<slug>` and `spine:<slug>` view nodes. Book IDs
  are stable slugs independent of their displayed title.
* A declaration can occur in several books, chapters and settings. Membership
  is a set of reading references, not a new declaration. Teaching-chapter module
  assignments include an inventory, not necessarily every lemma used by every
  theorem. Source chapters cite their explicit correspondence and primary names.
* Existing setting membership derives from the case ledger's Lean references.
  A placeholder's **related** chapters/cases are not promoted to result evidence
  or canonical setting membership. Unknown fields remain pending source review.
* Node status is `compiled` only in a build preceded by the Lean gate; a preview
  uses `source`, and placeholders/axioms use `stated`. A book's `planned` or
  `source-mapped` status describes its reading map, independently of node status.
  No new-book completion totals are inferred from reused declarations.

Graph JSON attaches the same memberships to the existing node objects.
`lean-graph/scope-index.json` contains canonical reference sets; its book/setting
slices are generated from those same nodes. Book slices start with chapter and
module stubs, and declaration details load from the existing module shards.
The complete graph and registry are explicit downloads, never automatic initial
page loads. Scope selection is an entry view, not a closed subgraph: following
an import or opening a module can reveal shared neighbors outside the selection.

## Four kinds of edges

| Kind | Evidence and meaning |
| --- | --- |
| Module import | Source-scanned `import`; a module-level relation |
| Teaching prerequisite / reading order | Reviewed teaching metadata; no claim of occurrence in a proof term |
| Lean type dependency | Constant occurrence in a compiled declaration type, from a versioned environment export |
| Lean value dependency | Constant occurrence in a compiled declaration value/proof body, separately exported; not a kernel or elaborator trace |

The current browser graph is a navigation graph with typed edge labels. The
Proof Graph Laboratory separately reports a **frozen** compiled-environment
observation with its own commit and hash. This layout change neither refreshes
that export nor turns teaching edges into a proof DAG. Joining an environment
export requires exact symbol and source-version reconciliation, especially for
private/generated constants. Import edges cannot substitute for type/value edges.
No sharing score, novelty result or understanding improvement is claimed.

## Before adding a book, setting, or theorem

1. Search existing definitions, lemmas, canonical declarations and dependencies
   in BanditRLlib and Mathlib. Record candidates in the lemma proposal.
2. Check hypotheses, types, quantifiers, feedback, probability mode and conclusion.
   Reference or reuse a compatible node first. Do not merge incompatible nodes
   to increase a sharing ratio; explain why a new abstraction is needed.
3. Freeze bibliographic version, theorem locator and verification date. New book
   metadata must come from the author or official source. Do not infer chapter
   coverage from a topical resemblance to an existing proof.
4. Add references to the owner JSON, preserving prior URLs. For a new topic,
   fill a separate result record per exact setting with assumptions, feedback,
   method, metric, expectation/high probability, parameter regimes, upper/lower
   bounds, computation/oracle conditions, source/version/date and Lean boundary.
5. Compare bounds only under compatible contracts. Keep known literature,
   compiled/partial Lean and audited literature-open questions separate. Unknown
   citations and missing formalization never establish a mathematical open problem.
6. Run `python -m unittest tools.test_book_registry tools.test_chapter17_site_gate`,
   generate the site, and run the site checker. Use `--allow-unverified` only for
   an honestly marked preview. `--lean-verified` requires a fresh successful
   `python tools/bandit.py check` for the built source.

Inspect desktop and narrow mobile views: nested Books navigation, current-page
state, keyboard disclosure, drawer focus and Escape, old fragments, source
chapters, shared declaration panels, long formulas/tables, graph scope selection
and deferred loading. The site checker validates the registry, graph memberships,
scope consistency, old route anchors, source mappings, links, math and diagrams.
