# Retrieval Index

Compact JSON memory used by prompt decks.

Generate global indexes with:

```bash
python3 tools/bandit.py reference-index
```

Generated files:

- `lml_bandit_cards.json`;
- `mathlib_bandit_cards.json`;
- `bandit_textbook_cards.json`;
- `bandit_paper_cards.json`;
- `bandit_scenario_cards.json`.
- `local_leaf_cards.json`.
- `local_lean_declarations.json`.

Search them from the CLI:

```bash
python3 tools/bandit.py search-memory QUERY
python3 tools/bandit.py list-papers
python3 tools/bandit.py list-lean-decls QUERY
python3 tools/bandit.py list-lean-decls QUERY --statement
```

Task-local memory produced by `memory-refresh` embeds the current global cards
and local Lean declaration index so lower agents can retrieve Mathlib/LML,
textbook, paper, theory-tree, and compiled local API context without scanning
the whole repository manually.
