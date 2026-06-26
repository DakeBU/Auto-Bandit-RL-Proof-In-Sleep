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
- `bandit_scenario_cards.json`.
- `local_leaf_cards.json`.

Search them from the CLI:

```bash
python3 tools/bandit.py search-memory QUERY
```

Task-local memory produced by `memory-refresh` embeds the current global cards
so lower agents can retrieve Mathlib/LML/theory-tree context without scanning
the whole repository.
