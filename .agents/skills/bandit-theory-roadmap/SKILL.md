---
name: bandit-theory-roadmap
description: Select and organize bandit/RL proof targets from textbook cards, paper cards, scenario cards, and the ABRL theory tree.
argument-hint: "[scenario or theorem]"
---

# Bandit Theory Roadmap

Use this skill when proposing a new theorem target, extending the proof tree,
or mapping a paper theorem into ABRL memory.

## Required Commands

```bash
python3 tools/bandit.py reference-index
python3 tools/bandit.py list-papers
python3 tools/bandit.py list-scenarios
python3 tools/bandit.py search-memory <scenario-or-algorithm>
```

## Required Files

Read:

- `research-wiki/textbooks/bandit-classics.md`;
- `research-wiki/papers/bandit-frontier-cards.md`;
- `research-wiki/scenarios/bandit-scenario-atlas.md`;
- `research-wiki/theory-tree/bandit-theory-tree.md`;
- `research-wiki/mathlib/theorem-cards.md`;
- task-local conversion windows and proof obligations.

## Target Selection Rule

A new target should name:

- source card: textbook, paper, LML, or Mathlib;
- scenario card;
- proof branch;
- first three leaf lemmas;
- Mathlib retrieval cards for each general leaf;
- hidden regularity contracts;
- current blocked technology.

## Reviewer Rule

Reject a proposal that only names an algorithm or paper theorem.  It must also
identify the source branch, local APIs, intended proof route, and memory files
that future lower agents can actually use.
