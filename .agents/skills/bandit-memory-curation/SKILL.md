---
name: bandit-memory-curation
description: Update ABRL theorem cards, cited results, proof-attempt memory, and retrieval indexes after proof progress or failure.
argument-hint: "[task id]"
---

# Bandit Memory Curation

Use this skill after any nontrivial proof attempt or literature lookup.

## Required Commands

```bash
python3 tools/bandit.py memory-refresh <task-id>
python3 tools/bandit.py reference-index
python3 tools/bandit.py search-memory <query>
python3 tools/bandit.py trial-summary
```

## What To Store

- compiled declarations and their proof role;
- theorem cards used;
- blocked cited results;
- rejected routes and why they were invalid;
- proof fragments worth reusing;
- exact next leaf.
- local APIs/imports and intended proof route for each active leaf;
- hidden regularity contracts promoted to reusable obligations;
- Mathlib candidate leaves and their upstream-readiness status;
- Mathlib retrieval cards searched before creating general lemmas;
- textbook and scenario cards used to place the theorem in the theory tree;
- persistent failure diagnoses, including missing assumptions or possible
  counterexamples.

## Directory Map

| Directory | Use |
| --- | --- |
| `research-wiki/lml/` | upstream LML theorem cards |
| `research-wiki/mathlib/` | Mathlib retrieval cards for reusable leaves |
| `research-wiki/textbooks/` | classic textbook and survey source cards |
| `research-wiki/scenarios/` | bandit/RL scenario taxonomy |
| `research-wiki/theory-tree/` | source-to-leaf proof tree |
| `research-wiki/cited-results/` | external theorem contracts |
| `research-wiki/proof-techniques/` | reusable proof patterns |
| `research-wiki/mathlib-candidates/` | general leaf lemmas to prepare for Mathlib |
| `proof-attempts/<task-id>/` | failed or partial local Lean attempts |
| `research-wiki/retrieval-index/` | compact JSON for future prompts |

## Reviewer Rule

If a run fails and leaves no memory update, classify the result as incomplete
even if the transcript contains useful information.

If a run changes proof route without recording the mathematical reason,
classify the memory update as incomplete.  Agents should not repeatedly rewrite
the proof plan when the right response is to recheck the statement or
hypotheses.
