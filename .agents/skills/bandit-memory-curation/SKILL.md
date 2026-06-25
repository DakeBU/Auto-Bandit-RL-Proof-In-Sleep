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
python3 tools/bandit.py trial-summary
```

## What To Store

- compiled declarations and their proof role;
- theorem cards used;
- blocked cited results;
- rejected routes and why they were invalid;
- proof fragments worth reusing;
- exact next leaf.

## Directory Map

| Directory | Use |
| --- | --- |
| `research-wiki/lml/` | upstream LML theorem cards |
| `research-wiki/cited-results/` | external theorem contracts |
| `research-wiki/proof-techniques/` | reusable proof patterns |
| `proof-attempts/<task-id>/` | failed or partial local Lean attempts |
| `research-wiki/retrieval-index/` | compact JSON for future prompts |

## Reviewer Rule

If a run fails and leaves no memory update, classify the result as incomplete
even if the transcript contains useful information.
