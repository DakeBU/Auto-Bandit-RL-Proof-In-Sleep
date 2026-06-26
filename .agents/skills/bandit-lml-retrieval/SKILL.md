---
name: bandit-lml-retrieval
description: Retrieve and use LeanMachineLearning/LML theorem cards without overstating their local Lean status.
argument-hint: "[declaration or task id]"
---

# Bandit LML Retrieval

Use this skill whenever a task references LeanMachineLearning/LML or any
classical bandit theorem already formalized upstream.

## Required Files

Read:

- `research-wiki/lml/theorem-cards.md`;
- `research-wiki/retrieval-index/lml_bandit_cards.json`;
- `research-wiki/mathlib/theorem-cards.md`;
- `research-wiki/scenarios/bandit-scenario-atlas.md`;
- the task conversion window.

If a local LML checkout is available, agents may inspect it through an
environment variable or explicit user-provided location.  Do not write local
filesystem paths into public docs, proof exports, or cited-results entries.

## Status Rules

Use one of:

- `card-only`: upstream theorem used for planning only.
- `ported`: local ABRL declaration implements the result.
- `imported`: ABRL imports a dependency that exposes the declaration.
- `blocked`: toolchain, dependency, or proof mismatch remains.

The default is `card-only`.

## Main Cards

- `Bandits.regret_eq_sum_gap`
- `Bandits.regret_eq_sum_pullCount_mul_gap`
- `Bandits.ETC.regret_le`
- `Bandits.UCB.regret_le`
- `Bandits.TS.hasCondDistrib_action`
- `Bandits.integral_regret_le`

## Companion Search

For each LML theorem card, search companion Mathlib cards before creating
local glue:

```bash
python3 tools/bandit.py reference-index
python3 tools/bandit.py search-memory regret
python3 tools/bandit.py search-memory Finset.sum
python3 tools/bandit.py search-memory integrable
```

Record whether each supporting leaf is already in Mathlib, is an ABRL
`mathlib-candidate`, or is only theorem-card memory.

## Reviewer Rule

Reject any proof note that writes "proved by ABRL" for an LML declaration
unless a local ABRL Lean declaration or imported dependency compiles under the
ABRL gate.
