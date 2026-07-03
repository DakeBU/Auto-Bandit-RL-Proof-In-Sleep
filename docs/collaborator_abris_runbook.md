# Collaborator ABRIS Runbook

ABRIS is the operational name for running this ABRL repository as an
in-sleep hierarchical proof system.  The repository remains ABRL; the run loop
is ABRIS-style automation.

## Before Spending Agent Budget

Run these commands first:

```bash
python3 tools/bandit.py check
python3 tools/bandit.py list-routes
python3 tools/bandit.py unfinished
python3 tools/bandit.py list-lean-decls --statement
```

Then inspect the route you intend to work on:

```bash
python3 tools/bandit.py route-plan ROUTE-UCB1-FINITE-STOCHASTIC --with-commands
```

The key distinction is:

- `route-plan` is for upper/middle planning;
- `unfinished` is for picking missing or theorem-card leaves;
- `list-lean-decls --statement` is for reusing compiled local proof material;
- lower agents should receive one exact Lean leaf, not a whole route.

## Recommended Screen Packet

Generate a task-specific packet:

```bash
python3 tools/bandit.py screen-plan BRL-UCB-PORT-001 \
  --route ROUTE-UCB1-FINITE-STOCHASTIC \
  --cycles 2 \
  --lower-count 4
```

The command prints a `screen` session name, preflight commands, the sleep-run
command, and reviewer checks.

## Running With Codex

A typical executed run is:

```bash
screen -S abrl-BRL-UCB-PORT-001

python3 tools/bandit.py blueprint-refresh BRL-UCB-PORT-001
python3 tools/bandit.py memory-refresh BRL-UCB-PORT-001
python3 tools/bandit.py sleep-run BRL-UCB-PORT-001 \
  --cycles 2 \
  --lower-count 4 \
  --execute \
  --agent-profile codex-parallel.example.json \
  --check-each-cycle \
  --stop-on-error
python3 tools/bandit.py memory-refresh BRL-UCB-PORT-001 --run-id latest
python3 tools/bandit.py blueprint-refresh BRL-UCB-PORT-001
python3 tools/bandit.py check
```

If the profile is not the right one for the local Codex installation, replace
it with an explicit command:

```bash
python3 tools/bandit.py sleep-run BRL-UCB-PORT-001 \
  --cycles 2 \
  --lower-count 4 \
  --execute \
  --agent-cmd 'codex exec --cd {root} < {prompt}' \
  --check-each-cycle \
  --stop-on-error
```

## Role Discipline

| Role | Allowed work | Rejected work |
| --- | --- | --- |
| Upper | choose route, compare source cards, propose several proof paths | editing Lean directly |
| Middle | create one-leaf packets with statement, APIs, route, contracts, retrieval evidence | sending broad theorem goals to lower |
| Lower retrieval | find Mathlib/LML/local declarations and imports | treating paper prose as proof dependency |
| Lower NL prover | explain one mathematical leaf and assumptions | changing the theorem target |
| Lower Lean worker | prove one leaf or produce a precise blocker | repeatedly rewriting the proof route |
| Reviewer | enforce target stability, contract visibility, and build gate | accepting uncompiled claims |

## UCB-Specific Warning

The repository has UCB-adjacent compiled leaves, but not a finished UCB theorem.
`UCBSummability` proves finite bad-event summability.  It does not prove the
sqrt/log index, positive initialization, good-event pull-count threshold, or
logarithmic regret theorem.

Before a lower worker touches UCB, middle should write one of these exact
leaf packets:

| Leaf packet | Local APIs to search first |
| --- | --- |
| positive initial count | `pullCount`, `ETC`/initialization count lemmas, `Nat.cast_pos` |
| UCB radius definition | `Real.sqrt`, `Real.log`, positivity side conditions |
| UCB maximality algebra | argmax/index API, order lemmas, gap definitions |
| bad-event decomposition | sub-Gaussian upper/lower tail wrappers, `UCBSummability` |
| expected pull count | expectation pull-count decomposition, finite bad-event budgets |

## Persistent Failure Protocol

After repeated failure on the same leaf, stop tactic search and write a
failed-attempt card containing:

| Field | Required content |
| --- | --- |
| Exact failed statement | The Lean theorem shape that failed. |
| Last stable route | The proof path that was attempted. |
| Failure type | missing assumption, wrong statement, API mismatch, counterexample risk, or dependency missing. |
| Proposed repair | weaker statement, added regularity contract, Mathlib search target, or upstream theorem card. |
| Reviewer action | accept blocker, request new statement, or send to NL prover. |

This is not wasted work.  Persistent failure is evidence about the mathematics
or the statement shape and should be compressed into memory.

## Closeout

After each run:

```bash
python3 tools/bandit.py trial-summary
python3 tools/bandit.py memory-refresh BRL-UCB-PORT-001 --run-id latest
python3 tools/bandit.py blueprint-refresh BRL-UCB-PORT-001
python3 tools/bandit.py unfinished
python3 tools/bandit.py check
git status --short
```

Do not claim a route is done unless `python3 tools/bandit.py check` passes and
reviewer accepts that the compiled Lean theorem matches the prose claim.
