# Lean Style

ABRL starts with a dependency-light Lean core and grows toward Mathlib/LML only
when a task needs that strength.

## Current Layer

- Use `Std` and Lean core for finite executable structures.
- Keep theorem-card records and automation contracts build-tested.
- Avoid `sorry`, `admit`, `axiom`, and `postulate`.
- Prefer small named declarations over long tactic blocks.
- Do not introduce an assumption only to make a theorem easy.

## Mathlib/LML Layer

When a task needs probability, kernels, conditional distribution, integrals,
asymptotics, or concentration:

1. create a conversion window;
2. list the needed Mathlib or LML declarations;
3. decide whether to port or import;
4. isolate toolchain and dependency changes;
5. run `lake build && lake build Tests`;
6. update attribution and memory.

## Reviewer Checks

Run:

```bash
python3 tools/bandit.py check
```

Then inspect:

- whether the theorem statement still matches the task;
- whether theorem-card names are marked as local proofs only after import/port;
- whether failed proof fragments were stored in `proof-attempts/`;
- whether proof-export prose names exactly the compiled declarations.
