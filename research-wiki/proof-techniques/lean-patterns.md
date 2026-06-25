# Lean Patterns For ABRL

## Dependency-Light Layer

Use recursive definitions when possible:

- `pullCount action arm 0 = 0`;
- `pullCount action arm (t + 1)` unfolds by `rfl`;
- `sumRewards` follows the same pattern.

This avoids needing Mathlib finite sums for early executable tests.

## Theorem-Card Layer

When a theorem needs probability or measure theory, record the upstream
declaration first.  Do not recreate a large API from memory.

Good theorem-card fields:

- declaration;
- module;
- assumptions;
- proof role;
- local status;
- import or port plan.

## Mathlib/LML Layer

Before adding dependencies:

1. write the exact target in `conversion-windows/`;
2. list the required imports;
3. decide whether toolchain alignment is acceptable;
4. run the full gate;
5. update attribution.

## Common Failure Classes

- `source translation gap`: prose theorem is not mapped to Lean symbols.
- `theorem-card dependency`: upstream theorem is known but not local.
- `semantic interface gap`: local ABRL definitions cannot express the theorem.
- `local Lean lemma gap`: proof needs a small compiled lemma.
- `invalid route`: proof changed assumptions or target.
