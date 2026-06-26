# Conversion Windows

Conversion windows keep natural-language theorem statements, Lean names,
assumptions, and proof-DAG leaves synchronized.

For each active leaf, record more than the theorem name:

- local APIs/imports;
- intended proof route;
- hidden regularity contracts;
- Mathlib status;
- pivot rule for persistent failure.

Lower agents should not receive an underspecified leaf.  If a proof repeatedly
fails, the conversion window is the place to revise the statement, add a
missing assumption, or record a counterexample diagnosis.
