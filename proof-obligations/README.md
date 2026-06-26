# Proof Obligations

Each file is a proof-DAG ledger.  Lower agents should work on one active leaf
at a time and update the ledger after success or failure.

Each active leaf must name:

- local APIs/imports;
- retrieval cards from Mathlib, LML, textbook, or scenario memory;
- intended proof route;
- regularity contracts;
- Mathlib status;
- current gate and status.

If repeated attempts fail, record the mathematical signal before changing the
proof route: missing assumption, false statement, counterexample, API mismatch,
or stale source mapping.
