# Independent Review: Finite-Index Geometric All-Time Union And Harness Audit

Date: 2026-08-11
Task: `CONCENTRATION-FINTYPE-GEOMETRIC-ALL-TIME-UNION`
Mode: independent sub-agent, read-only; the reviewer edited no files.

## Verdict

- P0: none.
- P1: none.
- Lean/math statement: accepted; the repository gate and lifecycle promotion
  subsequently passed.
- Chapter/status wording: conservative; no algorithm-level or chapter-level
  completion is inferred from the generic budget adapter.

## Mathematical Findings

The quantifier order, equal-cardinality share, and assumptions are correct.
The theorem works for an arbitrary measure and outer-measure events, requires
`Fintype Idx` plus `Nonempty Idx`, and uses `0 <= delta` only for the exact
geometric terminal. The proof correctly applies countable outer-measure
subadditivity, the finite equal-share wrapper, ENNReal `tsum` monotonicity, and
the exact geometric total. No hidden measurability, probability, independence,
filtration, `delta <= 1`, Ville/Doob, self-normalization, or Freedman premise
was found.

## Harness Findings And Resolution

The reviewer identified four P2 harness defects, all fixed by the main agent:

1. External prompt commands used to record every zero exit as `compiled` and
   every role as `agent`. They now record the actual prompt role and status
   `completed`; only explicit verifier paths may log `compiled`.
2. A later successful prompt/cycle could mask an earlier failure. `run-cycle`
   and `sleep-run` now preserve the first nonzero result while
   `--stop-on-error` controls only early termination.
3. Parallel route ownership allowed empty file sets and syntactic path aliases.
   Validation now requires nonempty ownership, resolves paths canonically under
   the repository root, rejects escape paths, and detects aliases before
   comparing overlap. This remains validation, not concurrency or enforcement.
4. Prompt decks tail-truncated task, conversion, and obligation files. Those
   three contract artifacts now use bounded complete-line head/tail snapshots,
   preserving both theorem headers and current status tails.

Regression tests cover canonical route ownership, prompt-role/status
recording, first-failure aggregation at cycle and sleep-run levels, and
head/tail contract snapshots. Focused harness tests pass: 41 run, 1 expected
skip.

## Reviewer Evidence

- Static inspection of `tools/bandit.py`, `tools/abrl_lifecycle.py`, the Lean
  leaf, root import, both canary surfaces, task/conversion/obligation/blueprint,
  local card, theory-tree/candidate records, and website mappings.
- `safe-verify` passed at statement hash
  `4df3691cb62b7389a0d544c661127aaca4ec3a81981d0474430dad1f5ca2c179`.
- The reviewer did not claim an independent Lean compile because its focused
  build was interrupted at the main agent's request; the main agent's focused,
  root, Tests, and external-canary builds are recorded separately.
- Post-review promotion evidence: verified memory `mem-99363842cb89e027`,
  accepted frontier and DAG, current-task digest, zero shadow mismatches, and a
  passing full repository gate.
