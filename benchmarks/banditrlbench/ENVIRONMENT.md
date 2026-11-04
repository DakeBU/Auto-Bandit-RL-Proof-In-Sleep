# Environment and execution boundary

Use Python 3.11+, Git, and the exact committed `lean-toolchain` and
`lake-manifest.json`. From a disposable checkout, fetch the pinned Mathlib cache,
then run `python tools/bandit.py check` before formal replay. The runner checks
toolchain/manifest compatibility and that task-owned source modules still match
the frozen Git blobs (normalizing Windows line endings). Imported `.olean`
artifacts remain a trusted build input; a source hash alone does not certify
them. Every replay records the library commit, dirty state and manifest hash.

The documentation build runner is pinned to Ubuntu 24.04 with Playwright 1.58.0.
An actual 2026-11-04 CI attempt passed the full library, Bench canaries and site
checks, then failed before browser execution because `ubuntu-latest` supplied
Ubuntu 26.04, unsupported by that Playwright version. The runner pin preserves
the browser gate rather than skipping it; see Actions run 41786531446.

## What runs today

- Python prompt preparation and response-bound expert-review packets, without
  model calls or Lean dependencies for the NL track.
- Trusted-local fixed-signature Lean replay with per-task wall-clock timeout,
  compiler logs, allowed axiom closure (`propext`, `Classical.choice`,
  `Quot.sound`) and direct type/proof constants from the compiled environment.
- Positive reference and negative empty/incorrect/placeholder canaries in CI.
- Public dev training exports, with solutions only after an explicit flag.

`--trusted-local` acknowledges executable Lean elaboration. The token filter and
axiom check are not a security boundary. Use only trusted proofs in a disposable
environment; do not execute untrusted submissions on a credentialed workstation.
The timeout bounds one compiler process's wall time; it is not a process-tree,
memory, CPU, filesystem or network isolation guarantee. No untrusted predictions
are replayed by the repository workflow: CI uses bundled reference/negative data.

## Container and Harbor release gate (not implemented)

An untrusted-code release must isolate the agent from verifier/solution files;
freeze the toolchain, package revisions, base image digest and task data; run
as an unprivileged user with a read-only base and bounded writable scratch;
disable credentials/network; cap the entire process tree's CPU, memory and time;
and collect artifact hashes outside the sandbox. Test good proofs, no-op,
wrong-type proofs, axiom/command injection, output spoofing, timeouts and solution
leakage. Replicate oracle and no-op trials before publishing results. Docker is
not available in the current development environment, so no image or Harbor
compatibility is claimed. A checked-in Dockerfile without an executed image
would not close this gate.

Design references: [Harbor task anatomy](https://docs.harborframework.com/tasks/overview)
and [Terminal-Bench contribution guide](https://github.com/harbor-framework/terminal-bench/blob/main/CONTRIBUTING.md),
consulted 2026-11-04. These inform the interface, not task content or an affiliation.
