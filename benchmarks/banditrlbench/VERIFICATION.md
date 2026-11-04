# Seed verification boundary

Base source snapshot: ee8c0b805c785220ee31799012325f4179dad875. No production Lean theorem is changed. The two references apply existing source declarations.

Actual reference command: `lake env lean <seed-checkout>/benchmarks/banditrlbench/lean/Reference.lean` from an existing built workspace at commit f7e3ec872aea7c82dc2bcc4a825058b358c0f987. Both imported project source modules are unchanged between that environment and the pinned source snapshot (checked with Git diff). Lean 4.29.1 and the pinned Mathlib environment are retained. This is a recorded reference-environment check, not a fresh build of the whole current main. Both printed axiom sets contain only propext, Classical.choice and Quot.sound. No sorry/admit or new axiom appears in the reference.

Registry/source checks, export-leakage and contract-mutation tests, site preview, content review and rendering evidence are recorded before delivery. These checks do not automatically admit semantic gold, prove whole-library graph coverage or supply a model evaluator. Full current-checkout Lean/Tests/harness and verified site gates remain required before main integration. No merge, live deployment, model run, training, paid API call or new mathematical result is claimed.

## Actual development checks

- Registry validator and both prompt exports passed; 4 regression tests passed, including gold exclusion, contract drift, source rebinding and shared track bindings.
- Unverified website preview build and `check_site.py --allow-unverified` passed. The Windows raw-source hash boundary needed identical Git-blob bytes temporarily for OnlinePrescientBregman.lean; no production Lean diff is included.
- Headless Edge screenshots of overview/NL/Lean pages at 1440 and 390 widths show no page overflow. Overview and opened NL solution were visually inspected. Common website shell is retained.
- Distinct automated content reviewer `/root/frontier_launch_review` found no blocking mathematical defect in the four candidate answers and two existing-lemma applications. It verified pinned source hashes and selected file equality, not transitive/current-root compilation. Its clarity request for a self-contained BRB-002 prompt was applied. This bounded review is not expert gold admission, model scoring or certification of every future contribution.
- All added publication prose is English. No cross-library promotion was added. The contribution manifest and diff gates are checked on committed source before push.


## 2026-11-04 operational increment

The original seed is merged (#271/#272). This increment preserves every sealed
NL question and production theorem. Fixed formal signatures are SHA-256 sealed
in `targets.json` and checked against the existing `Reference.lean` signatures.
`notation.json` changes only the presentation of literal expressions.

Actual local canary command:
`python tools/banditrlbench.py canary --trusted-local --library C:/qb261009/news --output C:/qb261104/canary-final`.
Replay ran from clean runner commit e31c6648fbdea45d84619693e944730461efcffb; exact runner-file hashes are in the receipt. Both references kernel-checked; empty, wrong-type and placeholder controls failed
as intended. `reference-replay.json` records the real prebuilt library commit,
dirty state, toolchain, manifest, proof/target hashes, axioms and direct type/value
constants. This is a trusted reference replay, not a fresh whole-root build or a
sandboxed model trial. `canary-check.json` records expected versus actual outcomes.
The wrong-type proof produced a compiler error and a `sorryAx` diagnostic; the
runner correctly rejected it rather than treating axiom output as success.

Seventeen unit regressions cover gold exclusion, source/contract drift, immutable
source commits, fixed target/response binding, reviewer completion, empty-answer
credit, axiom/dependency output rejection, graph-node existence and notation-only
projection. The full offline formula test compiled 918 unique formulas from 71
pages without errors. Actual headless Edge inspections at 1440 and 390 widths
covered five Bench routes, expanded proofs and direct graph selection; no page
overflow or math error occurred. The formalizer inspected desktop/mobile formula
and workflow screenshots. These are interface/harness checks, not expert gold or
an independent mathematical review. CI also tests both actual QA tracks and
valid/absent graph permalinks.

Full current-candidate library/Tests/harness, site checks, canaries and browser
math gate remain mandatory in CI. Publication status is reported separately from
these local observations. Gold admission, grouped held-out split, untrusted-code
sandbox, tested Harbor integration and model performance remain open.
