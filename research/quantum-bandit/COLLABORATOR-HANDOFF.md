# Quantum Bandit frontier: collaborator handoff

Updated: 2026-10-09. **Public research prototype; neither project A nor project B is complete.**

## Research questions

**A: Finite coherent-block regret.** Establish an implementable estimator and a horizon-safe bandit policy when a fresh quantum block can query one arm at most D times. Count both the reward unitary U and its matching inverse U-dagger. Classical history survives between blocks; quantum registers do not. Regret upper bounds, matching lower bounds and optimality remain open.

**B: Circuit-certified cost-aware multi-fidelity BAI.** Select actual circuit implementations using target-bias certificates, coherence limits and proved query/gate costs. Repetition reduces statistical error, not fixed implementation bias. The complete fidelity-selection algorithm, stopping rule, total-cost theorem and mixed-fidelity lower bound remain open.

The quantum library supplies circuit, measurement, inverse and resource semantics. BanditRLlib supplies confidence, elimination, pull-count, regret and testing structure. Existing classical multi-fidelity work and recent quantum estimation/bandit papers are prior art, not local proof premises. See [the literature audit](evidence/literature-audit.md).

## Current checkpoint

- **Compiled research increments:** Born probability stability; aligned circuit reward bias; forward/inverse query words and primitive gate accounting; a cross-library adapter and canaries; actual reset-history PMFs and fixed-finite-block adaptive Hellinger information accumulation.
- **Conditional transport:** bias plus statistical radius, confidence elimination and recommendation correctness. Actual estimation-tail producers remain missing.
- **Open roots:** concrete estimation/confidence, horizon-safe A strategy and regret bounds, B fidelity choice/stopping/cost, and information-theoretic lower-bound assembly.
- **Scope of the newest information theorem:** computational-basis measurement, deterministic classical-history policy, fixed finitely many blocks, natural-number path budget and both environments' expected query costs. It is not a stopping theorem or a K-arm minimax result.

Read [the exact research boundaries](research-boundaries.md) and [immutable historical audit evidence](evidence/adaptive/). Public availability does not imply main-library admission; earlier seal coverage and publication-pipeline boundaries remain visible.

## Independent-machine setup

Prerequisites: Git and elan. All three Lake projects pin Lean 4.29.1 and Mathlib `5e932f97dd25535344f80f9dd8da3aab83df0fe6`. Samplinglib is not a compatible dependency of this checkpoint. Do not copy another contributor's environment caches or local junctions.

Use a fresh parent directory. The two sibling directories must be named `bandit` and `quantum` for the joint project's relative path dependencies.

```powershell
git clone --branch research/qb261009 https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep.git bandit
git clone --branch research/qb261009 https://github.com/DakeBU/Quantum-Computing-Block-Encoding.git quantum

Set-Location quantum
git switch --detach b541c64bfbc0c1f416db8959d306d360508e2cf6
git switch -c collab/yourname-quantum-measurement
lake exe cache get
lake build
lake build Tests

Set-Location ../bandit
git switch --detach 64eb285ebecbdc4bf236318776aabc6160fb1851
git switch -c collab/yourname-bandit-measurement
git rev-parse HEAD
lake exe cache get
lake build
lake build Tests

Set-Location research/quantum-bandit
lake build QuantumBanditAdapter Canary AdaptiveTranscript AdaptiveTranscriptCanary
lake exe adaptive_dependency_export evidence/adaptive/reproduced-proof-term-graph.json
```

Check every exit status. Record the actual two commits and distinguish network/cache failures from mathematics failures. Never reset or check out a different branch in an existing dirty collaborator workspace.

The fixed Bandit mathematics/evidence release is `64eb285ebecbdc4bf236318776aabc6160fb1851`, whose latest proof-bearing parent is `5638277b618ee4bf0d3c61aae12991f4f2cbdf01`. Later handoff edits do not change that mathematics. The fixed snapshot includes an older handoff version: use this current English handoff for instructions while keeping the mathematics pinned.

Historical BornStability source-review raw hashes came from a CRLF Windows worktree; the pinned Quantum Git blob uses LF. A separate [portable binding supplement](evidence/adaptive/portable-source-bindings.json) records exact historical/Git-blob/canonical-LF hashes and verified normalized byte equality for five Lean sources. The original review is unchanged. Its 23 evidence artifacts retain exact bytes through the directory's `-text` Git attribute. Obtain the later portability supplement from the commit containing this current handoff, rather than assuming it exists in the older mathematics snapshot.

## Copyable bounded continuation goal

> Continue from the public Quantum Bandit research checkpoint. First read both repositories' AGENTS.md and publication/source-fidelity/Statement Seal/proof-graph protocols, the research README, research-boundaries.md and adaptive evidence. Freeze both actual commits, Lean 4.29.1 and the Mathlib pin; reproduce the adapter and canary in personal branches. Do not redo the completed Born-stability or adaptive-information proofs, overwrite collaborators, or merge main.
>
> Complete one bounded increment: an actual depth-limited amplitude-estimation measurement and query-cost producer. Pin the primary model to Erle and Koczor, arXiv:2608.24434v1, Measurement Model Eq. (1) and Algorithm 1. Freeze exact Lean signatures before proof search; independently extract and review the source construction topology. Start with a general finite-dimensional unitary, a known initial basis vector and a known good-coordinate projector. Produce the actual unitarity certificates for known reflections, odd/even query words, output probabilities, response means and literal forward-plus-inverse query counts. Charge the last inverse needed to implement the even-depth unknown-state readout as known-basis measurement. Handle zero queries and D=1. An odd-only schedule does not establish the cited estimator's full admissible-window confidence guarantee.
>
> Each block selects one arm classically, starts afresh, permits at most D calls to that arm's U or matching U-dagger, measures once and discards all quantum registers. Both oracle directions consume the horizon and the selected arm's gap. Unknown angles/means are analysis variables, not available algorithm inputs. Reflections, loading, synthesis, known gates and physical depth have explicit resource boundaries. A confidence interval does not imply independent unbiased sub-Gaussian estimator noise. Fixed systematic circuit bias is separate from noise changing between calls.
>
> Reuse QuantumQueryWord, QueryCircuitCost, PrimitiveSemantics, BornStability and ResetBlockProcess. Produce a real one-qubit primitive-circuit canary and gate-count certificate. If general reflection synthesis remains unproved, name that supplier rather than assume it and claim a complete gate-cost root. Any model refinement must be separately named with an explicit semantic delta.
>
> Finish the bounded measurement/cost increment with actual Lake compilation, executable canary, printed axioms, placeholder/new-axiom scan, actual compiled type/value dependency graph and distinct source-blind decoder/source reviewer seven-slot audits. Run both repositories' required build/Tests and publication checks; synchronize reader, graph and frontier evidence without promoting unfinished roots. Retain typed failures. Report compiled, conditional, speculative and refuted separately. Estimator statistics, A regret, B complexity and novelty remain open until their actual producers close. Submit personal branches and draft PRs; do not merge main.

## Parallel leaves and handback

Coordinate leaf ownership in [tracking issue #206](https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/issues/206). Another contributor can own B's finite feasible-fidelity selector, including empty sets, b<r, integer caps and known-gate costs, while retaining the missing-estimator boundary. A separate lower-bound leaf concerns stopped/one-environment information comparison, hard unitary families and testing-to-regret reduction; the existing symmetric information bound does not automatically supply the K factor.

Hand back exact source/version/anchor, frozen signatures, base/head commits, Lean declarations, actual dependencies, canary, verification commands/exit statuses, independent audit and remaining leaves. Push only the personal branch and open a draft PR. Public research authorization does not bypass either library's admission protocol.
