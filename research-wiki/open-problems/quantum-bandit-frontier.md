# Quantum Bandit A+B: frontier auto-formalisation started

Launch: **2026-10-09**. Status: **research started; complete algorithms and research-root theorems open**.

Public progress and leaf coordination: [tracking issue #206](https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/issues/206).

This is an owner-authorized public research launch linking BanditRLlib and
QuantumComputinglib. It is not an announcement of a new proved quantum advantage,
a globally novel problem, an optimal algorithm, or a main-library accepted theorem.

## Two linked questions

**A — Quantum MAB with Finite Coherent-Block Query Budget.** How does cumulative
pseudo-regret depend on a cap D on coherent reward-oracle calls between resets?
The candidate elimination analysis targets a depth-limited mean-estimation cost
of soft-O(1/r + 1/(D r²)), then gap-dependent and gap-free regret bounds, followed
by an information-theoretic lower bound in a precisely matching model. All of
these algorithm/complexity roots remain unproved locally. Essential horizon and
confidence logarithms cannot be discarded when taking the ideal-coherence limit.

**B — Circuit-Certified Cost-Aware Multi-Fidelity Quantum BAI.** Given actual
implemented circuits at several fidelities, how should epsilon-BAI choose their
precision and coherence under proved target-bias and resource certificates?
The candidate per-arm envelope minimizes an estimator's real cost over levels
with b<r. Confidence logs, integer caps, known gates, loading/readout and empty
feasible sets need explicit treatment. This envelope and mixed-fidelity optimality
are research targets, not proved theorems.

## Access model is part of the question

Classically choose a single arm between quantum blocks. A block starts afresh,
intersperses specified known unitaries with that arm's fixed U or matching U†,
uses at most D such calls in total, then measures and discards every quantum
register. Classical history persists. Every U **and** U† consumes T and charges
the selected arm's gap. Shots, oracle calls, primitive gate counts, physical depth
and wall-clock are different resources.

An ordinary reward sample or a quantum-state copy does not imply this reversible
oracle access. Unknown-state reflections and unknown-mean angles are not free.
For B, each fidelity's circuit is fixed: its systematic bias is distinct from
noise changing between oracle calls. State loading and general reflection synthesis
need separate certificates before a complete gate-cost claim.

## Exact checkpoint and evidence

The public Bandit research release is pinned at
[`64eb285ebecbdc4bf236318776aabc6160fb1851`](https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/tree/64eb285ebecbdc4bf236318776aabc6160fb1851),
with Quantum release
[`b541c64bfbc0c1f416db8959d306d360508e2cf6`](https://github.com/DakeBU/Quantum-Computing-Block-Encoding/tree/b541c64bfbc0c1f416db8959d306d360508e2cf6).
Both descend from frozen main bases, use Lean 4.29.1 and Mathlib
`5e932f97dd25535344f80f9dd8da3aab83df0fe6`, and remain outside main.

The [research README](https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/blob/64eb285ebecbdc4bf236318776aabc6160fb1851/research/quantum-bandit/README.md)
maps actual declarations and dependencies. The
[adaptive evidence](https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/tree/64eb285ebecbdc4bf236318776aabc6160fb1851/research/quantum-bandit/evidence/adaptive)
contains frozen source/signatures, reader lesson, distinct blind reconstruction and
seven-slot source review, compiler logs, axiom output and actual proof-term graph.
Historical private-only labels and machine paths are retained as historical facts;
the owner explicitly ended confidentiality for this release. No retrospective
Statement Seal repair or new independent-review verdict is invented.

A separate [portable source-binding supplement](https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/blob/ad9a15f02fc9915ecf98869af9a61f4c3b3c6d2c/research/quantum-bandit/evidence/adaptive/portable-source-bindings.json)
records the historical CRLF versus Git-blob LF hash difference for BornStability;
normalized source bytes agree. Historical review hashes/verdicts are unchanged.

| Evidence state | What is available |
|---|---|
| Compiled research increment | Born probability stability, aligned circuit bias, chronological forward/inverse query semantics, actual primitive expansion/cost, cross-library adapter and canaries |
| Compiled research increment | Fresh computational-basis PMFs, fixed-n classical adaptation, finite-kernel Hellinger chain, actual transcript/list-law bridge and natural-budget information bound |
| Conditional transport | Bias plus statistical radius, interval elimination and recommendation correctness given explicit estimation-tail suppliers |
| Speculative/open | Concrete estimator/confidence producer; A horizon-safe policy and regret upper/lower roots; B selector/stopping/total-cost and mixed-fidelity lower roots |
| Refuted target boundary | Fixed irreducible identical biased oracles cannot uniformly identify the ideal epsilon-best arm below their identifiability scale; the checkpoint contains the mathematical example, not a Lean lower-bound theorem |

The newest information theorem uses unhalved H² and proves

    H²(P_E, P_F) ≤ (D/2) (E_E C_eta + E_F C_eta),
    C_eta = sum over blocks of q_block * eta_selected_arm².

For uniform oracle distance eta and a natural all-trace budget T, H²≤DT eta².
Its scope is fixed finitely many blocks, computational-basis measurement and a
deterministic classical-history policy. Random stopping, arbitrary measurements,
hard oracle families and testing/regret reduction are missing. Both environments'
costs appear; replacing them with one environment's arm counts is not justified.
The theorem therefore does not yet prove a sqrt(KT/D) minimax lower bound.

The latest focused modules/canary and both libraries' full Lean build/Tests passed
at the recorded checkpoint. The 28 authored adaptive declarations use only the
standard reported Mathlib axioms (or none); no sorry/admit/new source axiom was used.
Source review accepted explicit finite-trace/natural-budget restrictions. Earlier
prototype exact-signature coverage debt and the Quantum Windows/publication pipeline
boundary remain visible. Main integration and strict publication admission are
separate from kernel checks and branch availability.

## Prior work and novelty boundary

[Erle–Koczor, arXiv:2608.24434v1](https://arxiv.org/html/2608.24434v1)
already provides an arbitrary-depth amplitude-estimation tradeoff; it remains an
external theorem until the required circuit/measurement/statistical adapter is
proved locally. [Liu–Li–Lui, arXiv:2608.14319v1](https://arxiv.org/html/2608.14319v1)
provides quantum Bandit lower bounds and prevents dropping essential horizon logs.
[Poiani et al., arXiv:2406.03033v2](https://arxiv.org/html/2406.03033v2)
already studies optimal classical multi-fidelity BAI: bias-radius composition alone
is not new. These preprint versions and mathematical model differences are kept
explicit. NeurIPS 2026 memory-decoherence and limited-adaptivity BAI were previously
audited at official-abstract level only; their full models remain a source-audit leaf.
No global absence-of-prior-work claim follows.

## Next open leaves and collaboration

1. **QB-ESTIMATOR-MEASUREMENT-AND-CONDITIONAL-CONFIDENCE:** actual odd/even-depth
   measurement circuits, charged inverse and known-reflection costs; then admissible
   window/least-squares statistics and confidence for each supported history.
2. **QB-A-HORIZON-SAFE-POLICY-AND-REGRET:** actual dyadic elimination, integer budget
   clipping, ties, K>T, D=1, stage failure budget and expected regret assembly.
3. **QB-B-FIDELITY-SELECTOR-STOPPING-AND-GATE-COST:** finite feasible argmin, empty-set
   behavior, certified query/shot/gate costs, epsilon-BAI termination and comparison.
4. **QB-STOPPED-INFORMATION-HARD-ORACLES-AND-TESTING:** hard unitary family,
   one-environment/stopped comparison and K-arm testing-to-regret reduction.

The [Chinese explanation, computer setup and copyable collaborator goal](https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/blob/ad9a15f02fc9915ecf98869af9a61f4c3b3c6d2c/research/quantum-bandit/COLLABORATOR-HANDOFF.md)
allows continuation from current proofs rather than restarting the library audit.
Work on personal branches, claim one bounded leaf, retain typed failures and exact
compiled/conditional/speculative/refuted boundaries, and submit draft PRs under both
libraries' protocols. Do not overwrite collaborator progress or merge main.
