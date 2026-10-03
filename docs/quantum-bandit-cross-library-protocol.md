# Quantum-bandit cross-library protocol

This protocol applies whenever BanditRLlib formalizes a bandit/RL result whose
information-access model is genuinely quantum.

The canonical Bandit taxonomy node is `quantum-bandits`.  Do not use
"quantum bandit" as one undifferentiated model.

## 1. Freeze the quantum access model first

A contribution must identify which model is being formalized.

At minimum distinguish:

1. **quantum reward-oracle MAB / linear bandits** — coherent unitary access to
   reward distributions or reward-generating oracles;
2. **quantum-state / observable bandits** — arms/actions are measurements or
   observables on unknown quantum states;
3. **quantum contextual / quantum-data bandits** — the context or reward model
   itself is quantum.

A classical MAB theorem does not become a quantum theorem by changing the word
"sample" to "query".  The oracle, inverse-oracle availability, measurement
semantics, query accounting and regret comparator belong in the theorem
contract.

## 2. Search order before new Lean

For every quantum-bandit theorem, the Codex/contributor must search in this
order:

1. **BanditRLlib** for the classical decision skeleton: regret decompositions,
   change of measure, testing, confidence, elimination, OFUL/linear-bandit
   geometry and lower-bound interfaces;
2. **Mathlib** for probability, matrices, linear algebra, finite-dimensional
   Hilbert-space and information-theoretic leaves;
3. **ASPBE / QuantumComputinglib**
   (`DakeBU/Quantum-Computing-Block-Encoding`) for state/operator/oracle,
   circuit, query-interface and quantum proof memory;
4. the quantum Lean reference surfaces already audited by ASPBE:
   - `Hayata-Yamasaki-Group/lean-quantum` (Apache-2.0);
   - `Timeroot/Lean-QuantumInfo` (MIT);
   - `duckki/quantum-computing-lean` (reference only unless its current
     license/toolchain is independently cleared).

Record exact modules/declarations searched.  Do not copy external source across
license or incompatible-toolchain boundaries.

## 3. Cross-library truth boundary

ASPBE and external quantum libraries are **candidate substrates**, not
BanditRLlib proof certificates.

A quantum result becomes local BanditRLlib truth only when one of the following
is explicit:

- an audited compatible dependency is imported and the ABRL declaration
  compiles;
- the required external fact is re-proved locally from an accepted mathematical
  statement;
- a narrow local adapter compiles and proves the bridge between the external
  quantum semantics and the ABRL bandit interface.

Until then, the edge is dashed and labelled `cross-library candidate`.

## 4. Required bridge decomposition

Prefer the following proof decomposition:

```text
quantum oracle/state contract
    ↓
quantum estimation / testing primitive
    ↓
explicit classical-style confidence or distinguishability contract
    ↓
BanditRLlib decision skeleton
    ↓
regret / sample-complexity theorem
```

The purpose is to expose exactly **where the quantum speedup enters**.  If only
the estimation/testing primitive changes, reuse the classical decision layer
instead of reproving it under quantum names.

Lower bounds use the dual decomposition:

```text
bandit regret guarantee
    ↓ bandit-to-testing reduction
quantum testing task
    ↓
query lower bound (e.g. polynomial/adversary/information method)
    ↓
bandit regret lower bound
```

## 5. Canonical source seeds

Current source anchors include:

- Wan, Zhang, Li, Zhang & Sun,
  *Quantum Multi-Armed Bandits and Stochastic Linear Bandits Enjoy Logarithmic
  Regrets*, AAAI 2023:
  <https://ojs.aaai.org/index.php/AAAI/article/view/26202>.
- Lumbreras, Haapasalo & Tomamichel,
  *Multi-armed quantum bandits: Exploration versus exploitation when learning
  properties of quantum states*, Quantum 6:749, 2022:
  <https://doi.org/10.22331/q-2022-06-29-749>.
- Liu, Li & Lui,
  *Quantum Multi-Armed Bandits and Linear Bandits: Lower Bounds and Algorithms*,
  arXiv:2608.14319 (2026 preprint):
  <https://arxiv.org/abs/2608.14319>.

Publication/preprint status must stay visible.

## 6. Graph protocol

Every quantum-bandit contribution updates or explicitly leaves unchanged:

- **Bandit Taxonomy:** exact quantum access subtype;
- **Technique Map:** usually `quantum-estimation-testing` plus any classical
  decision technique reused;
- **Bound & Source Atlas:** only theorem-level upper/lower claims with exact
  oracle/query assumptions;
- **Frontier:** only source-traceable open/resolved questions;
- **Lean Graph:** formal ABRL nodes and dashed candidate cross-library bridges;
- **Functor Hypergraph:** `family:quantum-estimation-testing` or a more precise
  new candidate family when the mechanism is genuinely different.

Never draw an ASPBE theorem as a solid ABRL dependency unless a compiled local
dependency/adapter exists.

## 7. Acceptance checklist

A source-facing quantum-bandit theorem is not integrated until the ordinary ABRL
contributor contract passes **and** the manifest records:

- quantum model subtype and oracle semantics;
- query versus sample accounting;
- source theorem/version/anchor;
- classical BanditRLlib skeleton reused;
- exact ASPBE/external quantum declarations searched;
- license/toolchain decision for each external surface;
- compiled local adapter or explicit `external-reference` boundary;
- source-blind semantic reconstruction;
- independent source review;
- Lean/Overview/Functor graph delta.

This protocol is intentionally conservative: quantum speedup claims are
especially sensitive to oracle strength, so the access model is part of the
mathematical theorem rather than an implementation detail.
