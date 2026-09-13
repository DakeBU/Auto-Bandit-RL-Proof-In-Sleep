# GAP-ENTROPY-EXTERNAL-BRIDGE — P0 source-port and graph-delta task

Problem id: `GAP-ENTROPY-EXTERNAL-BRIDGE`

Priority: **P0**

Status: external formalization audited and graph bridge published on the feature branch; local source port not yet claimed.

## Why this is P0

Chen and Li's COLT 2016 open problem is a rare frontier case with all of the ingredients BanditRLlib wants to study simultaneously:

1. a decade-old, precisely stated bandit conjecture;
2. important partial progress (Chen–Li–Qiao, COLT 2017);
3. two 2026 mathematical resolution routes appearing within days of each other;
4. a public Lean 4 formalization with source-statement alignment metadata;
5. a nontrivial graph contribution that is richer than adding one terminal theorem.

This makes it a calibration case for the future `LEAF / BRIDGE / SHORTCUT / HUB / RE-ORGANIZATION` contribution taxonomy.

## Primary sources

- Lijie Chen and Jian Li, *Open Problem: Best Arm Identification: Almost Instance-Wise Optimality and the Gap Entropy Conjecture*, COLT 2016: <https://proceedings.mlr.press/v49/chen16b.html>.
- Lijie Chen, Jian Li and Mingda Qiao, *Towards Instance Optimal Bounds for Best Arm Identification*, COLT 2017: <https://proceedings.mlr.press/v65/chen17b.html>.
- Jiarui Yao, Jiaxi Zhao and Xiangxin Zhou, *Gap Entropy and Almost Instance-Wise Optimal Best-Arm Identification*, public formalization repository: <https://github.com/zhouxiangxin1998/GapEntropy>.
- P. M. Aronow, Nathan Kallus and Patrick Lopatto, *A positive resolution of the gap-entropy conjecture*: <https://arxiv.org/abs/2609.10529>.

## External formalization boundary

The external repository is Apache-2.0 and pins `leanprover/lean4:v4.33.1`. BanditRLlib currently pins `leanprover/lean4:v4.29.1`. Therefore:

- do **not** label the external declarations as locally compiled;
- do **not** vendor the source tree without a toolchain/dependency review;
- retain license, repository, commit and source-level attribution if any code is later copied/ported;
- the current integration is metadata + an external graph slice only.

The external `formalization.yaml` reports `sorry_count: 0` for the main results and names the standard axioms `propext`, `Classical.choice`, and `Quot.sound`.

## External declarations to map

- `GapEntropy.benchmark`
- `GapEntropy.Instance.gapEntropy`
- `GapEntropy.gapEntropyConjecture`
- `GapEntropy.universalEntropyUpperBound`
- `GapEntropy.almostInstanceWiseOptimality`
- `GapEntropy.positiveSourceAlmostInstanceWiseOptimality`
- `GapEntropy.PolicyRepresentations.standardBenchmark_eq`

## BanditRLlib retrieval targets

Before proving anything, retrieve exact local declarations/types for:

1. finite/adaptive bandit histories and measurable policies;
2. probability kernels and posterior/trajectory laws;
3. stopping-time and unbounded-stopping infrastructure;
4. KL / relative entropy and event-testing inequalities;
5. adaptive change-of-measure / history information identities;
6. Gaussian means, concentration and finite-arm pull-count accounting;
7. the existing `fixed-confidence-best-arm-identification` BanditRLwiki case and its characteristic-time source map.

Every edge from a local node to an external node must be classified as one of:

- `exact-reuse` — same theorem/type after imports;
- `adapter-needed` — same mathematics, interface mismatch;
- `conceptual-overlap` — related proof technology only;
- `new-leaf` — genuinely absent local prerequisite;
- `new-hub` — new reusable abstraction organizing multiple downstream results.

## Expected graph delta

The candidate non-leaf contribution is the chain

`gap groups → normalized inverse-gap² mass → gap entropy → order-oblivious benchmark → universal algorithm`.

A second candidate hub is policy representation: arbitrary standard-Borel private randomness versus the Gaussian-tape policy class used in the formalization. These should be tested as reusable abstractions rather than buried inside one theorem port.

## Acceptance gate

1. Freeze external commit SHA, license and toolchain.
2. Produce exact declaration-to-declaration retrieval table against BanditRLlib.
3. Decide port strategy: local re-proof, compatible dependency/toolchain upgrade, or permanently versioned external certificate.
4. If local port is chosen: root import, focused canary, axiom audit and full repository gate must pass on one local toolchain.
5. Update BanditRLwiki case and graph only after the verification boundary is explicit.
6. Publish a graph-delta report classifying each added node/edge as leaf, bridge, shortcut, hub or re-organization candidate.

## Current published bridge artifacts

- `website/public-repo/banditrlwiki/frontier-problems/gap-entropy/index.html`
- `website/public-repo/lean-graph/external/gap-entropy/index.html`
- `website/public-repo/lean-graph/external/gap-entropy/gap-entropy.json`
- `website/public-repo/data/frontier-problems.json`
