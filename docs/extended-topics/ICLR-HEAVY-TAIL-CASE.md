# Heavy-tailed development case: Evaluation and appendix draft

Working insertion draft for the ICLR evidence package. This is one descriptive case in the mandatory ten-topic program, not the completed all-topic Evaluation. No canonical manuscript or anonymous submission snapshot is changed. The frozen development protocol precedes these results; its disabled controlled design remains unexecuted. Artifact links below support review and are not an anonymized submission package.

## Evaluation insertion

### Extending the library through an actual algorithm

We evaluated the development of a heavy-tailed bandit guarantee in the shared Lean library. The target has a finite nonempty arm set and stationary independent arm streams, with known $u>0$ satisfying $\mathbb E|X_a|^{1+\epsilon}\le u$ for each arm, where $0<\epsilon\le1$. The policy chooses from the observed history and consumes the next unused reward from its chosen arm. Its truncated estimator depends on both the sample index and the decision round. Preserving these two indices is essential: the adaptive observations cannot be substituted for an independent fixed sample.

The resulting proof connects raw moment assumptions to expected finite-horizon pseudo-regret for the actual policy. It derives the bias and truncated second moment, signed concentration, confidence at the random pull count, selection and count bounds, and the final expectation. Confidence and count estimates are proved within the chain rather than supplied as assumptions of the endpoint. Independent reconstruction, source comparison and separate repair review distinguish the original estimator and radius-four policy from the corrected regret coefficient.

The source audit also produced a finite mathematical obstruction. For two deterministic arms with rewards $0$ and $-1$, $\epsilon=u=1$, and $T=2^{50}$, the implemented permissible deterministic tie rule incurs expected pseudo-regret exceeding the printed coefficient's bound $32\log T+5$. The Lean certificate includes the raw second-moment assumptions, the actual policy's pull count and its connection to expectation under the product reward law. It establishes a failure of that literal coefficient for an admissible instance. The logarithmic regret rate and other estimators in the source are not rejected by this certificate.

### Reuse and transfer

The development reused existing concentration and reward-process interfaces while adding the mathematics specific to moment-controlled truncation and adaptive sampling. At the historical source-confidence snapshot, compiled proof terms contain 19 direct references to 15 distinct project targets. These are source–target reference pairs, not independent measurements of effort saved. Git object comparison separates two unchanged modules already present in the original frozen library from three heavy-tail modules introduced during development. This separation prevents later within-case reuse from being counted as initial-library support.

A transfer target, reserved before its implementation, replaces hard truncation by clipping and adds a pathwise corruption budget on the consumed prefix. The resulting estimator guarantee permits an outcome-dependent positive count and enlarges the confidence radius by $C/N$. Its proof combines the moment-based clean estimator analysis with clipping's perturbation bound. A five-module compiled export records 39 focused declarations and 113 project proof-reference pairs, with all referenced boundary nodes retained. This demonstrates concrete integration and use of the developed interfaces. It does not estimate a productivity effect or establish a corruption-robust policy regret theorem.

Validation combines semantic review, axiom inspection, public-root canaries, the shared Lean project and the repository harness. The latest recorded joint gate completed 9,015 root build jobs, 9,112 Tests build jobs and 437 Python tests, with seven skips. These build-job totals include shared dependencies and are not counts of new theorems. Ten reviewed declarations are connected to the common reading registry, with statement and proof-module hashes checked against their acceptance records. The heavy-tailed case remains incomplete at the program level because recent-source audits and the all-topic evidence obligations are still open. Controlled comparisons have not been run, so these observations support a descriptive account of reuse, transfer and source diagnosis, not a causal claim about efficiency.

## Appendix insertion

### Exact performance and failure contracts

For the unchanged source-parameter policy, the accepted corrected endpoint is

$$
\mathbb E[R_T]\le\sum_{a:\Delta_a>0}\Delta_a\bigl(A_a(T)+5\bigr),\qquad
A_a(T)=\frac{2\log(\max\{T,1\})}
{\left(\Delta_a/(8u^{1/(1+\epsilon)})\right)^{(1+\epsilon)/\epsilon}}.
$$

Here the arm set has finite size $K\ge1$, the known moment bound satisfies $u>0$, and $R_T$ is conditional-mean pseudo-regret, the expectation is over the product arm-stream law, and the actions are generated by the formalized causal policy. The theorem covers every natural horizon, including zero. It requires integrability and the bound on each arm's raw absolute $(1+\epsilon)$-moment. It does not assume a confidence event, a count bound or first-moment hypotheses separately: first moments are derived from the raw-moment assumptions. At $\epsilon=1$, the leading term is $128u\log(\max\{T,1\})/\Delta_a$, with additive $5\Delta_a$. This correction remains distinct from the printed coefficient and from the separately retained conservative policy adaptation.

The finite obstruction specializes to $u=1$, unit gap and $T=2^{50}$. A symbolic count argument proves more than $32\log T+5$ pulls of the inferior arm. It does not simulate $2^{50}$ rounds. Dirac reward laws make the stream deterministic almost surely; the proof then transfers the count to expected pseudo-regret and negates the literal positive-gap source sum. The certificate uses the implemented deterministic tie convention. No theorem for every randomized tie convention is claimed.

### Transfer contract and canary scope

The clipping endpoint bounds the outer measure of the bad event at an arbitrary outcome-dependent count $0<N\le t$. Its clean coordinates are independent, have a common mean and satisfy the stated raw-moment bound. On the consumed prefix, arbitrary corruption with total absolute magnitude at most $C$ changes the clipped mean by at most $C/N$. The confidence calculation and the perturbation calculation concern the same action trace; comparing two policies that react differently to corruption would require additional reasoning.

The larger canary uses nonconstant rewards and chooses $N\in\{9999,10000\}$ from the first reward, with a nonzero corruption budget. The accompanying numerical threshold diagnostic is not an empirical coverage experiment. Small canaries can instantiate a true theorem while their bad event is empty; those instances are recorded as contract-assembly checks, not evidence of sharpness. No bound on the regret of an adversarially corrupted policy follows merely from the estimator transfer.

### Snapshot and extraction semantics

| Evidence | Frozen snapshot | What it establishes |
|---|---|---|
| Source-confidence reuse | `abf4d27`, compared with `4b2efd8` | 19 direct project proof-reference pairs to 15 distinct targets at this historical stage |
| Original library | `eedcda1` | Two of the five compared modules have identical Git blobs here; the other three files are absent at this base |
| Clipping direct export | `e3a507c` | Five-module direct graph: 39 focused nodes, 655 boundary nodes, 2,968 edges, 113 project proof-reference pairs |
| Corrected actual-policy regret | `bea700c` | Full moment-to-expected-pseudo-regret endpoint with an explicit source correction |
| Finite printed-coefficient obstruction | `597ffe4` | Admissible finite actual-policy counterexample and expectation connection |
| Shared mapping validation | gate code `2afda62`; site `c9d1c49` | Combined gates and ten canonical reading references; no new proof declarations |

The confidence snapshot predates the later sharp producer. Its counts must not be relabeled as counts for the latest regret proof. The clipping export includes direct type and value references, with proof references selected by `kind=value` or `also_in_value=true`. A type-precedence record that also occurs in a proof is retained as proof evidence. Graph edges do not count uses at individual syntax locations, independent trials, transitive dependencies or units of researcher effort. The graph's 2,968 edges and 113 project proof-reference pairs are different quantities and have different scopes.

The two initial-base modules are `ConcentrationFixedMGF.lean` and `Exp3ComparatorBernstein.lean`. They supply the fixed-tilt MGF interface and elementary exponential control used by the confidence development. `HeavyTailTuning.lean`, `HeavyTailTruncation.lean` and `HeavyTailFixedTilt.lean` belong to later development. Their reuse within the case is real but does not demonstrate availability in the original frozen library.

### Failure, review and experimental boundaries

The artifact retains the literal source discrepancy, the corrected guarantee and the finite obstruction as separate objects. Source-facing endpoints have independent reconstruction and source/repair reviews; compilation alone does not establish attribution. Audited endpoint axiom closures use `propext`, `Classical.choice` and `Quot.sound`. No benchmark success rate is computed from the development history or from build jobs.

The ten-topic controlled protocol has not been frozen or executed. The earlier two-target protocol remains disabled. The current developer has seen the targets and solutions, so these development episodes cannot serve as fresh independent repeats. A future comparison must use isolated fresh runs, equal model/budget/tool access, audited import closure, exact-contract semantic scoring and inclusion of every failure and timeout. All-topic manuscript conclusions and controlled results remain pending.

## Maintainer evidence and reproduction

- [Deterministic evidence summary](../../runs/extended-topics-20260919/heavy-tail-case-evidence.json), regenerated with `python runs/extended-topics-20260919/summarize_heavy_tail_case.py`. It checks historical Git blobs and derives counts from receipts; it does not rerun Lean or an experiment.
- [Source-confidence compiled references](../../runs/extended-topics-20260919/source-confidence-reuse.json).
- [Clipping compiled references and exporter command](../../runs/extended-topics-20260919/clipping-reuse.json).
- [Corrected regret acceptance](../../runs/extended-topics-20260919/source-regret-validation.json).
- [Finite obstruction acceptance](../../runs/extended-topics-20260919/counterexample-validation.json).
- [Shared mapping and latest joint gates](../../runs/extended-topics-20260919/heavy-tail-mapping-validation.json).
- Primary-source anchors and the remaining source audit are maintained in [SOURCE-AUDIT.md](SOURCE-AUDIT.md), [SOURCE-REGRET-DERIVATION.md](SOURCE-REGRET-DERIVATION.md) and [PRINTED-REGRET-COUNTEREXAMPLE.md](PRINTED-REGRET-COUNTEREXAMPLE.md).

This draft is not a submission-ready anonymous artifact. Bind citations to the manuscript's actual bibliography when inserting it; no unverified BibTeX key is introduced here.
