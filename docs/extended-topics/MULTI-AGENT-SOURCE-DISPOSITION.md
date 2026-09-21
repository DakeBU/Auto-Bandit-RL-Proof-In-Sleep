# Multi-agent source selection and recent-proof disposition

2026-09-20. Independent disposition and witness reviews accepted the bounded
scope; bindings are in `multi-agent-source-disposition-review.json` under
`runs/extended-topics-20260920/`. This is a source-selection audit for the
frozen static Musical Chairs contract. It does
not certify an entire literature, replace the selected algorithm, or close the
all-topic evaluation obligation.

## Selected line and current evidence

The selected source remains Rosenski, Shamir and Szlak, ICML 2016, static
Algorithms 1/2 and supplement A.1. The explicit all-player exploration-budget
repair, total local unknown-population policy, arbitrary independent stationary
bounded reward laws, collision bit, actual learned continuation, and complete
expected pseudo/visible regret chain have local production acceptance at code
commit `3d0265b41717401463ca35b832a87906c17b80e2`. See
`runs/extended-topics-20260920/multi-agent-learner-validation.json` for the
separate semantic, Lean, axiom, harness and publication evidence. Current
integration metadata is committed at `4a09e817cabd67f4ffc3b248ff1487ae55f6dea3`.

The contract's original freeze-time status paragraphs are historical. This
disposition does not change its mathematical scope. In particular the public
endpoint preserves the failure residual and does not claim individual fairness,
adversarial robustness, delayed observations, or asynchronous participation.

## Recent comparison and pinned reading scope

The selected comparison is Zhou, Wang, Yang and Gao, *Distributed Algorithms
for Multi-Agent Multi-Armed Bandits with Collision*,
[arXiv:2510.06683v1](https://arxiv.org/abs/2510.06683v1), submitted 2025-10-08.
The inspected 21-page [PDF](https://arxiv.org/pdf/2510.06683v1) has SHA256
`52dc365e688f7dcc8a3ff3f1759936d7f87112090223ef300cf133aefb594423`.
Its AAAI-style 2026 footer is not treated as publisher verification or evidence
that a later proceedings version agrees with this preprint.

The relevant full-proof scope is the synchronous SynCD line: model and metrics
on physical pp2-3, Algorithm 1 and estimator/decision rules on p4, communication
and Theorem 1 on p5, initialization and communication details on pp7-9, and all
of Section 8.4 on pp10-14, including Lemmas 4-9 and their supplied proofs.
Formula pages 4, 9, 11 and 14 were rendered to resolve extraction ambiguity.
The periodic-asynchronous model and Theorems 2/3 are a separate disposition;
they are not prerequisites imported into the frozen synchronous learner.

Both models use homogeneous bounded stochastic rewards, simultaneous pulls,
and a separately observable collision indicator. SynCD adds collision-encoded
communication, adaptive successive elimination and balanced exploitation. Its
individual metric compares each player's expected reward with the average of
the best M means; the current Musical Chairs theorem bounds their aggregate
regret. A total-regret bound alone does not establish the individual metric.
SynCD assumes strict ordering of all means in its presentation, whereas the
frozen learner permits ties inside the top set and requires a boundary gap.

## Algorithm-to-proof findings

These are claim-specific findings about the pinned text. They distinguish
literal pseudocode, potential intended repairs, and missing justification.
They are not a counterexample to every possible corrected SynCD implementation.

1. **Exploration schedule and actual counts.** In Algorithm 1 line 13 the
   exploratory arm expression omits the outer `cycle` variable. With M=2,
   K=3, no accepted arms and ranks 0/1, an uninterrupted six-pull evaluation
   of that expression gives `(0,2),(1,0)` repeated three times. The per-player arm counts are
   `(3,3,0)` and `(3,0,3)`. These pulls are collision-free, but are not uniform
   over all active arms for each player. This holds the arm sets fixed and
   does not assert a reachable full trace: communication/state updates can
   interrupt the block. Thus the printed scheduling expression does not
   supply the balanced sampling used by Lemmas 5/6. The count increments in
   lines 19/20 also need reconciliation with actual observations. Adding a
   cycle offset and choosing a consistent phase-level update would be a
   changed algorithm requiring its own invariants and performance proof.

2. **Communication threshold convention.** Algorithm 1 takes beta>1 and
   tests `ECR_t <= beta * ECR_last`. For positive nonincreasing radii this
   condition already holds without a factor-beta decrease. Lemma 7 uses
   geometric shrinkage with logarithms to base beta, while Lemma 9 switches
   to beta in (0,1). For beta=2, old radius=1/2 and new radius=2/5, the printed
   test passes and the reciprocal-shrink test fails. One coherent convention
   is needed throughout, including its changed constants and first-message
   threshold; silently swapping conventions is not source-faithful reuse.

3. **Send/receive compatibility.** Algorithms 5/6 place data-bearing
   collisions on even slots but let the receiver terminate on an even-slot
   collision. With the favorable convention that both parties agree on the
   receiver arm and a sufficiently long receive loop, a three-bit protocol
   input beginning with 1 makes the receiver stop at slot 2, before the sender's
   designated terminal slot 6. This does not prove that the actual quantizer
   produces that input from an admissible reward history. The indexing of
   sender/receiver ranks, sign bit and binary-versus-decimal normalization also
   needs a precise convention. A reliable code is plausible, but correctness
   of the displayed protocol is not supplied by a bound on message length.

4. **Confidence and probability scope.** Lemma 4 invokes Hoeffding on
   aggregated observations and an old quantized estimate, then applies a
   no-communication radius comparison. Acceptance needs actual independent
   sample producers, a valid threshold convention, quantization error at the
   timestamp at which the stored mean was encoded, and a union or stopping
   argument covering the random times used by elimination. A single fixed-time
   confidence assertion cannot alone justify simultaneous adaptive decisions.
   The paper's deterministic expected regret notation is also mixed with
   high-probability bounds in Lemmas 5/6. Failure-event costs must be included
   explicitly when concluding Theorem 1's expectation.

5. **Elimination and telescoping constants.** Lemma 5's displayed statement
   has unsquared gap denominators (and an optimal-arm denominator vanishing
   at k=M), whereas its proof obtains squared denominators and the M+1
   boundary for accepted arms. Lemma 6's telescoping step requires control of
   `(T_p-MK)/(T_(p-1)-MK)` and positivity of both shifted counts. An unshifted
   ratio bound is insufficient: beta=2, counts 12 and 48, and MK=6 give the
   unshifted ratio 4 but shifted ratio 7. This is an obstruction to that
   inference, not proof these counts occur in a repaired learner. The first
   phase and batch overshoot need separate bounds. Substitution of
   `delta=1/T^2` also doubles `log(delta^-1)` relative to `log T`; the final
   constants require an explicit reconciliation.

6. **Message-length calculation.** Lemma 8's own bound retains beta inside
   its square-root term; the subsequent total-cost expression drops it.
   Its fixed-prefix concentration must also be justified at the actual
   communication times. Lemma 9's threshold inequality yields a lower sample
   count, not by itself the displayed upper count. A first-crossing argument
   plus an explicit bound on the check interval could produce an upper count,
   but neither follows merely by rearranging the displayed inequality.
   With `log(delta^-1)=2`, beta=1/2, count=100 and MK=6, the threshold holds
   while the displayed upper quantity is 10. This witness deliberately does
   not assume first crossing.

7. **Initialization and fairness.** Section 8.1 cites an almost-sure
   completion initializer with finite expected duration. Section 8.4 also
   uses deterministic `T_init=T0+2K`, `T0=ceil(K log T)`, and an initialization
   failure probability. These are different contracts. Likewise, uniform
   exploitation over completed cycles does not by itself prove the stated
   individual bound at arbitrary finite horizons, across initialization,
   communication, local elimination and incomplete cycles. A valid symmetric
   construction may provide such a result, but that identity must be proved
   for the actual policy.

The exact finite diagnostics are executable as
`python runs/extended-topics-20260920/check_syncd_source_witnesses.py`.
They check printed subclaims; they are neither simulation evidence nor new
Lean theorems or a disproof of a fully repaired regret theorem.

## Initialization dependency resolved at its actual scope

The cited source is Wang, Proutiere, Ariu, Jedra and Russo,
[AISTATS 2020](https://proceedings.mlr.press/v108/wang20m.html).
The main PDF SHA256 is
`96d8729db0d8616a25c7b651f160358ad78405b20e7ebd45ec97b2d78b7d8b4b`;
the 22-page supplementary artifact SHA256 is
`be24856f4b59112d5fc9de0ee3c40f1e4462e8f7e7b4d15724c2a69626a68c8c`.
Read main pp3-4 and supplement Appendix A pp10-11, including complete
orthogonalization and pairwise-rank proofs.

Appendix A uses fresh uniform draws on the K-1 ordinary arms, reserving arm K
for signalling. Given other players' choices, an unsatisfied player has at
least K-M free labels. Conditional success is therefore at least
`q=(K-M)/(K-1)`. Persistence and a union bound give
`P(some player unfinished after b blocks) <= M(1-q)^b`; summing tails and
multiplying by block length K+1 yields `M(K-1)(K+1)/(K-M)`. This argument uses
conditional fresh draws, not independence of players' waiting times.
The main text's use of zero in the arm-choice set must be distinguished from
the unsatisfied-state sentinel; the Appendix's K-1-arm convention is explicit.

For ranks k<j, the deterministic schedule makes the pair collide exactly at
slot k+j, on arm j. It lies after 2k and no later than 2j, so collisions in the
first 2k slots count lower ranks. Counting all pairwise collisions also reveals
the population. Thus `INITPHASE(M,K)` notation alone is not evidence that an
intended SynCD implementation necessarily requires population as prior input.
The source genuinely provides a way to learn it, but its random-duration
contract must be connected to the downstream algorithm consistently. No full
DPE1 regret theorem or external KL-UCB analysis is imported here.

## Candidate inventory and selection decision

The following additional comparisons were screened at primary publisher
metadata/abstract level only; their complete proofs are not accepted inputs.

| Primary record | Relevant change from the frozen model | Disposition |
|---|---|---|
| [Pacchiano, Bartlett and Jordan, ALT 2023](https://proceedings.mlr.press/v201/pacchiano23a.html) | Cooperation with unknown collision reward and implicit information sharing | Background; full 50-page proof not audited |
| [Mahesh et al., AAMAS 2024](https://aamas.csc.liv.ac.uk/Proceedings/aamas2024/pdfs/p1337.pdf) | Malicious players and robustness to deliberate collisions | Model/abstract screening only; cooperative-source proof does not imply adversarial robustness |
| [Fan et al., IJCAI 2025](https://www.ijcai.org/proceedings/2025/564) | Delayed reward/feedback synchronization | Background; immediate-feedback law cannot supply its delayed-history premise |
| [Wang, Zhang and Li, ICML 2025](https://proceedings.mlr.press/v267/wang25eo.html) | Heterogeneous means and max-min matching objective | Different reward and comparator contracts; not transferred |

The accepted bounded disposition is to retain the repaired 2016 static
unknown-population learner and record SynCD v1 as a relevant but unaccepted
algorithm/performance chain. Reading its complete relevant proof does not
oblige importing unsupported premises. The concrete diagnostics above narrow
the reasons for non-transfer. An independently reviewed correction of SynCD
would be a separate research line, not an implicit extension of this contract.
No comparative optimality, runtime improvement, experimental replication,
whole-topic completion or main/live publication follows from this audit.
