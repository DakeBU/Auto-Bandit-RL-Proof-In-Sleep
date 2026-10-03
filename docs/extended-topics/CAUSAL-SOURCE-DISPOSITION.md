# Causal source selection and dependency disposition, 2026-09-20

This record distinguishes acceptance of the frozen representative line from
screening later work. It does not certify every theorem in every candidate
paper or broaden the formalized information model.

## Selected classic line

The official NIPS 2016 main paper and supplement remain the source for the
known-parent-law Algorithm 2 and fixed-budget expected simple regret, uniform
allocation, attained optimal design, and parallel allocation bridge. Exact
version hashes are in `causal-source-hashes.json`. The actual law,
concentration, recommendation, finite-type transport, allocation and local
canary obligations now have bounded independent reviews and combined
validation in the four sampling, heterogeneous, noisy-diagnostics and parallel
packets under `runs/extended-topics-20260919/`.

The source repairs are visible: two confidence terms plus one bias give the
conservative coefficient; the confidence failure direction is corrected;
strict rarity and observation mass `1-D` normalize the parallel design.
This certifies the repaired frozen line under its stated assumptions. It
does not certify the separate unknown-marginal Algorithm 1, a lower-bound
comparison with noncausal methods, or all experiments in the 2016 paper.

## Recent full-proof comparison and external dependency

The comparison is [Shahverdikondori, Etesami and Kiyavash, AISTATS 2026](https://proceedings.mlr.press/v300/shahverdikondori26a.html).
Its pinned 33-page artifact includes appendices beyond the proceedings page
range. It studies unknown graphs/parent identity and expected cumulative
pseudo-regret, with reward means in `[0,1]` and centered sub-Gaussian rewards.
It does not assume the known parent-intervention laws required by the frozen
2016 learner. Thus it is relevant context and is not imported into that chain.

The independent review reads the model, Algorithm 1, Theorem 4.4, Eq.8,
Lemmas 2.1/9.7 and their entire supplied proofs, plus the other main theorem
proofs for a claim-specific disposition. Its external UCB reference is resolved
to the authors' [Bandit Algorithms online edition](https://tor-lattimore.com/downloads/book/book.pdf),
Algorithm 3 and Theorems 7.1–7.2, including the sub-Gaussian tail prerequisites.
The inspected book hash and exact reading/rendering scope are bound by the
review receipt. Reading a proof is distinct from accepting every step.

For the known-parent-count route, the printed optimal-arm fraction is a lower
bound, not necessarily the exact fraction. The printed sample count is also
noninteger and becomes zero at horizon one. An explicit finite interpretation
uses a nonempty integer subset, capped by the full action count, sampled
independently before reward feedback. UCB is applied conditionally on this
entire subset. A gap bound on means controls missed-optimum regret; bounded
reward realizations are unnecessary. This yields a corrected mathematical
comparison, not an additional Lean result.

The mixture lemma's assertion that centered residuals are independent of
selected component means is false in general. Conditioning on the mixture
component, applying its centered MGF bound, and then the bounded-mean
Hoeffding bound gives the claimed variance proxy without that assertion.
For adaptive mixture arms, this argument requires conditioning on the history
that fixes the weights and drawing fresh component rewards.

The lower-bound chains have unresolved exact-parent, admissible-gap,
finite-horizon and counting qualifications. The unknown-parent-count upper
chain also needs phase rounding and truncation, history-conditioned mixture
sampling, and the approximation-regret term omitted from its recycled-mixture
equality. Its Pareto consequence depends on unaccepted chains. These results
are not transferred or certified. A flaw in a displayed proof step is not a
counterexample to its final asymptotic theorem. Experimental claims have not
been validated.

## Candidate inventory and accepted scope

`CAUSAL-LITERATURE-SCREEN.md` records the broader publisher-level screen:
Yabe 2018, Lu 2020, Maiti 2022, Sawarni 2023, Liu 2024, Jamshidi 2024 and
Konobeev 2025 are metadata/abstract comparisons, not accepted proof inputs.
They introduce different propagation, confounding, graph knowledge,
adaptivity or budget settings. None supplies a missing premise to the frozen
algorithm. Additional unopened search leads remain leads. The full recent
comparison above is the selected source-selection obligation; an exhaustive
proof audit of the whole causal-bandit literature is not claimed.

The outcome is a bounded selection decision: retain the repaired 2016
algorithm-to-simple-regret line and record the inspected 2026 comparison as
not transferred. The classic source-facing endpoints and recent comparison
are assessed separately. Final review hashes and the finite-repair check
are recorded in `causal-source-disposition-review.json` once complete.
Whole-topic acceptance, controlled all-topic evaluation and manuscript
integration remain separate requirements.
