# Causal source audit, 2026-09-18

Current update (2026-09-20): the bounded source-selection obligation is now accepted in CAUSAL-SOURCE-DISPOSITION.md and runs/extended-topics-20260919/causal-source-disposition-review.json. The selected recent proof comparison and exact external UCB dependency have independent review, with separate mathematical-repair acceptance. Other candidates remain metadata-only; unaccepted lower bounds, unknown-k/Pareto chains and experiments are not transferred. The paragraphs below retain the dated 2026-09-18 inspection snapshot; their pending implementation/review statements are historical. Current production evidence is in the sampling, heterogeneous, noisy-diagnostics and parallel review/validation packets. Whole-topic and all-topic evaluation acceptance remain open.


Status: selected classic model, Algorithm 2, Theorem 3 proof and allocation
bridge inspected; recent comparison partially inspected. Full classic/recent
audit obligation remains open. No independent review is recorded.

## Primary source versions

- [Official NIPS 2016 main paper](https://proceedings.neurips.cc/paper_files/paper/2016/file/b4288d9c0ec0a1841b3b3728321e7088-Paper.pdf):
  9 pages, SHA256 `99aa9427e02e31883510dfcd0b11ba4f45097dc30dd98a094cbf13068f93b747`.
  Algorithm 2 and model are on p.5; Theorem 3 and Proposition 4 on p.6.
- [Official supplemental ZIP](https://proceedings.neurips.cc/paper_files/paper/2016/file/b4288d9c0ec0a1841b3b3728321e7088-Supplemental.zip):
  entry `paper-with-proofs.pdf`, 15 pages, extracted PDF SHA256
  `f943218e350729efe12c811abe36462f0b0afc1290b52f161e23b049a329d58f`.
  Section 10 on p.14 proves Theorem 3; p.15 contains Proposition 8.
- [ArXiv v1](https://arxiv.org/pdf/1606.03203v1): 14 pages, SHA256
  `0daf7d81af38ba63fb5107b04b248a35b120cf46bb85cb612825bc8821c9b599`.
  Its parallel bridge is numbered Proposition 9. The supplement is the
  primary proof locator; these version numbers must not be mixed.

PDFs were extracted as text; main p.6 and supplement pp.14–15 were also
rendered and visually inspected. Private source copies stay outside the public
repository. Machine-readable hashes identify them without local private paths.

## Source repairs and clarifications

| Location | Finding | Formalization treatment |
| --- | --- | --- |
| Supplement p.14, final comparison | The written loss has two epsilon terms and one bias, but the printed coefficient accounts for only one epsilon. | The written inequalities give 2 sqrt(2)+7. Preserve the asymptotic Theorem 3 rate and disclose this conservative repair. No claim that a sharper proof is impossible. |
| Supplement p.14, final probability display | The displayed good-event probability is bounded above by 1/T. | Prove bad-event probability <=1/T, equivalently good-event probability >=1-1/T, before integration. |
| Supplement p.15, allocation | Rare-action mass D plus the printed empty mass 1/2+(1-D) totals 3/2. The later denominator also uses a different expression. | Empty mass 1-D normalizes the vector and remains >=1/2, sufficient for the intended bound. |
| Mixture likelihood ratio | Ratios on unsupported states need a convention and a coverage domain. | Require Q positive on the union of action supports; define ratio zero only outside that union. Full-support eta is sufficient but is not imposed as necessary. |

These are findings about the displayed derivations. They do not establish that
the asymptotic theorem is false. The general-graph algorithm assumes known
reward-parent intervention distributions, not merely known graph topology.

## Recent source boundary

[Graph Learning is Suboptimal in Causal Bandits](https://proceedings.mlr.press/v300/shahverdikondori26a.html),
Shahverdikondori, Etesami and Kiyavash, AISTATS 2026, PMLR 300:3088–3096,
was downloaded from the PMLR linked repository. Abstract, related work and
model sections were read. Its unknown graph, bounded intervention size and
cumulative regret setting differs from the frozen 2016 known-parent-law
simple regret setting. A subsequent targeted upper-bound proof inspection is recorded below;
other theorem proofs and the external UCB dependency remain unaudited. No
constants, optimality claims or experimental results from it enter the
contract. The broader screen is recorded separately.

## New derivation versus proof status

The contract's three-node canary and compact-sublevel optimizer route are
local constructions. They are not attributed to the source. The former has
exact arithmetic checks; the latter remains a proposed proof route. Neither
has been compiled in Lean. No source correction is hidden in a theorem name.

## Additional recent-proof inspection

Subsequently read 2026 Algorithm 1, Theorem 4.4 and its complete printed proof,
the optimal-arm fraction calculation (8), Lemma 9.7 and its proof, and
Lemma 2.1 including both intervention-size cases. Also inspected Lemma 9.6;
PDF page 15 was rendered to verify the mixture and sampling formulas.
This is a targeted upper-bound dependency inspection, not a complete audit
of the paper's lower bounds, unknown-parent-size results or external UCB proof.

Qualifications before any formal reuse:

- The displayed optimal-arm fraction is a guaranteed lower bound, not generally
  the exact fraction: multiple maximizing parent assignments can add arms.
- A real-valued sample count needs ceiling and a nonempty small-horizon rule;
  the written log(sqrt(T)) is zero at T=1. The finite-set implementation must
  handle its cardinality cap and not ask UCB to select from an empty subset.
- Lemma 9.6 asserts independence of the centered residual and selected mean.
  Componentwise sub-Gaussian bounds do not supply that independence. Its
  variance-proxy conclusion instead follows by conditioning on the selected
  component, applying its centered MGF bound, then Hoeffding to the bounded
  component mean. This repairs the argument without refuting the result.
- Theorem 4.4 should condition on the sampled arm subset before invoking UCB,
  then average over subsets; subset sampling must be independent of subsequent
  rewards. Its external UCB guarantee is not itself reconstructed here.

These findings reinforce the frozen line's requirements for actual sampling,
nonempty action sets and derived probability identities. They do not transfer
the 2026 cumulative-regret theorem into the 2016 simple-regret contract.


## Receipt hash portability (2026-09-21)

The append-only normalization record is
`runs/extended-topics-20260921/topic-receipt-hash-normalization.json`.
PR #131 integrated its portable module/receipt validation into main without
changing Lean proofs, historical receipt bytes, semantic verdicts or topic
completion. Main/Pages acceptance is recorded in `ALL-TOPICS-LEDGER.json`
under `merged_baseline`; local mixed-ending validation is separately recorded
in `runs/extended-topics-20260921/receipt-portability-local-validation.json`.
