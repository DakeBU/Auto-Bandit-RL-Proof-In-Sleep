# Causal source audit, 2026-09-18

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
simple regret setting. Its full theorem proofs have **not** been audited;
no constants, optimality claims or experimental results from it enter the
contract. Complete a relevant recent-proof audit before closing the source
obligation. The broader screen is recorded separately.

## New derivation versus proof status

The contract's three-node canary and compact-sublevel optimizer route are
local constructions. They are not attributed to the source. The former has
exact arithmetic checks; the latter remains a proposed proof route. Neither
has been compiled in Lean. No source correction is hidden in a theorem name.
