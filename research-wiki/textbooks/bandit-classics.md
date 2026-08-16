# Bandit Textbook And Survey Cards

ABRL uses textbook cards to decide which proof tree to reproduce next.  These
are source-routing cards, not local proof certificates.

## Core Sources

| Card | Source | Why it matters for ABRL | First proof roots |
| --- | --- | --- | --- |
| `TXT-BUBECK-CESABIANCHI-2012` | [Bubeck and Cesa-Bianchi, 2012](https://arxiv.org/abs/1204.5721) | Standard survey for stochastic and adversarial regret, including finite-arm upper/lower-bound routes. | finite stochastic regret, UCB, EXP3, lower bounds |
| `TXT-LATTIMORE-SZEPESVARI-2020` | [Lattimore and Szepesvári, 2020](https://tor-lattimore.com/downloads/book/book.pdf) | Main textbook spine for concentration, finite stochastic bandits, adversarial bandits, lower bounds, contextual and linear bandits. | ETC, UCB, MOSS, KL-UCB, EXP3, LinUCB/OFUL |
| `TXT-SLIVKINS-2019-2024` | [Slivkins, 2019](https://arxiv.org/abs/1904.07272) | Broad teaching-oriented tree covering IID rewards, Bayesian priors, Lipschitz/contextual/adversarial bandits, knapsacks, and agents. | Bayesian regret, similarity bandits, BwK, incentive-compatible exploration |

## Lattimore--Szepesvári Part IV Source Theorem Cards

Canonical edition for these cards: Tor Lattimore and Csaba Szepesvári,
*Bandit Algorithms*, Cambridge University Press, 2020,
[DOI 10.1017/9781108571401](https://doi.org/10.1017/9781108571401),
[official author PDF](https://tor-lattimore.com/downloads/book/book.pdf). Printed
and PDF page numbers are recorded separately because the front matter shifts
the PDF counter. These are source-routing cards, never local proof evidence.

| Card | Exact source window | Conservative target | Local status |
| --- | --- | --- | --- |
| `TXT-LS-2020-CH13-MINIMAL-SOURCE-CHANGE` | Ch. 13, §13.1, printed pp. 181--182 / PDF pp. 190--191 | least-explored alternative-arm averaging; base and one-coordinate-changed regret expressions; the cross-law expectations are only heuristically close in this chapter | compiled semantic, averaging, and quantitative error-bearing algebra leaves; no history-law comparison |
| `TXT-LS-2020-THM-13-1` | Ch. 13, Thm. 13.1, printed p. 180 / PDF p. 189; proof explicitly deferred to Ch. 15 | for `k>1`, `n>=k`, unit-variance Gaussian arms with mean vector in `[0,1]^k`, a universal positive constant gives minimax regret of order at least `sqrt(k n)` | source-stated / planned; no local declaration is presented as this theorem |

The Chapter 13 conversion window is
[`conversion-windows/TEXTBOOK-PART-IV-CHAPTER-13-BASIC-LOWER-BOUND-SPINE.md`](../../conversion-windows/TEXTBOOK-PART-IV-CHAPTER-13-BASIC-LOWER-BOUND-SPINE.md).
Chapters 14--17 receive their own theorem cards only after their exact source
contracts have been re-read and frozen; the website's future-chapter entries
are navigation-level planned mappings, not frozen theorem statements.

## Paper Bridge Layer

Textbooks provide the main spine; individual algorithm and frontier routes use
paper cards in [`research-wiki/papers/bandit-frontier-cards.md`](../papers/bandit-frontier-cards.md).
The bridge layer currently covers:

- UCB1, EXP3, KL-UCB, Thompson sampling, LinUCB/OFUL, and UCB-VI;
- bandits with knapsacks and resource constraints;
- dueling/preference, safe, private, fair, federated, and neural/federated
  contextual bandits.

Run `python3 tools/bandit.py list-papers` or `python3 tools/bandit.py
search-memory <topic>` before creating a new theorem route.

## Reproduction Order

1. Finite stochastic arms: definitions, pull counts, regret decomposition,
   ETC, UCB, Thompson sampling.
2. Concentration spine: sub-Gaussian MGF contracts, Hoeffding-style tails,
   union bounds, anytime events, summability.
3. Lower-bound spine: change-of-measure, KL for Bernoulli arms, minimax and
   instance-dependent lower bounds.
4. Adversarial finite arms: experts, exponential weights, importance-weighted
   losses, EXP3 regret.
5. Contextual and policy-regret layer: finite policy classes, EXP4-style
   routes, contextual measurability.
6. Linear/structured layer: least squares, confidence ellipsoids, self-normalized
   concentration, OFUL/LinUCB.
7. Modern extensions: pure exploration, nonstationary, combinatorial, resource
   constrained/knapsack, dueling/preference, heavy-tailed/robust, delayed,
   safe/fair/private, federated, and LLM/recommender bandits.

## Textbook Leaf Contract

Every textbook theorem port should create:

- a task packet;
- a conversion window with source theorem/section;
- a proof-obligation row for each leaf;
- Mathlib retrieval card ids for generic leaves;
- LML theorem-card ids when applicable;
- one proof-export target for Markdown and LaTeX after Lean closure.

If a textbook proof repeatedly fails in Lean, treat the failure as a signal to
audit the statement or hidden hypotheses before changing the proof route.
