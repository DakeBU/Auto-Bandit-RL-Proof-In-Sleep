# Bandit Textbook And Survey Cards

ABRL uses textbook cards to decide which proof tree to reproduce next.  These
are source-routing cards, not local proof certificates.

## Core Sources

| Card | Source | Why it matters for ABRL | First proof roots |
| --- | --- | --- | --- |
| `TXT-BUBECK-CESABIANCHI-2012` | [Bubeck and Cesa-Bianchi, 2012](https://arxiv.org/abs/1204.5721) | Standard survey for stochastic and adversarial regret, including finite-arm upper/lower-bound routes. | finite stochastic regret, UCB, EXP3, lower bounds |
| `TXT-LATTIMORE-SZEPESVARI-2020` | [Lattimore and Szepesvári, 2020](https://tor-lattimore.com/downloads/book/book.pdf) | Main textbook spine for concentration, finite stochastic bandits, adversarial bandits, lower bounds, contextual and linear bandits. | ETC, UCB, MOSS, KL-UCB, EXP3, LinUCB/OFUL |
| `TXT-SLIVKINS-2019-2024` | [Slivkins, 2019](https://arxiv.org/abs/1904.07272) | Broad teaching-oriented tree covering IID rewards, Bayesian priors, Lipschitz/contextual/adversarial bandits, knapsacks, and agents. | Bayesian regret, similarity bandits, BwK, incentive-compatible exploration |

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
