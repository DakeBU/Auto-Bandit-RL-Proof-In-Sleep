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
| `TXT-LS-2020-DEF-13-MINIMAX-OPTIMAL` | Ch. 13 opening, author-online p. 180 / physical PDF p. 189 | worst-case and minimax regret over an environment/policy class; minimax optimality is attainment for a policy together with its environment class and horizon | compiled as `worstCaseExpectedRegret`, `minimaxExpectedRegret`, and `IsMinimaxOptimal`; no general attainment existence is claimed |
| `TXT-LS-2020-EQ-13-1-GAUSSIAN-TESTING` | Ch. 13, §13.1, Eq. (13.1), author-online p. 181 / physical PDF p. 190; analytic source Eq. (13.4), author-online p. 184 / physical PDF p. 193 | the empirical mean of `n>0` iid `N(mu,1)` observations, midpoint decision for the resulting `N(0,1/n)` versus `N(Delta,1/n)` model, and the exact printed two-sided Mills-ratio error bounds | the canonical finite-iid empirical-mean law, midpoint error events, and honest maximum-risk Chernoff companion `exp(-n*Delta^2/8)` compile; both exact Eq. (13.4) integral bounds and the printed Eq. (13.1) now compile via `gaussianMills_lower_integral`, `gaussianMills_upper_integral`, and `gaussianSampleMeanZeroErrorProbability_source_bounds` |
| `TXT-LS-2020-CH13-MINIMAL-SOURCE-CHANGE` | Ch. 13, §13.1 (CUP starts p. 155), author-online pp. 181--182 / physical PDF pp. 190--191 | least-explored alternative-arm averaging; base and one-coordinate-changed regret expressions; the cross-law expectations are only heuristically close in this chapter | compiled semantic, averaging, and quantitative error-bearing algebra leaves; no history-law comparison |
| `TXT-LS-2020-THM-13-1` | Ch. 13, Thm. 13.1, CUP print p. 155 / author-online p. 180 / physical PDF p. 189; proof explicitly deferred to Ch. 15 | for `k>1`, `n>=k`, unit-variance Gaussian arms with mean vector in `[0,1]^k`, a universal positive constant gives minimax regret of order at least `sqrt(k n)` | compiled through the Chapter 15 construction as `unitGaussianMinimaxExpectedPseudoRegret_ge_one_div_fiftyFour_sqrt`, with explicit universal constant `1/54` |
| `TXT-LS-2020-CH14-ENTROPY-CODING` | Ch. 14, §14.1, Eqs. (14.1)--(14.3), author-online pp. 186--188 / physical PDF pp. 195--197 | finite binary prefix codes, expected length, base-two/natural entropy, and the Huffman/source-coding bounds | code/entropy definitions, prefix-to-unique-decoding proof, and Kraft adapter compile; Huffman optimality, the one-bit sandwich, and asymptotic source coding remain blocked |
| `TXT-LS-2020-CH14-RELATIVE-ENTROPY` | Ch. 14, §14.2 (CUP starts p. 162), Eqs. (14.4)--(14.6) and Thm. 14.1, author-online pp. 188--190 / physical PDF pp. 197--199 | extended-real `D(P,Q)`; arbitrary finite-alphabet and Bernoulli endpoints; RN/log-likelihood representation on the absolutely-continuous integrable branch; infinity otherwise | compiled project adapters around Mathlib KL, arbitrary finite-alphabet Eq. (14.4) with exact support dichotomy, and Bernoulli endpoints; Eq. (14.5) supremum equivalence compiles; Eq. (14.6) aggregate integration remains pending |
| `TXT-LS-2020-THM-14-2-BRETAGNOLLE-HUBER` | Ch. 14, §14.2 (CUP starts p. 162), Thm. 14.2 / Eq. (14.7), author-online pp. 190--191 / physical PDF pp. 199--200 | for probability laws and measurable `A`, `P(A)+Q(Aᶜ) >= exp(-D(P,Q))/2`, with the right side zero at infinite KL | compiled unconditional measure/event terminal in the exact `P`-to-`Q` direction |
| `TXT-LS-2020-EX14-10-DPI` | Ch. 14, §14.5 (CUP starts p. 167), Ex. 14.10, author-online pp. 195--196 / physical PDF pp. 204--205 | restriction to any sub-sigma-algebra cannot increase relative entropy; the event inequality is its binary specialization | full finite-measure `Measure.trim` theorem compiles as `relativeEntropy_trim_le`; the earlier event specialization remains separately compiled |
| `TXT-LS-2020-LEMMA-15-1-DIVERGENCE-DECOMPOSITION` | Ch. 15, §15.1, Lemma 15.1 / Eq. (15.1), CUP print pp. 170--171 / author-online pp. 198--199 / physical PDF pp. 207--208 | for one common possibly randomized nonanticipating policy, `D(P_nu^pi,P_nu'^pi)=sum_i E_nu^pi[T_i(n)]D(P_i,P_i')` with first-law pulls and KL direction | compiled as `LowerBounds.banditHistoryRelativeEntropy_eq_expectedPulls_sum`; finite arms, countably generated reward space, arbitrary Markov arm laws, and exact realized pull-count lower integrals |
| `TXT-LS-2020-THM-15-2-GAUSSIAN-MINIMAX` | Ch. 15, §15.2, Theorem 15.2, CUP print pp. 171--173 / author-online pp. 199--201 / physical PDF pp. 208--210 | for `k>1`, `n>=k-1`, every policy has a unit-variance Gaussian mean vector in `[0,1]^k` with expected regret at least `sqrt((k-1)n)/27` | compiled as `finiteArmedGaussianMinimaxLowerBound`; the environment witness, event comparison, exact history KL bound, `1/27` constant, worst-case, and minimax consequences all compile |
| `TXT-LS-2020-DEF-16-1-CONSISTENCY` | Ch. 16, §16.1, Definition 16.1 / Eq. (16.1), CUP print p. 177 / author-online p. 207 / physical PDF p. 216 | one policy is consistent over `E` exactly when `R_n(pi,nu)/n^p -> 0` for every `nu in E` and every real `p>0` | exact generic quantifier interface and sum/power/log-growth dependencies compiled; no bandit terminal claimed |
| `TXT-LS-2020-THM-16-2-ASYMPTOTIC` | Ch. 16, §16.1, Theorem 16.2 / Eq. (16.2), CUP print pp. 177--179 / author-online pp. 207--208 / physical PDF pp. 216--217 | for an unstructured product class and a consistent policy, `liminf R_n/log n` is at least `sum_{i:Delta_i>0} Delta_i/d_inf(P_i,muStar,M_i)` | `d_inf`, candidate, Gaussian perturbation, and consistency analytic leaves compiled; expected-pull information and liminf terminals blocked |
| `TXT-LS-2020-LEMMA-16-3-FINITE-TIME` | Ch. 16, §16.2, Lemma 16.3 / Eq. (16.4), CUP print p. 180 / author-online p. 209 / physical PDF p. 218 | for a one-arm change making arm `i` uniquely optimal, lower-bound original-law expected pulls using the exact log regret-sum numerator divided by `D(P_i,P_i')` | one-arm history KL, the measurable majority event, BH information, finite-KL evaluation, and scalar log rearrangement compile; the two source-general event-to-expected-pseudo-regret producers and exact terminal remain blocked |
| `TXT-LS-2020-THM-16-4-GAUSSIAN-FINITE-TIME` | Ch. 16, §16.2, Theorem 16.4 / Eq. (16.5), CUP print p. 180 / author-online pp. 209--210 / physical PDF pp. 218--219 | under the local unit-Gaussian `C n^p` envelope, sum the exact positive-part per-gap terms with factor `2/(1+epsilon)^2` | exact target frozen; Gaussian arm KL available, but Lemma 16.3 and final regret terminal blocked |
| `TXT-LS-2020-THM-17-1-STOCHASTIC-TAIL` | Ch. 17, §17.1, Theorem 17.1, CUP print pp. 186--187 / author-online pp. 216--217 / physical PDF pp. 225--226 | a uniform `B sqrt((k-1)n)` expected-regret envelope forces random pseudo-regret above `(1/4) min{n,(1/B)sqrt((k-1)n)log(1/(4delta))}` with probability at least `delta` on some Gaussian instance | exact target, threshold, and Lemma 15.1 history KL compiled; the Chapter 17 tail-event consumer and bandit terminal remain blocked |
| `TXT-LS-2020-COR-17-2-STOCHASTIC-MINIMAX-TAIL` | Ch. 17, §17.1, Corollary 17.2 / Eqs. (17.6)--(17.7), CUP print p. 187 / author-online p. 217 / physical PDF p. 226 | under the exact horizon-confidence side condition, every policy has a Gaussian instance with the stated outer-quarter minimax random-pseudo-regret tail | exact threshold compiled; expectation contradiction and terminal blocked |
| `TXT-LS-2020-COR-17-3-UNIFORM-TAIL-IMPOSSIBILITY` | Ch. 17, §17.1, Corollary 17.3, CUP print pp. 187--188 / author-online pp. 217--218 / physical PDF pp. 226--227 | no single policy has strict `<delta` tail at `B sqrt((k-1)n) log(1/delta)^p` for all horizons, confidence levels, and Gaussian environments when `p in (0,1)` | exact target frozen; tail integration and Theorem 17.1 terminal blocked |
| `TXT-LS-2020-THM-17-4-ADVERSARIAL-TAIL` | Ch. 17, §17.2, Theorem 17.4, CUP print pp. 188--190 / author-online pp. 218--220 / physical PDF pp. 227--229 | under `n>=Ck log(1/(2delta))`, some deterministic bounded reward matrix has random-regret tail at `c sqrt(nk log(1/(2delta)))` at least `delta` | threshold and Claim 17.5 first moment compiled; clipped-normal construction and terminal blocked |
| `TXT-LS-2020-CLAIMS-17-5-17-7` | Ch. 17, §17.2, Claims 17.5--17.7 and Eq. (17.8), CUP print pp. 189--190 / author-online pp. 219--220 / physical PDF pp. 228--229 | first-moment deterministic witness, clipped-normal pull-small event, pathwise regret comparison, and clipping-count concentration | Claim 17.5 plus event-subtraction/quarter algebra compile; Claims 17.6--17.7 and construction-level Eq. (17.8) blocked |

The Chapter 13 conversion window is
[`conversion-windows/TEXTBOOK-PART-IV-CHAPTER-13-BASIC-LOWER-BOUND-SPINE.md`](../../conversion-windows/TEXTBOOK-PART-IV-CHAPTER-13-BASIC-LOWER-BOUND-SPINE.md).
The Chapter 14 conversion window is
[`conversion-windows/TEXTBOOK-PART-IV-CHAPTER-14-INFORMATION-THEORY-SPINE.md`](../../conversion-windows/TEXTBOOK-PART-IV-CHAPTER-14-INFORMATION-THEORY-SPINE.md).
The Chapter 15 conversion window is
[`conversion-windows/TEXTBOOK-PART-IV-CHAPTER-15-MINIMAX-LOWER-BOUNDS-SPINE.md`](../../conversion-windows/TEXTBOOK-PART-IV-CHAPTER-15-MINIMAX-LOWER-BOUNDS-SPINE.md).
The Chapter 16 conversion window is
[`conversion-windows/TEXTBOOK-PART-IV-CHAPTER-16-INSTANCE-DEPENDENT-LOWER-BOUNDS-SPINE.md`](../../conversion-windows/TEXTBOOK-PART-IV-CHAPTER-16-INSTANCE-DEPENDENT-LOWER-BOUNDS-SPINE.md).
The Chapter 17 conversion window is
[`conversion-windows/TEXTBOOK-PART-IV-CHAPTER-17-HIGH-PROBABILITY-LOWER-BOUNDS-SPINE.md`](../../conversion-windows/TEXTBOOK-PART-IV-CHAPTER-17-HIGH-PROBABILITY-LOWER-BOUNDS-SPINE.md).
The Chapter 14 kernel chain-rule retrieval candidate has now been developed
into local compiled infrastructure: the project proves the missing measurable
conditional-KL integral, constructs the canonical finite history law for the
existing kernel-valued randomized `HistoryAlgorithm`, and closes Lemma 15.1.
The Chapter 15 Gaussian construction now consumes that identity and compiles
Theorem 15.2 and its minimax consequence.  The later Chapter 16--17
information and tail consumers remain separate targets.

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
