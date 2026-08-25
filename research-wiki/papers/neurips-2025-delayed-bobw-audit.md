# NeurIPS 2025 delayed-feedback best-of-both-worlds audit

Card: `PPR-SCHLISSELBERG-LANCEWICKI-AUER-MANSOUR-2025-DELAYED-BOBW`

Status: `source-frozen; accounting, causal-view, new-arrival-processing,
active-allocation, optimal-arm-survival, and one-round action-law leaves plus
a D.10/D.12 width-direction diagnostic, a conditional same-snapshot repair
skeleton, a
  conditional gap-ordering consumer, a deterministic processed-trace-summary
  adapter, one ordered no-switch structural processing step, and a generic multi-regime contract
interface compiled; no paper endpoint audited`

## Frozen source

- Schlisselberg, Lancewicki, Auer, and Mansour, *Improved Best-of-Both-Worlds
  Regret for Bandits with Delayed Feedback*, NeurIPS 2025.
- Official camera-ready:
  <https://proceedings.neurips.cc/paper_files/paper/2025/file/02f0ac0a323dc17d964d4bbf8a62e01b-Paper-Conference.pdf>
- SHA-256:
  `525240c98b67616b4918bf5bffb799577f298786fc46538aff91153380ae0f9e`.
- The 38-page camera-ready includes the appendices used by this audit.
- Version cross-check on 2026-08-18: the latest listed
  [arXiv v2](https://arxiv.org/abs/2505.24193) (2025-10-19; downloaded PDF
  SHA-256 `79326ce5724e1eddea039f221943b6f54dcc3c3e223511de4a130e101b291c31`)
  and the public OpenReview PDF retain the same displayed D.10/D.12 chain.
  A targeted proceedings/arXiv/OpenReview/author-page scan found no public
  erratum; this is a search record, not evidence that none exists.

## Multi-regime target contract

The source claim is coupled.  It is not reproduced by separately proving a
stochastic theorem for one policy and an adversarial theorem for another.
The frozen contract therefore retains:

1. one horizon-aware Delayed SAPO algorithm, initialized once, with one
   monitoring/switch mechanism and the same tuning in both regimes;
2. feedback tuple `(source round, observed loss)` becomes available only after
   its source-specific delay, and the delay is unknown when the action is
   chosen;
3. losses and delays are selected by oblivious adversaries in the adversarial
   regime; stochastic losses are armwise iid while delays remain adversarial
   in the stochastic regime;
4. expected regret is against the best fixed arm;
5. Theorem 4.1 is the stochastic endpoint, Theorem 5.1 is the generic
   adversarial-composition endpoint, and Corollary 5.4 chooses the external
   adversarial algorithm;
6. the physical PDF page-7 Theorem 4.1 retains its `log K` term; the reduced
   `log K` algorithm is a separate Appendix-F refinement;
7. `T >= K`, positive finite arms, source-time indexing, and the external
   algorithm's regret contract remain explicit.

## First three leaves

| Leaf | Intended role | Initial evidence status |
| --- | --- | --- |
| `DELAYED-BOBW-FEEDBACK-AVAILABILITY-PARTITION` | formalize physical PDF page 4's `B(t)={s:s+d_s<t}` and the complementary outstanding set without an off-by-one drift | compiled project-local leaf |
| `DELAYED-BOBW-MISSING-COUNT-SURFACE` | identify the action-time outstanding count and its maximum-over-time surface before probability arguments | compiled project-local leaf; not yet identified with the paper's end-of-round `sigma` |
| `DELAYED-BOBW-SIGMA-INDEX-BRIDGE` | relate the paper's one-based end-of-round `sigma(t)` carrier to the zero-based action-time outstanding set without silently changing a strict inequality | compiled project-local leaf |
| `DELAYED-BOBW-SAME-ALGORITHM-REGIME-CONTRACT` | package one algorithm/tuning/information/comparator identity shared by Theorems 4.1 and 5.1 | compiled generic interface; no Delayed SAPO implementation or theorem endpoint |
| `DELAYED-BOBW-CAUSAL-ACTION-TIME-VIEW` | expose past actions and strictly available losses without passing hidden delays or unobserved losses to the decision rule | compiled interface and observation-equivalence theorem; no randomized kernel or Delayed SAPO state |
| `DELAYED-BOBW-NEWLY-OBSERVED-PROCESSING` | formalize the set-level `B(t) \ S` batch update | compiled monotonicity/disjointness/exact-update layer; simultaneous-arrival order and BSC/EAP state open |
| `DELAYED-BOBW-ACTIVE-EQUAL-ALLOCATION` | formalize Algorithm 5 line 15's residual equal allocation | compiled nonnegativity and total-mass-one leaf under explicit inactive-mass hypotheses; EAP maintenance and sampling kernel open |
| `DELAYED-BOBW-OPTIMAL-ARM-SURVIVAL` | connect Algorithm 5 lines 7--8 to the nonempty-active premise in line 15 | compiled deterministic core of source Lemma D.9 under an explicit certificate; full recursive lemma open |
| `DELAYED-BOBW-GOOD-EVENT-D9-PROJECTION` | derive the certificate from the two source upper-confidence surfaces and carry a supplied event-failure budget to optimal-arm elimination | compiled elimination projection and probability-bound consumer; full Definition D.1 and D.2--D.7 component producers open |
| `DELAYED-BOBW-D8-D9-ASSEMBLY` | union the six D.2--D.7 failure components into Corollary D.8's `9/T` budget and compose it with D.9 survival | compiled outer-measure union and event transport; the six component bounds and full-event projection remain hypotheses |
| `DELAYED-BOBW-D10-D12-GAP-ORDERING-AUDIT` | audit the prefix/elimination width transport used between Appendix Lemmas D.10 and D.12 | compiled antitone-width diagnostic, a literal `T=4` reverse-direction witness, a line-7 gap lower bound, the exact small-count scalar implication, a large/small-count active-arm consumer, a conditional same-snapshot factor-20 consumer, and the earlier conditional four-edge consumer; downstream D.1 and trace-summary layers now supply algebraic inputs conditionally, while D.4 probability remains open, so D.10/D.12 remain unresolved |
| `DELAYED-BOBW-D1-ACTIVE-COUNT-TO-WIDTH-PRODUCER` | turn Algorithm 5 line-15 source-time allocations and the exact D.1 count clause into the missing same-prefix D.10/D.12 inputs | compiled processed-prefix action/allocation ledger, equal active-arm pull-mass theorem, exact `n_j >= n_i/4 - 6 log T` comparison, large/small width producers, recursive-UCB edge, unconditional same-prefix factor-ten theorem, and conditional factor-20 gap theorem; the compiled trace-summary adapter constructs its certificate, while Algorithm-5 generation and D.4 probability remain open |
| `DELAYED-BOBW-PROCESSED-TRACE-SUMMARY-ADAPTER` | construct the count certificate from a source-shaped trace summary without conflating processing order, source round, and intra-round active state | compiled distinct source-index ledger, strict-availability witnesses, separate intra-round/source-round active surfaces, explicit current-to-source containment invariant, definitionally generated source width/recursive UCB, D.4 count-clause boundary, certificate producer, and conditional factor-20 consumer; Algorithm-5 generation/invariant production and D.4's `2/T` bound remain open |
| `DELAYED-BOBW-ORDERED-NO-SWITCH-PROCESS-ONE` | refine one Algorithm 5 lines 3--4 and 7--8 iteration without imposing chronological order | compiled 15-declaration structural transition: append an arbitrary member of `B(t) \ S`, preserve duplicate-freedom, derive strict availability and source-index injectivity, build the line-7 summary, use exact line-8 `remainingActive`, and preserve the round-start active-set invariant; numeric BSC/EAP generation, switch logic, measurable recursion, D.4, and endpoints remain open |
| `DELAYED-BOBW-CAUSAL-ACTION-MEASURE` | turn the line-15 vector into a causal one-round randomized law | compiled probability measure and observation-equivalence transport; measurable history kernel and recursive trajectory open |

These leaves are deliberately small but source-semantic: they check the exact
meaning of “available at round `t`” before any martingale or regret work.  It
does not establish either theorem, a regret bound, stochastic concentration,
or best-of-both-worlds performance.

## Route placement

- Scenarios: `SCN-DELAYED-BOBW`, `SCN-DELAYED-BATCHED`,
  `SCN-BOBW-ADAPTIVE`.
- Theory branch: `ROUTE-ROBUST-NONSTATIONARY-DELAYED`.
- Textbook calibration: `TXT-LATTIMORE-SZEPESVARI-2020` for finite-bandit and
  martingale infrastructure; no textbook theorem is treated as this paper.
- Mathlib retrieval cards: `MLIB-FINSET-SUMS`,
  `MLIB-MARTINGALE-STOCHASTIC`, `MLIB-CONDITIONAL-EXPECTATION`.
- Proof-weapon inspiration only: `WEAPON-TAIL-INEQUALITIES`.

## Known technology boundary

The current library has rich finite-action, kernel, conditional-MGF, EXP3,
Tsallis, and adaptive-trajectory infrastructure.  It now also has one
source-exact elimination snapshot, a source-shaped good-event projection, the
Corollary-D.8 union assembly, the deterministic optimal-arm survival consumer,
the D.10/D.12 direction diagnostic, the exact small-count width lower bound, a
source-time processed-prefix ledger, D.1 count-to-width producers, a
conditional same-snapshot factor-20 theorem, the earlier conditional four-edge
consumer, a causal measure-valued one-round action rule, and a deterministic
  processed-trace-summary adapter and one ordered no-switch processing step.
  The adapter records distinct, strictly
available, possibly nonchronological source indices; reads each action and
allocation at source time; and keeps the intra-round active set separate from
the antitone source-round trace while recording containment explicitly.  It
  The one-step structural transition now constructs those fields and proves
  containment for an explicit round state after appending an arbitrary newly
  observed source, and preserves the invariant through exact line-8 removal.
  It does not construct the numerical BSC/EAP surfaces, a random state, or a
  round-to-round measurable Algorithm-5 trajectory.  The
count-to-width producer
derives rather than assumes the large/small branch, recursive-UCB edge, and
same-prefix factor-ten comparison.  Its remaining stochastic boundary is a
  measurable generated Delayed-SAPO trajectory, its numerical transition into
  the structural state, and the D.4 simultaneous `2/T`
probability proof for the two count inequalities.  It therefore still neither
verifies nor refutes the source lemmas.
The library does not yet
have the paper's complete delayed SAPO state machine, probability banks,
measurable recursive sampling kernel, detection/switch semantics, the complete
Definition-D.1 event, D.2--D.7 component probability producers, a proved
full-event projection, or the coupled
terminal.  Full Theorems 4.1 and 5.1
must remain `planned` until their exact algorithms and proof chains compile.
