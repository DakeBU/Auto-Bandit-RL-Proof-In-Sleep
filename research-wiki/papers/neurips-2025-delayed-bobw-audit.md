# NeurIPS 2025 delayed-feedback best-of-both-worlds audit

Card: `PPR-SCHLISSELBERG-LANCEWICKI-AUER-MANSOUR-2025-DELAYED-BOBW`

Status: `source-frozen; accounting, causal-view, new-arrival-processing,
active-allocation, optimal-arm-survival, and one-round action-law leaves plus
a D.10/D.12 width-direction diagnostic, a conditional gap-ordering consumer,
and a generic multi-regime contract interface compiled; no paper endpoint
audited`

## Frozen source

- Schlisselberg, Lancewicki, Auer, and Mansour, *Improved Best-of-Both-Worlds
  Regret for Bandits with Delayed Feedback*, NeurIPS 2025.
- Official camera-ready:
  <https://proceedings.neurips.cc/paper_files/paper/2025/file/02f0ac0a323dc17d964d4bbf8a62e01b-Paper-Conference.pdf>
- SHA-256:
  `525240c98b67616b4918bf5bffb799577f298786fc46538aff91153380ae0f9e`.
- The 38-page camera-ready includes the appendices used by this audit.

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
| `DELAYED-BOBW-D10-D12-GAP-ORDERING-AUDIT` | audit the prefix/elimination width transport used between Appendix Lemmas D.10 and D.12 | compiled antitone-width diagnostic, exact reverse-direction canary, and conditional four-edge factor-20 consumer; the source lemma remains unresolved pending an endpoint/index repair or clarification |
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
the D.10/D.12 direction diagnostic and conditional factor-20 consumer, and a
causal measure-valued one-round action rule.  The diagnostic identifies an
unjustified displayed direction/indexing edge; it neither verifies nor
refutes the source lemmas.  The library does not yet
have the paper's complete delayed SAPO state machine, probability banks,
measurable recursive sampling kernel, detection/switch semantics, the complete
Definition-D.1 event, D.2--D.7 component probability producers, a proved
full-event projection, or the coupled
terminal.  Full Theorems 4.1 and 5.1
must remain `planned` until their exact algorithms and proof chains compile.
