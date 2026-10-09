# Conversion Window: Same-run prescient cumulative bounds: frozen five-terminal conversion

Task id: `ONLINE-CH2-PRESCIENT-CUMULATIVE-20261009`

Source card:
Scenario card:

## Natural-Language Statement

Write the theorem, proof fragment, or paper equation in precise prose.

## Lean Mapping

| Source symbol | Meaning | Lean declaration | Type / role | Status |
| --- | --- | --- | --- | --- |
| `A_t` | action at time `t` | | action process | unmapped |

## Assumption Ledger

| Assumption | Lean status | Source | Blocking? |
| --- | --- | --- | --- |
| finite action set | typed | task packet | no |
| sub-Gaussian rewards | obligation | cited result | yes |

## Local API And Proof Route

| Leaf | Existing APIs/imports | Mathlib/LML cards | Intended route | Pivot rule |
| --- | --- | --- | --- | --- |
| root | TBD | TBD | theorem-card route plus local wrappers | pivot only after reviewer records a mathematical reason |

## Proof-DAG

| Node | Interface | Dependencies | Owner | Lean declaration | Human proof map | Retrieval cards | Regularity contracts | Mathlib status | Gate | Status |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| root | target theorem | TBD | upper | | this file | TBD | TBD | project-local | `lake build && lake build Tests` | planned |

## Gaps

- [ ] Missing definition:
- [ ] Missing lemma:
- [ ] Missing regularity contract:
- [ ] Mathlib candidate to upstream:
- [ ] Missing cited-result entry:

Delayed native artifact materialization after BODY review. The draft conversion intent below existed in director-architect-draft-v1.md at its indexed draft SHA; this native template did NOT exist at stabilization and is not backdated. No new target or premise.

# Draft roles, obligations, conversion window

Route: online-learning Chapter2 forward dependency on Algorithm15.8/Theorem15.30, not early Chapter15 acceptance. Source card, exact headers/scoped context and real type probe are separate artifacts. Reuse canonical iterate_one_step and weighted_potential_sum; sum_range_sub' handles fixed telescope. No duplicate algorithm/divergence/Abel library. Inspiration-only weapons do not certify dependencies.

DAG: iterate_one_step + actual-success/interior witnesses + DifferentiableOn.differentiableAt -> iterate_divergence_sum; this common interface -> iterate_fixed_sharp via sum_range_sub' and actualinitialstate identity; same common interface -> iterate_variable_sharp via a=2B,C=2M in canonical weighted_potential_sum. Each sharp -> corresponding printed corollary via divergence_nonneg, strictconvex.convexOn and positive final denominator. Nonempty finite range uses nonempty_range_iff, max bound uses le_sup'. First ready lower leaf after contractreview: iterate_divergence_sum only.

Semantic signature: complete real inner-product E (generalization from finite-dimensional source); deterministic all fixed comparators u in V, actualsuccessstates0..T, sourceinteriorstates all including terminal/initial, wholecurrentlosses, EReal proper/global source supports at V, positive steps. Constanteta allows T0. VariableT>=1 and monotonicity only used pairs inside horizon; maximum ranges PREVIOUSstates0..T-1. No unnecessary bounded domain. No assumed regret/stability bound. Negative terminal retained in sharps; printedcorollaries drop it only with certified nonnegativity. Initialcenterx0 recovered from recursion at0; no requirement x0 in V/lossdomain.

Source-vs-Lean deltas for explicit review: sourcepsi:X->R represented by ambientpsi plus interior differentiability; existing locality theorem licenses divergence independence only targetinX/baseinteriorX. Generic sharp interfaces do not need convex/closedpsi or VsubsetX because ordered divergence algebra needs only actual derivatives; printedcorollaries require strictconvexonX and VsubsetX. Closedness of V/psi omitted as unused conditional theorem assumptions, NOT asserted to imply attainment/interiorpreservation. Source nonemptyV and Vsubsetfinite-domain/no-bottom imply SourceProper: this exact source-facing transport remains open; current APIs state it plus global supports explicitly. hseq encodes well-defined selected actualrun; no generalexistence from closed/strict. Stronger conditional math is reusable, not automatic full source closure. Lossdifferences are finite toReal comparisons whose finiteness is supplied by proper/support premises, never infinity subtraction. Full unconditional choiceability, sourceclosedness packaging, all chapter containers remain required/open.

Publication plan after proof gates: exactsourceattribution/formulaproof/assumptiondelta/foldedLean/dependencies/redboundary adjacent; extend shared declaration registry/source-qualified Book map, preserve old links and per-book library. LeanGraph newnodes/actual compilerVALUEparents, Overview updated affectedforward boundaryonly/Chapter2 stillpartial, Functor none-found-with-reason (this is conditional same-setting telescope, no new certified transport). results/frontier/otherBooks no-change-with-reason where unrelated. New contributionmanifest will cover affectedfiles after exact review. Do not alter old data in draft.

Independent obligations: five frozen proof terminals; nondegenerate fixed and decreasing-step canaries with realcurrentlosses/actualminima/interiority/nonzeroordereddivergences/exactprevious-statefiniteMAX and numericVALUEdependencies; declaration probes/statementfences/axiomaudit/focusedbuild/combinedrootTests/fullharness/shadow/contributor/sitebrowser; distinct semantic BODY/FINALreview. Counts are package obligations only; chapter denominator remains null.

Frozen source/headers/context/DAG: docs/contracts/online-ch2-prescient-cumulative-v1/stabilized-v1.json. All five exact theorem bodies are now reviewed and focused-compiled; combined/publication/FINAL gates remain separately pending.
