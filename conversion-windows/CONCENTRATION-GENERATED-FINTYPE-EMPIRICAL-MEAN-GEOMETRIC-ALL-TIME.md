# Conversion Window: Generated finite-arm empirical-mean geometric all-time confidence

Task id: `CONCENTRATION-GENERATED-FINTYPE-EMPIRICAL-MEAN-GEOMETRIC-ALL-TIME`

Source cards: `TXT-LATTIMORE-SZEPESVARI-2020`, `PPR-AUER-CBF-2002-UCB1`
Scenario card: `SCN-STOCHASTIC-FINITE`

## Natural-Language Statement

Fix one canonical trajectory law generated from a probability initial pair,
a measurable history policy, measurable context/state maps, and a centered
reward kernel. Suppose the selected reward variance proxy is uniformly at
most `sigma2`, and every arm has one history-stationary mean. For every
positive successor horizon and every arm, use the existing positive-random-
count empirical-mean radius with that arm's geometric confidence share. The
outer measure of the union of all these failures is at most the total budget.

## Lean Mapping

| Symbol | Meaning | Lean surface | Status |
| --- | --- | --- | --- |
| `mu` | canonical pair trajectory law | `Kernel.trajMeasure mu0 stepKernel` | compiled parent |
| `A` | finite action family | `[Fintype Action] [Nonempty Action]` | explicit |
| `N_a(n+1)` | positive successor pull count | `successorArmPullCount action arm (n+1)` | compiled |
| `hat_mu_a(n+1)` | successor empirical mean | `successorArmEmpiricalMean` | compiled |
| `delta_n / card(A)` | per-arm/time share | geometric share divided by `Fintype.card Action` | fixed |
| all-time event | union over `n`, then `arm` | nested `Set.iUnion` | compiled |

## Assumption Ledger

| Assumption | Lean status | Purpose |
| --- | --- | --- |
| probability initial pair law | typeclass | canonical trajectory probability |
| measurable context/state | explicit | generated step kernel |
| Standard Borel/measurable singleton finite action | typeclasses | selected action and trajectory APIs |
| centered reward kernel law | explicit | conditional sub-Gaussian parent |
| global selected-history proxy `<= sigma2` | explicit | every time-index parent tail |
| history-stationary mean for every arm | explicit | empirical-mean centering |
| positive real coercion of `sigma2` | explicit | parent radius |
| `delta > 0` | explicit | positive geometric per-event shares |
| event measurability/independence/`delta<=1` | deliberately absent | outer-measure composition |

## Proof DAG

| Node | Interface | Dependencies | Gate | Status |
| --- | --- | --- | --- | --- |
| N0 | one arm at horizon `n+1` | canonical random-pull-count parent | imported | compiled |
| N1 | one time, all finite arms | N0 plus finite equal shares | focused | compiled |
| root | every time and arm, total `delta` | N1 plus geometric all-time adapter | full harness | accepted |

## Gaps

- [x] No duplicate local all-time empirical-mean producer exists.
- [x] Exact parent declarations and Mathlib cards were retrieved.
- [x] Lean source/root/`Tests`/typed canary compile; full-result SafeVerify and
  the baseline axiom audit pass.
- [x] Review, lifecycle promotion, website synchronization, paper export/build,
  and full gate.
