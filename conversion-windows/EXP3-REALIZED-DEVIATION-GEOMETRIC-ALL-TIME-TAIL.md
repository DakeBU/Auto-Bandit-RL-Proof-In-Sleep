# Conversion Window: Generated EXP3 realized-deviation geometric all-time tail

Task id: `EXP3-REALIZED-DEVIATION-GEOMETRIC-ALL-TIME-TAIL`

Source cards: `TXT-LATTIMORE-SZEPESVARI-2020`,
`PPR-AUER-CFS-2002-EXP3` (placement only)
Scenario card: `SCN-ADVERSARIAL-FINITE`

## Natural-Language Statement

Fix one generated EXP3 process. For prefix `n+1`, use confidence share
`delta/2/2^n` and deterministic predictable-variance budget `n+1`. The
outer measure of samples where realized-minus-predictable selected loss crosses its
corresponding quadratic radius at at least one positive prefix is at most
`ENNReal.ofReal delta`.

## Lean Mapping

| Symbol | Meaning | Lean declaration | Status |
| --- | --- | --- | --- |
| `V_n` | deterministic variance budget `n+1` | `sampledRealizedPredictableVarianceLinearBudget n` | compiled |
| `r_n` | quadratic radius at `V_n` and `delta/2/2^n` | `sampledRealizedDeviationGeometricAllTimeRadius delta n` | compiled |
| `D_n` | realized-minus-predictable selected-loss sum over `range (n+1)` | existing finite sum of `sampledTrajectoryRealizedDeviationAt` | compiled parent |
| `E` | `union_n {r_n <= D_n}` | `sampledRealizedDeviationGeometricAllTimeFailureSet` | compiled |

## Assumption Ledger

| Assumption | Lean status | Source | Blocking? |
| --- | --- | --- | --- |
| finite action law and `[0,1]` losses | explicit for generic variance leaf | generated EXP3 loss regularity | no |
| measurable Env, measurable-singleton Action, decidable nonempty arms, `0<=gamma<=1` | explicit API-level contract for deterministic generated budget | generated distribution source | no |
| probability prior and Standard Borel nonempty Env/Action | explicit for terminal measure theorem | generated trajectory law | no |
| fixed `eta`, `gamma`, arms, prior, and predictable loss process | statement scope | one-process requirement | no |
| positive outer `delta` | explicit | geometric schedule and quadratic optimizer | no |
| event measurability, independence, stationarity | deliberately absent | inherited outer-measure route | no |

## Proof DAG

| Node | Interface | Dependencies | Owner | Gate | Status |
| --- | --- | --- | --- | --- | --- |
| N0 | finite-law centered second moment `<=1` | finite distribution and unit interval | lower | focused | compiled |
| N1 | generated pointwise variance `<=1` and prefix sum `<=horizon` | N0; generated probability/loss source | lower | focused/Tests | compiled |
| N2 | linear budget, radius, pure event, membership | prior all-time definitions | lower | focused/Tests | compiled |
| N3 | old joint event at linear budget equals pure event | N1-N2 | middle | focused/Tests | compiled |
| root | pure all-time failure mass `<=ofReal delta` | N3; accepted joint all-time theorem | upper | full harness | accepted |

## Remaining Boundaries

- The radius uses the universal unit variance envelope; it is not a small-loss,
  sparse-loss, empirical-variance, or self-normalized boundary.
- The theorem controls selected-loss deviation only. Full realized regret
  still needs the potential, exploration, and comparator terms on the same
  fixed process.
- No Ville/Doob, mixture, optional stopping, general Freedman, horizon-varying
  tuning, or ideal EXP3.P conclusion is implied.
