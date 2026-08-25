# Proof obligations: NeurIPS 2025 stochastic-gradient-bandit source audit

Task id: `PAPER-AUDIT-NEURIPS-2025-STOCHASTIC-GRADIENT-BANDIT`

| Obligation | Evidence target | Status | Boundary |
| --- | --- | --- | --- |
| SGB-3 softmax law | positive denominator, positive coordinates, sum one | compiled | deterministic finite action set |
| SGB-4 Algorithm-1 update | exact selected/nonselected formula and zero-sum | compiled | reward is a scalar input |
| SGB-5 conditional-mean algebra | gradient and gap coordinate identities | compiled | finite categorical expectation after conditioning |
| SGB-6 best-arm cumulative lower bound | pointwise and finite-horizon forms | compiled | unique best and positive minimum gap explicit |
| SGB-7 regret split | post-convergence plus squared failure mass | compiled | maximum-gap envelope and positive `eta*Delta` explicit |
| SGB-HISTORY-STATE | recursive parameter state and measurability | compiled | inclusive history and fixed learning rate explicit |
| SGB-HISTORY-POLICY | initial/successor finite softmax Markov laws | compiled | generated from the recursive state, not assumed |
| SGB-HISTORY-TRAJECTORY | canonical pair trajectory and successor conditional laws | compiled | uses an explicit measurable history environment |
| SGB-EQ5-COND-MEAN | conditional-kernel integral of the generated source increment | compiled | coordinate-update integrability and arm-reward integral equalities remain explicit |
| SGB-TWO-ARM-STRUCTURE | pathwise Equation (9), source-time adapter, uniform initialization, and Equation (11) odds | compiled | `Fin 2`, source zero initialization, and exact trace-time fence explicit |
| SGB-EQ8-EXPONENTIAL-MOMENT | source-exact `C_eta`, its monotonicity, `C_eta <= exp(2 eta)`, and Equation (8) | compiled | generic probability law with a.e. measurable reward supported on `[-1,1]`; not yet a generated conditional-kernel statement |
| SGB-RATES paper endpoints | Theorems 1--4 | blocked | generated-kernel Equation-(8) instantiation, conditional recurrences, expected squared failure-mass control, and terminal assembly absent |
| SGB-CANARY | typed checks and representative axiom prints | compiled | baseline axioms only |
| SGB-EVIDENCE-SITE | reference index, Blueprint, website source links, anonymous ledger | compiled | refreshed and checked at 26 plus 18 plus 18 plus 14 declarations; 642 generated pages and 17,021 Lean source links pass the site gate |
| SGB-REVIEW | independent source/claim review | compiled | two-arm and Equation-(8) layers independently reviewed; no blocking, high, or medium issue |

No obligation may be promoted because a prose theorem card exists. Only the
focused Lean module, canary, full gate, and generated evidence may move the
finite algebra, process, two-arm structure, or Equation-(8) rows to `compiled`; the overall
audit remains `partial`, and the rate row remains `blocked`, because none of
the source learning-rate endpoints follows from these declarations.
