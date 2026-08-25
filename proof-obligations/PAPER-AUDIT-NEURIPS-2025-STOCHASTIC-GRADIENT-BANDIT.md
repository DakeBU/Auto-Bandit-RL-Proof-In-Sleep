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
| SGB-EQ8-EXPONENTIAL-MOMENT | source-exact `C_eta`, its monotonicity, `C_eta <= exp(2 eta)`, and Equation (8) | compiled | generic probability law with a.e. measurable reward supported on `[-1,1]`; retained as a standalone analytic theorem |
| SGB-EQ8-GENERATED-KERNEL | Equation (8) on the generated initial and successor reward kernels | compiled | 4 declarations; armwise support and fixed means remain explicit |
| SGB-TWO-ARM-SUCCESSOR-RECURRENCE | forward/inverse fixed-history successor recurrence inequalities | compiled | 10 declarations; generated-kernel Equation (8), exact signs, and success/failure-square remainders |
| SGB-TWO-ARM-INITIAL-RECURRENCE | uniform source initialization and both time-one recurrence inequalities | compiled | 3 declarations; zero initialization gives `p_1=1/2` |
| SGB-MEASURABLE-RECURRENCE | measurable bounded fixed-mean contract, trajectory, filtration, and a.e. conditional-distribution transport | compiled | 25 declarations; general prior reveals latent `Env`, while a fixed/Dirac environment gives the fixed-instance reading |
| SGB-PATH-INTEGRABILITY | finite-prefix reward support, source-parameter envelope, potential identities/integrability, condexp identities, and tower-ready recurrence bounds | compiled | 17 declarations in the exact 2+4+2+1+2+2+2+2 split; no global tower iteration is claimed |
| SGB-FIXED-IID-SOURCE-CONTRACT | fixed two-arm probability laws to the bounded fixed-mean history-environment contract | compiled | 8 declarations: 2 definitions and 6 theorems; `twoArmFixedIIDEnvironment_contract` is a one-way bridge, not an equivalence |
| SGB-FIXED-IID-EQ5-INTEGRABILITY | discharge Equation-(5)'s `Integrable sourceIncrement` premise on the generated fixed-IID history | blocked | reward-id `AEStronglyMeasurable` and the environment contract compile, but no theorem derives this generated-history integrability premise |
| SGB-THEOREM-1 | exact two-arm finite-regret endpoint | blocked | global tower iteration, expected squared failure-mass control, and Equation-(7) terminal assembly absent |
| SGB-THEOREMS-2-4 | logarithmic/polynomial and general-`K` learning-rate endpoints | blocked | source-specific rate arguments uncompiled |
| SGB-CANARY | typed checks and representative axiom prints | compiled | baseline axioms only |
| SGB-EVIDENCE-SITE | reference index, Blueprint, website source links, anonymous ledger | pending refresh | maintained sources now target 143 declarations in the `26+18+18+14+4+10+3+25+17+8` split; generated evidence must be rebuilt and checked |
| SGB-REVIEW | independent source/claim review | partial | earlier two-arm/Equation-(8) layers reviewed; final path-integrability and synchronized-claim review remains required |

No obligation may be promoted because a prose theorem card exists. Only the
focused Lean module, canary, full gate, and generated evidence may move the
finite algebra, process, generated Equation-(8), recurrence, or path-
integrability rows to `compiled`; the overall audit remains `partial`, and the
Theorem-1 and Theorems-2--4 rows remain `blocked`, because global recurrence
iteration, expected failure-mass control, Equation-(7) assembly, and every
source learning-rate endpoint remain absent.  The fixed-IID adapter discharges
the separate fixed two-arm source-law producer by mapping its probability,
support, measurability, and integral-mean hypotheses into the bounded fixed-
mean contract.  The map is one-way and does not identify the broader contract
with fixed IID laws.  It also does not discharge Equation-(5)'s separate
generated-history `Integrable sourceIncrement` premise, which remains blocked.
