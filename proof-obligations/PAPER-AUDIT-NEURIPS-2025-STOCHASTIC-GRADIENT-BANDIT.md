# Proof obligations: NeurIPS 2025 stochastic-gradient-bandit source audit

Task id: `PAPER-AUDIT-NEURIPS-2025-STOCHASTIC-GRADIENT-BANDIT`

| Obligation | Evidence target | Status | Boundary |
| --- | --- | --- | --- |
| SGB-3 softmax law | positive denominator, positive coordinates, sum one | compiled | deterministic finite action set |
| SGB-4 Algorithm-1 update | exact selected/nonselected formula and zero-sum | compiled | reward is a scalar input |
| SGB-5 conditional-mean algebra | gradient and gap coordinate identities | compiled | finite categorical expectation after conditioning |
| SGB-6 best-arm cumulative lower bound | pointwise and finite-horizon forms | compiled | unique best and positive minimum gap explicit |
| SGB-7 regret split | post-convergence plus squared failure mass | compiled | maximum-gap envelope and positive `eta*Delta` explicit |
| SGB-HISTORY trajectory lift | history kernel, measurability, conditional reward mean | blocked | not implied by finite algebra |
| SGB-RATES paper endpoints | Theorems 1--4 | blocked | learning-rate/failure-probability analysis absent |
| SGB-CANARY | typed checks and representative axiom prints | compiled | baseline axioms only |
| SGB-EVIDENCE-SITE | reference index, Blueprint, website source links | compiled | 26 declarations agree across generated evidence |
| SGB-REVIEW | independent source/claim review | compiled | no unresolved content-level blocking/high/medium finding |

No obligation may be promoted because a prose theorem card exists. Only the
focused Lean module, canary, full gate, and generated evidence may move the
finite algebra rows to `compiled`; the stochastic history and rate rows remain
blocked until their own declarations exist.
