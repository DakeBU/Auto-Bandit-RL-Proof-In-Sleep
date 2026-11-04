# Lean companion track

Reference.lean contains two library-application exercises, BRB-001 and BRB-003. They are intentionally small API warmups, not novel proof synthesis. Both compile in the recorded environment; the complete NL answers have broader scope. BRB-002 and BRB-004 formal views remain planned and are omitted from formal prompt export.

Run from a built, pinned repository environment:

```sh
lake env lean benchmarks/banditrlbench/lean/Reference.lean
```

Next bounded contribution: implement BRB-002 retaining all integrability and measure hypotheses, print its axioms, and independently compare the exact target to the NL contract. Keep the existing core/family/split. Do not add a supplied concentration result as an unnoticed hypothesis or treat a successful reference as evaluation of model predictions. A future evaluator must compile predictions in isolation without reference solutions.
