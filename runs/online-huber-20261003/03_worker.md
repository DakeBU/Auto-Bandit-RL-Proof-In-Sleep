# Worker attempts

Header probe reports only two deliberate body failures: both target types and the combined prerequisite context elaborate. Leaf01 proves the joining structure but fails quadratic derivative normalization (`x = id x`). Leaf02 adds simplification and compiles; the final candidate replaces the redundant tactic sequence by `simpa` and is compiled as part of canary02.

Canary01 fails three numeric conditional simplifications; its error-recovery sorryAx output is rejected, not treated as a proof. Canary02 explicitly normalizes the numerical derivative coefficient and genuinely compiles all five instances. Both frozen library targets and all five canaries print only propext, Classical.choice and Quot.sound. All failures remain in this run.

Chain continuation: convex leaf01 compiles four targets; vector leaf01 fails implicit point inference, leaf02 compiles three. Vector canaries01/02 fail real-inner/numeric normalization, canary03 passes. OGD leaf01 compiles four targets; OGD canaries01/02 fail concrete real-inner normalization, canary03 uses an explicit definitional multiplication identity and passes the actual step and residual bound. All failed compiler/axiom recovery outputs retained and rejected.
