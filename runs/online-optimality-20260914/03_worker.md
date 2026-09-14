v1 stabilized before theorem bodies. First attempt uses local minimum derivatives along feasible segments and finite EReal coercion. No terminal edits authorized in repair.

Leaf01: IsMinOn is a set/filter predicate; arithmetic and rewrites did not unfold membership automatically. Leaf02 explicitly changes those goals/hypotheses to inequalities. No statement change.

Canary01 rejected: membership elaboration and EReal numeral/coercion simplification failed; failed theorem elaborations produced sorryAx in that rejected log. Canary02 uses explicit membership proofs and finite coe-order rewriting, without changing targets or premises. Core statements all had standard axioms already.

Canary02: only one remaining implicit Ici membership elaboration at sub_nonneg. Canary03 states the real inequality explicitly; no assumptions changed.
