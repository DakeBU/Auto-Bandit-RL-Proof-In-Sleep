from common_v1 import *
fixed()
native('retrieve-public-Regret-v1','list-lean-decls','OnlineLearningRegret','--statement')
native('retrieve-comparator-v1','list-lean-decls','comparatorRegret','--statement')
native('retrieve-noregret-v1','list-lean-decls','noRegret','--statement')
gate('retrieve-actual-mathlib-v1','rg','-n','theorem sum_nonpos|sum_nonpos|div_nonpos_of_nonpos_of_nonneg|sum_congr','--glob','*.lean','.lake/packages/mathlib/Mathlib/Algebra/Order/BigOperators','.lake/packages/mathlib/Mathlib/Algebra/Order/Field')
gate('actual-lean-version-v1','lake','env','lean','--version')
native('retrieval-record-v1','retrieval-record','--task',TASK,'--query','Typed W-loss/V-comparator instantiation, finite-prefix invariance and eventual upper NoRegret','--candidate',PRE+'comparatorRegret','--candidate',PRE+'comparatorRegret_eq_sum','--candidate',PRE+'NoRegret','--candidate',PRE+'noRegret_of_vanishing_bound','--rejection','generic W performance theorem=Footnote1 supplies no such guarantee','--provenance',(RUN/'retrieve-comparator-v1.log').as_posix(),'--output',(RUN/'retrieval-native-v1.json').as_posix())
fixed()
