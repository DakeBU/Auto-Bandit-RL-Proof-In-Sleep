from append_leaf_v1 import *
append_leaf('F2','''  by_cases hT : T = 0
  · subst T
    simp [comparatorRegret]
  · unfold comparatorRegret
    rw [empiricalMean_decomposition y T (Nat.pos_of_ne_zero hT) u]
    ring
''')
