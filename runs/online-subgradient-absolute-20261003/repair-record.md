# Body/context-only repairs

full-leaf01: three sign leaves compiled, but linarith cannot infer strict negativity from nonpositivity and a disequality. Replaced only the final proof step with lt_of_le_of_ne; full-leaf02 compiles all four unchanged headers. Error-recovery sorryAx rejected.

full-canary01: ordinary simp did not decide the concrete negative numeral inequality in the source conditional. Canary02 uses norm_num on the actual source theorem instance. Original log and snapshot retained; no source statement changed.

All failed snapshots remain evidence of failure, not compilation or acceptance.
