from pathlib import Path
P=Path(__file__).resolve().parent;s=(P/'candidate-v1.lean').read_text(encoding='utf-8')
s=s.replace('RCLike.inner_apply]\n    ring','RCLike.inner_apply]\n    change v 0 * w 0 + v 1 * w 1 = w 0 * v 0 + w 1 * v 1\n    ring',1)
s=s.replace('have hn : ‖query‖ ^ 2 = (1 : ℝ) := by norm_num [query]','have hn : ‖query‖ ^ 2 = (1 : ℝ) := by\n    change ‖(fun _ : Fin 2 => (1 : ℝ))‖ ^ 2 = 1\n    norm_num')
s=s.replace('have hfq : objective query = (2 : EReal) := by norm_num [objective, query]','have hfq : objective query = (2 : EReal) := by\n    norm_num [objective, query]\n    rfl')
s=s.replace('rw [hf0, hfq, hp, hc]\n    norm_num','rw [hf0, hfq, hp, hc]\n    change ¬ ((0 : ℝ) + 1 + (1 / 2) * 8 ≤ 2)\n    norm_num')
s=s.replace('rw [hfq, hfn, hf0, hdiff]\n  norm_num','rw [hfq, hfn, hf0, hdiff]\n  change (1 / 2 : ℝ) * 2 + (1 / 2) * 0 - 0 - (1 / 2) * (1 / 2) * (1 / 2) * 4 = 1 / 2\n  norm_num')
s=s.replace('Set.eq_empty_iff_forall_not_mem','Set.eq_empty_iff_forall_notMem')
tail='  · norm_num [negativeSquare]\n\nend '
s=s.replace(tail,'  · change (((1 / 2 : ℝ) * (-1) + (1 / 2) * (-1) : ℝ) : EReal) = ((-1 : ℝ) : EReal)\n    congr 1\n    norm_num\n\nend ')
with (P/'candidate-v2.lean').open('xb') as f:f.write(s.encode())
