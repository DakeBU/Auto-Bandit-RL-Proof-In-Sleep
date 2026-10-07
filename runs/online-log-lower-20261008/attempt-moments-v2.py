from common_v1 import *
assert load(RUN/'public-law-build-v2-exit.json')['exit_code']==0
write(RUN/'moments-repair-v2.json',dict(prior_exit=load(RUN/'moments-attempt-v1-exit.json')['exit_code'],
    prior_log_sha256=sha(RUN/'moments-attempt-v1.log'),
    cause='Failed public-law promotion; sum rewrite lambda inference; Bool simplifier name; beta reduction; redundant ring after solved field simplification.',
    correction='Use exactly compiled law-v2; explicit successor function, actual simp reductions and beta reduction; conditional ring sequencing.',
    source_or_frozen_target_changed=False))
addition=(RUN/'moments-addition-v1.lean.txt').read_text(encoding='utf-8')
addition=addition.replace('rw [pathExpectation, sum_vectors_succ]',
    'rw [pathExpectation, sum_vectors_succ T (fun h => pathWeight h * f h)]')
old='''      simp only [List.count_cons, Bool.false_eq_true, Bool.true_eq_true, ↓reduceIte,
        Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero, polyaNext, hl]
      field_simp
      ring'''
assert old in addition
addition=addition.replace(old,'''      simp [polyaNext, hl]
      field_simp <;> ring''')
addition=addition.replace('      unfold polyaNext\n      rw [hl]',
    '      dsimp only\n      simp only [polyaNext, hl]')
addition=addition.replace('    field_simp\n    ring', '    field_simp <;> ring')
addition=addition.replace('  field_simp\n  ring', '  field_simp <;> ring')
write(RUN/'moments-addition-v2.lean.txt',addition)
ending='end BanditRL.OnlineLearning.GuessingLower';source=PUBLIC.read_text(encoding='utf-8')
write(RUN/'leaves/moments-v2.lean',source[:source.rindex(ending)]+addition+'\n'+ending+'\n')
gate('moments-attempt-v2','lake','env','lean',RUN/'leaves/moments-v2.lean')
