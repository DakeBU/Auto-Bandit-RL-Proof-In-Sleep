from proof_driver import *
assert load(RUN/'unique-attempt-v1-inspected.json')['compiled_module_markers']
body='''  intro t
  induction t with
  | zero =>
      intro _
      simp only [iterate, hinit]
  | succ t ih =>
      intro ht
      have hlt : t < T := Nat.lt_of_succ_le ht
      have hprev : t ≤ T := Nat.le_of_lt hlt
      change (iterate V ψ η loss x0 t).bind (advance V ψ (η t) (loss t)) =
        some (x (t + 1))
      rw [ih hprev]
      simp only [Option.bind_some]
      exact advance_eq_some_of_minimizer V X hV hVX ψ hψ (loss t)
        (hf t hlt) (hs t hlt) (η t) (hη t hlt) (x t) (x (t + 1))
        (hmin t hlt).1 (hmin t hlt).2
'''
assert append_proof(3,'identity-attempt-v1',body)
