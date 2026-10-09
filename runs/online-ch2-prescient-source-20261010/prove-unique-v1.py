from proof_driver import *
assert load(RUN/'strict-attempt-v1-inspected.json')['compiled_module_markers']
body='''  classical
  have hfin : ∀ z ∈ V, f z ≠ ⊤ ∧ f z ≠ ⊥ := by
    intro z hz
    obtain ⟨g, hg⟩ := hs z hz
    exact ⟨ne_of_lt (BanditRL.OnlineConvex.subgradient_point_finite f hf z g hg), hf.1 z⟩
  have hstrict := penalized_strictConvex V X hV hVX ψ hψ f hf hs η hη x
  have hpReal := (proximal_finitePart_minimizer_iff f V ψ η x p hp hfin).mp hmin
  have hatt : ∃ q, q ∈ V ∧
      IsMinOn (fun z => f z + ((η⁻¹ * divergence ψ z x : ℝ) : EReal)) V q :=
    ⟨p, hp, hmin⟩
  have hq := Classical.choose_spec hatt
  have hqReal := (proximal_finitePart_minimizer_iff f V ψ η x
    (Classical.choose hatt) hq.1 hfin).mp hq.2
  have heq : Classical.choose hatt = p := hstrict.eq_of_isMinOn hqReal hpReal hq.1 hp
  unfold advance
  rw [dif_pos hatt]
  exact congrArg some heq
'''
assert append_proof(2,'unique-attempt-v1',body)
