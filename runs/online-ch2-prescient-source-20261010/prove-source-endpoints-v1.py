from proof_driver import *
assert load(RUN/'identity-attempt-v1-inspected.json')['compiled_module_markers']
fixed_body='''  have hf (t : ℕ) (ht : t < T) : BanditRL.OnlineConvex.SourceProper (loss t) :=
    BanditRL.OnlineConvex.sourceProper_of_domain (loss t) V hVn (hbot t ht) (hdom t ht)
  have hseq := iterate_eq_of_source_updates V X hV hVX ψ hψ
    (fun _ => η) loss x0 x T hinit (fun _ _ => hη) hf hs hmin
  exact iterate_fixed_regret V X hV hVX ψ hψ hd η hη loss x0 x T
    hseq hinterior hf hs u hu
'''
assert append_proof(4,'source-fixed-attempt-v1',fixed_body)
variable_body='''  have hf (t : ℕ) (ht : t < T) : BanditRL.OnlineConvex.SourceProper (loss t) :=
    BanditRL.OnlineConvex.sourceProper_of_domain (loss t) V hVn (hbot t ht) (hdom t ht)
  have hseq := iterate_eq_of_source_updates V X hV hVX ψ hψ
    η loss x0 x T hinit hη hf hs hmin
  exact iterate_variable_regret V X hV hVX ψ hψ hd η loss x0 x T hT
    hseq hinterior hη hmono hf hs u hu
'''
assert append_proof(5,'source-variable-attempt-v1',variable_body)
write(RUN/'six-production-focused-summary-v1.json',dict(proof_terminals_total=6,focused_compiled=[r['name'] for r in load(CONTRACT/'stabilized-v1.json')['six_targets']],proof_terminal_remaining=0,canary_gate=False,root_Tests_harness=False,semantic_BODY=False,package_accepted=False,chapter_status='partial/null',whole_goal='active',actual_source=rows([PUBLIC]),scope='Six exact own frozen mathematical terminals compile, not chapter/source-container/whole-Goal completion.'))
fixed()
