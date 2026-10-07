from common_v1 import *
fixed();assert load(RUN/'first-public-leaf-safe-v2-01-exit.json')['exit_code']==0
assert PUBLIC.read_bytes()==(RUN/'leaves/first-public-leaf-v1.lean.txt').read_bytes()
targets=load(CONTRACT/'headers-v1.json')
bodies={
'selected_bound':'''  exact loss_subgradient_bound (y t) _ _ (hlegal t ht)''',
'step_clamp':'''  simp only [output_succ, BanditRL.OnlineGradientDescent.project_unitInterval, smul_eq_mul]''',
'example_2_32':'''  have hdiam : ∀ x ∈ unitInterval.carrier,
      ∀ z ∈ unitInterval.carrier, ‖x - z‖ ≤ (1 : ℝ) := by
    intro x hx z hz
    change x ∈ Icc (0 : ℝ) 1 at hx
    change z ∈ Icc (0 : ℝ) 1 at hz
    change |x - z| ≤ 1
    exact abs_le.mpr ⟨by linarith [hx.1, hz.2], by linarith [hx.2, hz.1]⟩
  have hlegal' : LegalFeedback unitInterval (fun _ => 1 / (1 * Real.sqrt T))
      (fun s => loss (y s)) x₁ p T := by
    simpa only [one_mul] using hlegal
  have hb := BanditRL.OnlineSubgradientPolicy.regret_tuned unitInterval
    (fun s => loss (y s)) x₁ p hx₁ T hT 1 1 (by norm_num) (by norm_num)
    (fun t ht => loss_on_unitInterval (y t)) hlegal' hdiam
    (fun t ht => by
      simpa only [one_mul] using
        selected_bound (fun _ => 1 / Real.sqrt T) y x₁ p T hlegal t ht)
  simpa only [BanditRL.OnlineSubgradientPolicy.regret, loss, EReal.toReal_coe, one_mul]
    using hb''',
'example_2_32_average_eventually':'''  have hlimit : Tendsto (fun T : ℕ => (Real.sqrt (T : ℝ))⁻¹) atTop (nhds (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hsmall := hlimit.eventually (eventually_lt_nhds hε)
  filter_upwards [hsmall, eventually_gt_atTop (0 : ℕ)] with T hsmall hT
  have ht : 0 < (T : ℝ) := Nat.cast_pos.mpr hT
  have hs : 0 < Real.sqrt (T : ℝ) := Real.sqrt_pos.mpr ht
  have hb := example_2_32 y x₁ p hx₁ T hT (fun t ht => hy t) (hlegal T hT) u hu
  calc
    (∑ t ∈ range T,
      (|output unitInterval (fun _ => 1 / Real.sqrt T)
        (fun s => loss (y s)) x₁ p t - y t| - |u - y t|)) / T ≤ Real.sqrt T / T :=
        div_le_div_of_nonneg_right hb (Nat.cast_nonneg T)
    _ = (Real.sqrt T)⁻¹ := by
      rw [inv_eq_one_div]
      apply (div_eq_div_iff (ne_of_gt ht) (ne_of_gt hs)).mpr
      nlinarith [Real.sq_sqrt (Nat.cast_nonneg T)]
    _ < ε := hsmall'''
}
write(RUN/'worker-terminal-v1.md','ROOT staged worker requested medium. First norm leaf compiled3324jobs/nativeguardv2 passed. Next dependency-ready clamp derives actual projection identity; finite terminal uses actual normproducer/trueintervaldiameter and shared tuned producer on exactly same eta; one-sided average consumes finite terminal/positiveT and reciprocal sqrt limit. hlegal/hy/quantifiers frozen, no replacement consumer/trajectory or offpath assumption. Full public module focused gate below does not certify newcanary/semanticBODY/combined/reader/chapter.')
native('proving-terminals-event-v1-01','lifecycle-event','--session',TASK,'--event','proving','--payload-json',json.dumps(dict(run_id=RUN.name,contract_version=1,leaf='Same-run Example2.32 terminal then dependent eventual upper-average',first_leaf_verifier=RUN.joinpath('first-public-leaf-focused-v1-01-exit.json').as_posix(),single_lower_route=True,chapter_complete=False,goal_complete=False)))
text=(CONTRACT/'public-context-v1.txt').read_text(encoding='utf-8')+'''\n/-!
Example2.32 in Orabona arXiv1912.13213v10, printed20/PDF32.
Reuse the shared absolute loss, unit interval and actual projected finite-history
policy recursion. Every played legal support is allowed, including historical
choices in the full tie interval. Performance uses this same eta=1/sqrtT run,
not a supplied regret inequality or a universal off-path oracle premise.
The exact finite sqrtT bound specializes the source OSD transfer at D=G=1.
The last theorem is only eventual upper average over separately prescribed
horizons, not signed convergence to zero or one anytime run.
Broader norm/clamp algebra permits arbitrary initialization/labels/rates;
the tuned source game retains feasible labels/initialization and positive T.
-/\n\n'''
text+='\n\n'.join(h+' := by\n'+bodies[n] for n,h in targets.items())+'\n\nend BanditRL.OnlineGuessingSubgradientPolicy\n'
write(RUN/'leaves/full-public-body-v1.lean.txt',text);PUBLIC.write_bytes(text.encode('utf-8'))
headers()
gate('full-public-focused-v1-01','lake','build','BanditRLProof.OnlineGuessingSubgradientPolicy')
for n in targets:
 fence=RUN/'native-public-fences'/(n+'-full-v1.json')
 native('full-public-fence-'+n+'-v1','statement-fence','--declaration','BanditRL.OnlineGuessingSubgradientPolicy.'+n,'--file',PUBLIC,'--output',str(fence))
 native('full-public-safe-'+n+'-v1','safe-verify','--fence',str(fence),'--lean-file',PUBLIC)
write(RUN/'public-terminal-focused-v1.json',dict(status='four-new-public-bodies-compiled-and-frozen',new_proofs=4,new_definitions=0,public_raw_sha256=sha(PUBLIC),unchanged_headers_sha256=sha(CONTRACT/'headers-v1.json'),focused_receipt=RUN.joinpath('full-public-focused-v1-01-exit.json').as_posix(),source_contract=r['verdict'] if False else 'accepted-with-explicit-delta',source_body_review='pending',public_canary='pending',root_Tests_harness_site='pending',package_accepted=False,chapter_complete=False,goal_complete=False))
headers();print('Actual full four public bodies compiled/fenced; SAME-RUN finite terminal closed locally; canary/BODY/integrated gates still pending.')
