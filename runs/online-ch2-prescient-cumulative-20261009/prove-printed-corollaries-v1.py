from common import *
fixed()
review=RUN/'three-BODY-canary-CONTRACT-review-v1.json'
assert sha(review)=='e3d0d9738b180eb1ad437e9fef3c975f0dd19cebf958098188d78a8bdcb7cecb'
r=load(review); assert r['verdict']=='accepted-with-explicit-delta' and not r['required_repairs']
st=load(CONTRACT/'stabilized-v1.json')
assert sha(PUBLIC)==load(RUN/'three-proof-public-inspected-v1.json')['module_sha256']
write(CONTRACT/'canary-stabilized-v1.json',dict(stage='stabilized',**{k:v for k,v in load(CONTRACT/'canary-targets-draft-v1.json').items() if k!='stage'},CONTRACT_review_sha256=sha(review),decoder_sha256=sha(RUN/'canary-blind-reconstruction-v1.json'),allowed_file='Tests/OnlinePrescientBregmanRegretCanary.lean',edit_boundary='Exact two complete conjunction bodies and necessary imports only. No new named helpers; numeric branches retain required new production proof VALUES. No root/reader/site/publication before separate integration review.'))
bodies=['''  have h := iterate_fixed_sharp V X hV ψ hd η hη loss x0 x T
    hseq hinterior hf hs u hu
  have hterminal := divergence_nonneg X ψ hc.convexOn u (x T) (hVX hu)
    (interior_subset (hinterior T le_rfl))
    (hd.differentiableAt (isOpen_interior.mem_nhds (hinterior T le_rfl)))
  have hquot : 0 ≤ divergence ψ u (x T) / η := div_nonneg hterminal hη.le
  linarith only [h, hquot]
''','''  let M : ℝ := (range T).sup' (nonempty_range_iff.mpr (Nat.ne_of_gt hT))
    (fun t => divergence ψ u (x t))
  have hbound (t : ℕ) (ht : t < T) : divergence ψ u (x t) ≤ M :=
    Finset.le_sup' (fun t => divergence ψ u (x t)) (mem_range.mpr ht)
  have h := iterate_variable_sharp V X hV ψ hd η loss x0 x T hT
    hseq hinterior hη hmono hf hs u hu M hbound
  have hterminal := divergence_nonneg X ψ hc.convexOn u (x T) (hVX hu)
    (interior_subset (hinterior T le_rfl))
    (hd.differentiableAt (isOpen_interior.mem_nhds (hinterior T le_rfl)))
  have hlast : T - 1 < T := Nat.sub_lt hT (by omega)
  have hquot : 0 ≤ divergence ψ u (x T) / η (T - 1) :=
    div_nonneg hterminal (hη (T - 1) hlast).le
  change _ ≤ M / η (T - 1) - _
  linarith only [h, hquot]
''']
footer='end BanditRL.OnlinePrescientBregman\n'
for i,(t,body) in enumerate(zip(st['targets'][3:],bodies)):
    label=['fixed-printed','variable-printed'][i]
    write(RUN/('pre-'+label+'-native-exact-v1.json'),dict(rows=[dict(path=p.as_posix(),sha256=sha(p),raw_base64=base64.b64encode(p.read_bytes()).decode('ascii')) for p in [RUN/'lifecycle-sessions.jsonl',RUN/'lifecycle-state.json',RUN/'trials.jsonl',RUN/'own-artifact-journal.md'] if p.exists()]))
    old=PUBLIC.read_bytes(); write(RUN/('pre-'+label+'-public-v1.lean'),old)
    event('native-'+label+'-proving-v1','proving',dict(leaf=t['declaration'],statement_sha256=t['statement_sha256'],BODY_progression_review_sha256=sha(review),terminal_nonnegative='Actual interior derivative plus convexity on X',whole_Goal_status='ACTIVE'))
    text=old.decode('utf8'); assert text.endswith(footer)
    PUBLIC.write_bytes((text[:-len(footer)]+t['exact_header']+' := by\n'+body+'\n'+footer).encode('utf8'))
    assert PUBLIC.read_bytes().startswith(old[:-len(footer.encode())])
    write(RUN/(label+'-public-before-build-v1.lean'),PUBLIC.read_bytes())
    capture(label+'-statement-fence-v1',sys.executable,'-B','-X','utf8','tools/bandit.py','statement-fence','--declaration',t['declaration'],'--file',PUBLIC.relative_to(ROOT),'--output',CONTRACT/(label+'-fence-v1.json'))
    code,out=capture(label+'-focused-build-v1','lake','build','BanditRLProof.OnlinePrescientBregmanRegret',required=False)
    passed=code==0 and 'Built BanditRLProof.OnlinePrescientBregmanRegret' in out and 'Build completed successfully' in out
    write(RUN/(label+'-focused-inspected-v1.json'),dict(actual_exit=code,compiled=passed,new_module_Built_marker='Built BanditRLProof.OnlinePrescientBregmanRegret' in out,module_sha256=sha(PUBLIC),prior_BODIES_preserved=True,frozen_target_sha256=t['statement_sha256'],concrete_canary='pending',whole_Goal_status='ACTIVE'))
    if passed:
        capture(label+'-safe-verify-v1',sys.executable,'-B','-X','utf8','tools/bandit.py','safe-verify','--fence',CONTRACT/(label+'-fence-v1.json'))
    else:
        print(out[-3000:])
        event('native-'+label+'-repair-v1','repair',dict(leaf=t['declaration'],actual_exit=code,terminal_unchanged=True,evidence=label+'-focused-build-v1.json'))
    fixed()
    assert passed,label
write(RUN/'printed-worker-attempts-v1.md','# Frozen printed corollaries\n\nEach exactsharp reused; terminaldivergence proven nonnegative from StrictConvexOn.convexOn, feasiblecomparatorinX, terminalininteriorX and actual ambientderivative. Only then dropnegative terminal. Variableactualnonemptyfinite range maximum supplies M via Finset.le_sup\x27; no geometricdiameter or initial-onlymaximum substituted. Allpreviousbodies/5exactheaders unchanged, everymovement retained. Both actual focused builds/nativeguards passed; canaries/fullintegration stillpending.\n')
print('Five exact production proof bodies now focused-compiled; two full canary bodies remain pending.')
