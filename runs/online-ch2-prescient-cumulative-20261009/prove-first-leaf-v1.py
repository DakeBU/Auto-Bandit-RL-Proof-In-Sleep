from common import *
fixed()
target=load(CONTRACT/'stabilized-v1.json')['targets'][0]
body='''  have hstep (t : ℕ) (ht : t ∈ range T) :
      (loss t (x (t + 1))).toReal - (loss t u).toReal ≤
        (divergence ψ u (x t) - divergence ψ u (x (t + 1))) / η t -
          divergence ψ (x (t + 1)) (x t) / η t := by
    have hlt : t < T := mem_range.mp ht
    have hle : t + 1 ≤ T := Nat.succ_le_of_lt hlt
    have a := iterate_one_step V hV ψ η loss x0 (x t) (x (t + 1)) t
      (hseq t (Nat.le_of_lt hlt)) (hseq (t + 1) hle) (hη t hlt)
      (hf t hlt) (hs t hlt)
      (hd.differentiableAt (isOpen_interior.mem_nhds (hinterior t (Nat.le_of_lt hlt))))
      (hd.differentiableAt (isOpen_interior.mem_nhds (hinterior (t + 1) hle))) u hu
    rw [← sub_div]
    apply (le_div_iff₀ (hη t hlt)).mpr
    simpa only [mul_comm] using a
  have hsum := Finset.sum_le_sum (s := range T) hstep
  simpa only [sum_sub_distrib] using hsum
'''
write(RUN/'first-leaf-worker-attempt-v1.md','# Selected first leaf\n\nExact stabilized target '+target['statement_sha256']+'. Actual parent iterate_one_step consumes consecutive successful states, sourceinterior supplies actual ambient derivatives. Divide positive eta, distribute finite sum. No desiredbound assumed; only newfilebody is written. Focused build/fence/declvalue/axiom evidence follows, not auto accepted.\n')
context=load(CONTRACT/'stabilized-v1.json')['context']
write(PUBLIC,context+'\n'+target['exact_header']+' := by\n'+body+'\nend BanditRL.OnlinePrescientBregman\n')
assert target['exact_header'] in PUBLIC.read_text(encoding='utf8')
write(RUN/'first-leaf-source-before-build-v1.json',dict(module_sha256=sha(PUBLIC),frozen_header_sha256=target['statement_sha256'],source_snapshot=PUBLIC.read_text(encoding='utf8'),compiled=False))
capture('first-leaf-statement-fence-v1',sys.executable,'-B','-X','utf8','tools/bandit.py','statement-fence','--declaration',target['declaration'],'--file',PUBLIC.relative_to(ROOT),'--output',CONTRACT/'first-leaf-fence-v1.json')
code,out=capture('first-leaf-focused-build-v1','lake','build','BanditRLProof.OnlinePrescientBregmanRegret',required=False)
passed=code==0 and 'Built BanditRLProof.OnlinePrescientBregmanRegret' in out and 'Build completed successfully' in out
write(RUN/'first-leaf-focused-inspected-v1.json',dict(actual_exit=code, actual_new_module_built_marker='Built BanditRLProof.OnlinePrescientBregmanRegret' in out,build_completed_marker='Build completed successfully' in out, compiled=passed, proof_sha256=sha(PUBLIC),source_container_closed=False,chapter_complete=False,whole_Goal_status='ACTIVE'))
print(out[-3200:])
if not passed:
    event('native-first-leaf-repair-event-v1','repair',dict(leaf=target['declaration'],actual_exit=code,evidence='first-leaf-focused-build-v1.json',terminal_unchanged=True,whole_Goal_status='ACTIVE'))
else:
    capture('first-leaf-safe-verify-v1',sys.executable,'-B','-X','utf8','tools/bandit.py','safe-verify','--fence',CONTRACT/'first-leaf-fence-v1.json')
fixed()
assert passed,'First focused build failed; exact raw compiler receipt retained.'
