from common import *
fixed()
st=load(CONTRACT/'stabilized-v1.json'); t=st['targets'][2]
assert load(RUN/'fixed-sharp-focused-inspected-v1.json')['compiled']
assert sha(PUBLIC)==load(RUN/'fixed-sharp-focused-inspected-v1.json')['module_sha256']
assert sha(RUN/'first-leaf-BODY-review-v1.json')=='819edcf10959fdb53232abfbcc61f90ca466e9efe2cebd87bfee41a2ebf1c656'
old=PUBLIC.read_bytes(); write(RUN/'pre-variable-public-v1.lean',old)
event('native-fixed-focused-compiled-v1','focused-compiled',dict(leaf=st['targets'][1]['declaration'],module_sha256=sha(PUBLIC),build_actual_exit=0,concrete_canary='pending',whole_Goal_status='ACTIVE'))
event('native-variable-sharp-proving-v1','proving',dict(leaf=t['declaration'],statement_sha256=t['statement_sha256'],dependency='actual shared sum; canonical weighted_potential_sum',whole_Goal_status='ACTIVE'))
body='''  have hsum := iterate_divergence_sum V X hV ψ hd η loss x0 x T
    hseq hinterior hη hf hs u hu
  have hp := BanditRL.OnlineGradientDescent.weighted_potential_sum
    (fun t => 2 * divergence ψ u (x t)) η (2 * M) T hT hη hmono
    (fun t ht => mul_le_mul_of_nonneg_left (hbound t ht) (by norm_num))
  have htwo : (2 : ℝ) ≠ 0 := by norm_num
  simp only [← mul_sub, mul_div_mul_left _ _ htwo] at hp
  exact hsum.trans (sub_le_sub_right hp _)
'''
footer='end BanditRL.OnlinePrescientBregman\n'
text=old.decode('utf8'); assert text.endswith(footer)
PUBLIC.write_bytes((text[:-len(footer)]+t['exact_header']+' := by\n'+body+'\n'+footer).encode('utf8'))
assert PUBLIC.read_bytes().startswith(old[:-len(footer.encode())])
write(RUN/'variable-worker-attempt-v1.md','# Frozen variable sharp\n\nReuse existing canonical weighted_potential_sum with a=2*ordereddivergence and C=2*M. Cancel only nonzero2; eta positive and monotonicity are exact played-index premises, previous-statebound excludesterminal. Signed M/divergence allowed. Same actual sharedsum, bothnegative terminal and weightedmovements retained. First/fixed proofs and allfrozenheaders unchanged.\n')
write(RUN/'variable-public-before-build-v1.lean',PUBLIC.read_bytes())
capture('variable-sharp-statement-fence-v1',sys.executable,'-B','-X','utf8','tools/bandit.py','statement-fence','--declaration',t['declaration'],'--file',PUBLIC.relative_to(ROOT),'--output',CONTRACT/'variable-sharp-fence-v1.json')
code,out=capture('variable-sharp-focused-build-v1','lake','build','BanditRLProof.OnlinePrescientBregmanRegret',required=False)
passed=code==0 and 'Built BanditRLProof.OnlinePrescientBregmanRegret' in out and 'Build completed successfully' in out
write(RUN/'variable-sharp-focused-inspected-v1.json',dict(actual_exit=code,compiled=passed,new_module_Built_marker='Built BanditRLProof.OnlinePrescientBregmanRegret' in out,module_sha256=sha(PUBLIC),prior_BODIES_preserved=True,frozen_target_sha256=t['statement_sha256'],canary='pending',whole_Goal_status='ACTIVE'))
print(out[-1900:])
if passed:
    capture('variable-sharp-safe-verify-v1',sys.executable,'-B','-X','utf8','tools/bandit.py','safe-verify','--fence',CONTRACT/'variable-sharp-fence-v1.json')
else:
    event('native-variable-repair-v1','repair',dict(leaf=t['declaration'],actual_exit=code,terminal_unchanged=True,evidence='variable-sharp-focused-build-v1.json'))
fixed()
assert passed
