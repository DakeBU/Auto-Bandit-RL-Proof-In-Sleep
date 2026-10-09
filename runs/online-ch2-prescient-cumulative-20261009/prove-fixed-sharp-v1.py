from common import *
fixed()
review=RUN/'first-leaf-BODY-review-v1.json'
assert sha(review)=='819edcf10959fdb53232abfbcc61f90ca466e9efe2cebd87bfee41a2ebf1c656'
r=load(review); assert r['verdict']=='accepted-with-explicit-delta' and not r['required_repairs']
st=load(CONTRACT/'stabilized-v1.json'); t=st['targets'][1]
old=PUBLIC.read_bytes(); write(RUN/'pre-fixed-public-v1.lean',old)
assert sha(PUBLIC)==load(RUN/'first-leaf-public-inspected-v2.json')['module_sha256']
event('native-fixed-sharp-proving-v1','proving',dict(leaf=t['declaration'],statement_sha256=t['statement_sha256'],first_leaf_BODY_review_sha256=sha(review),dependency='actual compiled iterate_divergence_sum',whole_Goal_status='ACTIVE'))
body='''  have h := iterate_divergence_sum V X hV ψ hd (fun _ => η) loss x0 x T
    hseq hinterior (fun _ _ => hη) hf hs u hu
  have hx : x 0 = x0 := (Option.some.inj (hseq 0 (Nat.zero_le T))).symm
  simpa only [← sum_div, sum_range_sub', hx, sub_div] using h
'''
footer='end BanditRL.OnlinePrescientBregman\n'
text=old.decode('utf8'); assert text.endswith(footer)
PUBLIC.write_bytes((text[:-len(footer)]+t['exact_header']+' := by\n'+body+'\n'+footer).encode('utf8'))
assert PUBLIC.read_bytes().startswith(old[:-len(footer.encode())])
write(RUN/'fixed-worker-attempt-v1.md','# Frozen fixed sharp\n\nSourceactualinitialpoint identity comes from hseq at0, not an unrelated trace. Canonicalsum_div/sum_range_sub telescope constanteta; bothnegative terminal and totalmovement remain. First acceptedBODY unchanged, exactfrozenheader unchanged, Tallows0.\n')
write(RUN/'fixed-public-before-build-v1.lean',PUBLIC.read_bytes())
capture('fixed-sharp-statement-fence-v1',sys.executable,'-B','-X','utf8','tools/bandit.py','statement-fence','--declaration',t['declaration'],'--file',PUBLIC.relative_to(ROOT),'--output',CONTRACT/'fixed-sharp-fence-v1.json')
code,out=capture('fixed-sharp-focused-build-v1','lake','build','BanditRLProof.OnlinePrescientBregmanRegret',required=False)
passed=code==0 and 'Built BanditRLProof.OnlinePrescientBregmanRegret' in out and 'Build completed successfully' in out
write(RUN/'fixed-sharp-focused-inspected-v1.json',dict(actual_exit=code,compiled=passed,new_module_Built_marker='Built BanditRLProof.OnlinePrescientBregmanRegret' in out,module_sha256=sha(PUBLIC),first_BODY_preserved=True,frozen_target_sha256=t['statement_sha256'],canary='pending',whole_Goal_status='ACTIVE'))
print(out[-1900:])
if passed:
    capture('fixed-sharp-safe-verify-v1',sys.executable,'-B','-X','utf8','tools/bandit.py','safe-verify','--fence',CONTRACT/'fixed-sharp-fence-v1.json')
else:
    event('native-fixed-repair-v1','repair',dict(leaf=t['declaration'],actual_exit=code,terminal_unchanged=True,evidence='fixed-sharp-focused-build-v1.json'))
fixed()
assert passed
