from common_v1 import *
fixed(True);assert load(RUN/'focused-v1-exit.json')['exit_code']==1
old=CANARY.read_bytes();write(RUN/'leaves/failed-canary-body-v1.lean',old)
text=old.decode('utf-8');needle='''      ∑ t ∈ Finset.range 2, demoLoss t (leader 2) := by
  norm_num [demoLoss, Finset.sum_range_succ]'''
replacement='''      ∑ t ∈ Finset.range 2, demoLoss t (leader 2) := by
  dsimp only
  constructor
  · intro n hn hnt
    exact Set.mem_univ _
  · norm_num [demoLoss, Finset.sum_range_succ]'''
assert text.count(needle)==1
text=text.replace(needle,replacement)
headers=lambda s:{m.group(1):m.group(0).strip() for m in re.finditer(r'(?m)^theorem (\w+)\b[\s\S]*?(?= := by\b)',s)}
assert headers(text)==headers(old.decode('utf-8'))==load(CONTRACT/'planned-canary-headers-v1.json')
write(RUN/'canary-body-repair-v2.json',dict(kind='Proof body only; mathematical contract remains v1',failed_body_snapshot=(RUN/'leaves/failed-canary-body-v1.lean').as_posix(),failed_body_sha256=sha(RUN/'leaves/failed-canary-body-v1.lean'),failed_gate_sha256=sha(RUN/'focused-v1-exit.json'),error='norm_num unfolded Bool universal-set membership to unresolved excluded middle forall n, not a false target',repair='Prove feasible membership directly with Set.mem_univ, then separately normalize numerical failure witness.',all_seven_headers_unchanged=True,source_public_statement_body_unchanged=True,original_failure_retained=True,compile_state='pending actual focused-v2'))
native('failed-worker-trial-v1','trial-log','--task',TASK,'--role','lower','--kind','build','--status','failed','--run-id',RUN.name,'--attempt-id','FOUNDATIONS-NAMED-CANARY-V1','--lean',CANARY,'--statement-hash',fixed(True)['native_header_hash'],'--verifier-evidence',RUN/'focused-v1-exit.json','--harness','hierarchical','--progress-class','diagnostic','--error-signature','Bool-univ-membership-normalization-excluded-middle','--notes','Frozen public/seven test targets unchanged. Original failed body/log retained; routine proof-only repair returns membership to direct Set.mem_univ before numeric normalization.')
CANARY.write_bytes(text.encode('utf-8'))
gate('focused-v2','lake','build','BanditRLProof.OnlineLearningFoundations','Tests.OnlineLearningFoundationsCanary')
original=(RUN/'prove-and-check-v1.py').read_text(encoding='utf-8')
remaining=original[original.index("names=[PRE+'lemma_1_2']"):].replace("RUN/'focused-v1.log'","RUN/'focused-v2.log'")
write(RUN/'continue-checks-v2.py','from common_v1 import *\nfixed(True)\nplan=load(CONTRACT/\'planned-canary-headers-v1.json\')\n'+remaining)
subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'continue-checks-v2.py')],check=True)
fixed(True);print('Actual proof-only repair and unchanged v1 targets pass; original failed attempt retained.')
