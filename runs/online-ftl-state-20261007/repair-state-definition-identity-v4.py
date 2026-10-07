from common_v1 import *
fixed(proving=True);assert load(RUN/'state-definition-identities-v1-exit.json')['exit_code']==1
assert PUBLIC.read_text(encoding='utf-8')==(RUN/'leaves/state-definitions-frozen-v1.txt').read_text(encoding='utf-8')+'\nend BanditRL.OnlineLearning\n'
write(RUN/'state-definition-identity-failure-repair-v3.json',dict(failed_gate_sha256=sha(RUN/'state-definition-identities-v1-exit.json'),failed_log_sha256=sha(RUN/'state-definition-identities-v1.log'),cause='Separately named equation-compiler recursive definitions are not definitionally equal by rfl',repair='Prove full function equality extensionally by induction using identical local step; retain rfl checks for nonrecursive mean/predictor/step. No production definition/header change.',mathematical_target_change=False,actual_recursive_definition_unchanged=True,new_production_proofs_not_written=True))
text=(RUN/'leaves/state-definition-identities-v1.lean').read_text(encoding='utf-8')
bad='example : Neutral.d = BanditRL.OnlineLearning.ftlState := by rfl'
assert text.count(bad)==1
good='''theorem neutralStateIdentity : Neutral.d = BanditRL.OnlineLearning.ftlState := by
  funext initial y t
  induction t with
  | zero => rfl
  | succ t ih =>
    change Neutral.c (Neutral.d initial y t) (y t) =
      BanditRL.OnlineLearning.ftlMeanStep (BanditRL.OnlineLearning.ftlState initial y t) (y t)
    rw [ih]
    rfl'''
write(RUN/'leaves/state-definition-identities-v2.lean',text.replace(bad,good))
gate('state-definition-identities-v2','lake','env','lean',RUN/'leaves/state-definition-identities-v2.lean')
assert 'sorryAx' not in (RUN/'state-definition-identities-v2.log').read_text(encoding='utf-8')
defs=load(CONTRACT/'production-definitions-v1.json');prefix=(RUN/'leaves/state-definitions-frozen-v1.txt').read_text(encoding='utf-8')+'\n'
write(RUN/'state-definition-bindings-v1.json',dict(status='Actual3 new complete definitions verified; canonicalMean/predictor/step neutral rfl identities and recursive state function equality by extensional induction compiled; actual3 names/types/kernel checked',full_definition_rows=[dict(name=PRE+n,source_raw_text=h,sha256=hashlib.sha256(h.encode()).hexdigest()) for n,h in defs.items()],actual_module_definition_prefix_sha256=hashlib.sha256(prefix.encode()).hexdigest(),recursive_identity_method='Actual whole-function equality via funext and Nat induction, not rfl',recursive_native_fence_claim=False,native_api_boundary='Equation-style recursion unsupported by native header extractor; full raw bytes plus compiled functional identities/types/kernel are separate evidence',original_failed_recursive_rfl_retained=True,source_package_accepted=False))
text=(RUN/'prove-state-v2.py').read_text(encoding='utf-8');tail=text[text.index('bodies={'):]
write(RUN/'continue-state-v3.py',"from common_v1 import *\nfixed(proving=True)\ndefs=load(CONTRACT/'production-definitions-v1.json');headers=load(CONTRACT/'new-public-headers-v1.json')\nassert load(RUN/'state-definition-bindings-v1.json')['recursive_identity_method'].startswith('Actual whole-function equality')\n"+tail)
fixed(proving=True)
