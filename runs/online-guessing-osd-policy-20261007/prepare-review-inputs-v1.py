from common_v1 import *
fixed()
def capture(label,args):gate(label,*args)
capture('local-semantic-search-v1-01',['rg','-n','regret_tuned|example_2_32|loss_subgradient_bound|SupportPolicy','BanditRLProof','-g','OnlineGuessing*.lean','-g','OnlineSubgradientPolicy.lean'])
capture('mathlib-semantic-search-v1-01',['rg','-n','tendsto_sqrt_atTop|tendsto_inv_atTop_zero|abs_le','\.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Sqrt.lean'.lstrip('\\'),'.lake/packages/mathlib/Mathlib/Topology/Algebra/Order/Field.lean'])
write(RUN/'reuse-decision-v1.md','Actual scoped rg/compiled exact declaration probe: project contains canonical12 Example2.32 declarations, true generic21 history-policy recurrence and sharp/tuned guarantees; no preexisting arbitrary-policy absolute-loss terminal. New4 adapt existing dependencies; do not duplicate any loss/domain/history/support definition. Mathlib reciprocal-square-root limits are actual checked imports. Pinned lakefile requires only mathlib4.29.1 plus transitive dependencies; LML/Optlib are not pinned compatible dependencies here, no unrebuilt external theorem is claimed. Initial literal wildcard path rg read failed under Windows; corrected scoped -g query is retained. No source statement or target was changed for these retrieval corrections.')
targets=load(CONTRACT/'headers-v1.json')
context=(CONTRACT/'public-context-v1.txt').read_text(encoding='utf-8')
actual=[]
for i,(n,h) in enumerate(targets.items(),1):
 args,c=h[len('theorem '+n):].rsplit(' :\n',1)
 actual.append('def S%02d : Prop :=\n  ∀'%i+args+',\n'+c)
actualtext=context+'\n\n'.join(actual)+'\nend BanditRL.OnlineGuessingSubgradientPolicy\n'
neutral=(RUN/'leaves/neutral-types-v2.lean').read_text(encoding='utf-8')
bridge=neutral+'\n'+actualtext
for i in range(1,5):bridge+=f'example : NeutralScalarHistory.Q{i:02d} = BanditRL.OnlineGuessingSubgradientPolicy.S{i:02d} := rfl\n'
write(RUN/'leaves/actual-neutral-type-bridge-v1.lean',bridge)
gate('actual-neutral-type-bridge-v1-01','lake','env','lean',RUN/'leaves/actual-neutral-type-bridge-v1.lean')
write(RUN/'type-bridge-v1.json',dict(status='all-four-complete-closed-types-kernel-equal-under-explicit-map',neutral_type_file_sha256=sha(RUN/'leaves/neutral-types-v2.lean'),headers_sha256=sha(CONTRACT/'headers-v1.json'),bridge_sha256=sha(RUN/'leaves/actual-neutral-type-bridge-v1.lean'),actual_command_receipt=RUN.joinpath('actual-neutral-type-bridge-v1-01-exit.json').as_posix(),target_proofs=False,source_fidelity=False,statement_change=False))
write(RUN/'review-scope-v1.md','Contract-only review before production theorem body: actual frozen full four header types/source/signature/DAG/conversion/localAPI/reuse/neutral blind. Search for mismatch, not confirmation. Existing canonical12 are dependency evidence, not new proof growth or silently reaccepted old publication. Source all3 abs support branches and any-support Algorithm2.2 must match actual played policy and same-run eta. New finite sqrtT/one-sided eventual are explicit consequences of source asymptotic example/transfer. Old required publication/nineOTHERChapter1/remaining chapters stay open. Mandatory distinct actors, no human/external/runtimemodel attestation. No fullsource semantics enforced by CLI alone.')
print('Actual public and neutral closed types match, no theorem proof body. Source review awaiting distinct blind reconstruction.')
