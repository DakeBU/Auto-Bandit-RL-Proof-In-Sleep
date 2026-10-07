"""Repair actual scoped-type mismatch without editing any public theorem or old evidence."""
from common_v2 import *
fixed();r=load(RUN/'source-contract-receipt-v1.json');assert r['verdict']=='rejected';assert sha(r['report'])==r['report_sha256']
text=(RUN/'leaves/neutral-propositions-v1.lean').read_text(encoding='utf-8')
new,count=re.subn(r'(?m)^def (P\d\d) : Prop :=',r'def \1 [instFD : FiniteDimensional ℝ E] : Prop :=',text);assert count==15
write(RUN/'leaves/neutral-propositions-v2.lean',new)
mapping=load(RUN/'neutral-to-actual-map-v1.json')['rows']
meta='''
open Lean Meta Elab Command in
run_meta do
  let env ← getEnv
  let rec closeLambdas : Expr → Expr
    | .lam n t b bi => .forallE n t (closeLambdas b) bi
    | e => e
  let pairs : Array (Name × Name) := #[
'''+',\n'.join('    (`'+x['actual_name']+', `NeutralUpdate.'+x['neutral_name']+')' for x in mapping)+''']
  for (actual, neutral) in pairs do
    let some actualInfo := env.find? actual | throwError "missing actual {actual}"
    let some neutralInfo := env.find? neutral | throwError "missing neutral {neutral}"
    let some value := neutralInfo.value? | throwError "missing proposition description {neutral}"
    unless ← isDefEq actualInfo.type (closeLambdas value) do
      throwError "FULL CONTEXT MISMATCH {actual}: actual {actualInfo.type}; neutral {closeLambdas value}"
    logInfo m!"FULL_CONTEXT_MATCH {actual} = {neutral}"
'''
probe='import BanditRLProof.OnlineSubgradientDescent\nimport Lean\n'+new+'\n'+meta
write(RUN/'leaves/full-context-comparison-v2.lean',probe)
write(RUN/'neutral-repair-probes-before-use-v2.json',dict(rows=[dict(path=p.as_posix(),sha256=sha(p)) for p in [RUN/'leaves/neutral-propositions-v2.lean',RUN/'leaves/full-context-comparison-v2.lean']],actual_PUBLIC_and_CANARY_unchanged=True,new_proof_bodies=False))
write(RUN/'neutral-context-repair-v2.json',dict(status='repair pending actual re-elaboration/definitional comparison/distinct reconstruction/separate source review',prior_rejected_review='source-contract-receipt-v1.json',prior_rejected_receipt_sha256=sha(RUN/'source-contract-receipt-v1.json'),M3=dict(finding='Neutral P02/P03 inferred no FiniteDimensional binder, although both actual compiled public types retain one. Original all15_exact_actual_types_preserved flag was false for those two.',repair='Explicit FiniteDimensional instance binder on every neutral proposition description, followed by actual compiled-environment definitional equality of complete reified neutral proposition and actual public theorem type for each15.',original_v1_packet_reconstruction_map_and_accepted_compile_output_preserved=True,original_compile_was_successful_proposition_elaboration_not_source_fidelity=True,actual_mathematical_headers_and_PUBLIC_CANARY_bytes_unchanged=True,source_contract_stabilization_v1_rejected=True),metadata_only=True,new_proofs=0,chapter_complete=False,goal_complete=False))
gate('neutral-propositions-v2-01','lake','env','lean',RUN/'leaves/neutral-propositions-v2.lean')
gate('full-context-comparison-v2-01','lake','env','lean',RUN/'leaves/full-context-comparison-v2.lean')
raw=(RUN/'full-context-comparison-v2-01.log').read_text(encoding='utf-8');assert raw.count('FULL_CONTEXT_MATCH ')==15
write(RUN/'neutral-to-actual-map-v2.json',dict(rows=mapping,status='actual15 full-context definitional-equality checks passed',all15_exact_actual_types_preserved=True,actual_evidence='full-context-comparison-v2-01.log',PUBLIC_sha256=sha(PUBLIC),CANARY_sha256=sha(CANARY),actual_target_header_version=2,neutral_context_version=2,neutral_definitions_are_Prop_descriptions_not_proofs=True,prior_wrong_mapping_preserved=True))
packet=(RUN/'blind-packet-v1.md').read_text(encoding='utf-8');intro=packet.split('```lean',1)[0]
intro=intro.replace('blind-reconstruction-v1.md','blind-reconstruction-v2.md').replace('blind-receipt-v1.json','blind-receipt-v2.json')
intro+='\nVersion2 neutral scoped context explicitly retains the finite-dimensional real-space binder for EVERY proposition. Read version2 alone and reconstruct all15 afresh; no proof/source or prior verdict is supplied. Actual elaboration output below is proposition/context evidence only.\n\n'
write(RUN/'blind-packet-v2.md',intro+'```lean\n'+new+'\n```\nActual standalone elaboration:\n```text\n'+(RUN/'neutral-propositions-v2-01.log').read_text(encoding='utf-8')+'\n```\n')
event('repair',dict(kind='neutral compiled scoped-type mismatch',repair=(RUN/'neutral-context-repair-v2.json').as_posix(),actual_15_full_context_comparisons_passed=True,headers_unchanged=True,distinct_reconstruction_and_separate_source_M3_review_pending=True),attempt='neutral-v2')
fixed();print('Actual all15 full-context comparisons pass; original rejected contract/incorrect neutral metadata preserved, fresh neutral2 decoder/source review pending.')
