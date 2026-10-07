"""Compare compiled neutral context under an explicitly audited dependency renaming."""
from common_v2 import *
fixed();assert load(RUN/'repair-neutral-binders-v2-01-exit.json')['exit_code']!=0
new=(RUN/'leaves/neutral-propositions-v2.lean').read_text(encoding='utf-8')
mapping=load(RUN/'neutral-to-actual-map-v1.json')['rows']
names=['Domain','SubdifferentiableOn','currentSubgradient','step','iterate','regret']
meta='''
open Lean Meta Elab Command in
run_meta do
  let env ← getEnv
  let deps : Array (Name × Name) := #[
'''+',\n'.join('    (`NeutralUpdate.'+n+', `BanditRL.OnlineSubgradientDescent.'+n+')' for n in names)+''']
  let renameDeps (e : Expr) : Expr := e.replace fun x => match x with
    | .const n ls => match deps.find? (fun p => p.1 == n) with
      | some p => some (.const p.2 ls)
      | none => none
    | _ => none
  for (neutral, actual) in deps do
    let some ai := env.find? actual | throwError "missing actual dependency {actual}"
    let some ni := env.find? neutral | throwError "missing neutral dependency {neutral}"
    unless ← isDefEq ai.type (renameDeps ni.type) do
      throwError "DEPENDENCY TYPE MISMATCH {actual}: {ai.type}; {renameDeps ni.type}"
    let some av := ai.value? | throwError "missing actual definition value {actual}"
    let some nv := ni.value? | throwError "missing neutral definition value {neutral}"
    unless ← isDefEq av (renameDeps nv) do
      throwError "DEPENDENCY VALUE MISMATCH {actual}: {av}; {renameDeps nv}"
    logInfo m!"DEPENDENCY_TYPE_VALUE_MATCH {actual} = {neutral}"
  let rec closeLambdas : Expr → Expr
    | .lam n t b bi => .forallE n t (closeLambdas b) bi
    | e => e
  let pairs : Array (Name × Name) := #[
'''+',\n'.join('    (`'+x['actual_name']+', `NeutralUpdate.'+x['neutral_name']+')' for x in mapping)+''']
  for (actual, neutral) in pairs do
    let some ai := env.find? actual | throwError "missing actual {actual}"
    let some ni := env.find? neutral | throwError "missing neutral {neutral}"
    let some nv := ni.value? | throwError "missing proposition description {neutral}"
    unless ← isDefEq ai.type (renameDeps (closeLambdas nv)) do
      throwError "FULL CONTEXT MISMATCH {actual}: {ai.type}; {renameDeps (closeLambdas nv)}"
    logInfo m!"FULL_CONTEXT_MATCH {actual} = {neutral}"
'''
write(RUN/'leaves/full-context-comparison-v3.lean','import BanditRLProof.OnlineSubgradientDescent\nimport Lean\n'+new+'\n'+meta)
write(RUN/'neutral-comparison-repair-v3.json',dict(M4='Version2 compared independently named recursive iterate constants directly. The first3 checks passed, iterate_mem failed. Version3 audits compiled type AND value of all6 dependency definitions under explicit neutral-to-actual dependency renaming, then compares all15 complete compiled proposition types under exactly that renaming. This is not literal equality of independently named recursive constants.',original_failed_v2_probe_and_logs_preserved=True,probe_sha256=sha(RUN/'leaves/full-context-comparison-v3.lean'),neutral_scoped_context_version=2,public_and_canary_unchanged=True,new_proofs=0,source_review_pending=True))
gate('full-context-comparison-v3-01','lake','env','lean',RUN/'leaves/full-context-comparison-v3.lean')
raw=(RUN/'full-context-comparison-v3-01.log').read_text(encoding='utf-8');assert raw.count('FULL_CONTEXT_MATCH ')==15 and raw.count('DEPENDENCY_TYPE_VALUE_MATCH ')==6
write(RUN/'neutral-to-actual-map-v3.json',dict(rows=mapping,status='actual15 full-context comparisons passed under6 independently type/value-audited dependency renamings',all15_exact_actual_types_preserved=True,actual_evidence='full-context-comparison-v3-01.log',comparison_method='Lean.Meta.isDefEq after explicit6 dependency renamings; actual compiled type AND value of each dependency checked separately',PUBLIC_sha256=sha(PUBLIC),CANARY_sha256=sha(CANARY),actual_target_header_version=2,neutral_context_version=2,neutral_definitions_are_Prop_descriptions_not_proofs=True,prior_wrong_mapping_and_failed_unmapped_comparison_preserved=True))
intro=(RUN/'blind-packet-v1.md').read_text(encoding='utf-8').split('```lean',1)[0].replace('blind-reconstruction-v1.md','blind-reconstruction-v2.md').replace('blind-receipt-v1.json','blind-receipt-v2.json')
intro+='\nNeutral packet version2: every proposition explicitly retains a finite-dimensional real-space parameter. Reconstruct all15 afresh from this packet alone. No source/proof/prior verdict is supplied. Standalone elaboration below is context evidence only.\n\n'
write(RUN/'blind-packet-v2.md',intro+'```lean\n'+new+'\n```\nActual standalone elaboration:\n```text\n'+(RUN/'neutral-propositions-v2-01.log').read_text(encoding='utf-8')+'\n```\n')
event('repair',dict(kind='neutral missing FD context and independently named recursion comparison',repair=(RUN/'neutral-comparison-repair-v3.json').as_posix(),actual15_context_comparisons_under6_audited_definition_renamings=True,headers_unchanged=True,distinct_reconstruction_and_separate_M3_M4_review_pending=True),attempt='neutral-v3')
fixed();print('Actual6 compiled dependency types/values and15 full target contexts match under explicit renaming. Fresh neutral2 blind/source repair reviews pending; original rejected and failed evidence preserved.')
