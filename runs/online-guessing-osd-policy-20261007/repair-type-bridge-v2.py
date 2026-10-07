from common_v1 import *
fixed()
prior=(RUN/'leaves/actual-neutral-type-bridge-v1.lean').read_text(encoding='utf-8')
imports=[];body=[]
for line in prior.splitlines():
 if line.startswith('import '):
  if line not in imports:imports.append(line)
 else:body.append(line)
text='\n'.join(imports+body)+'\n'
write(RUN/'leaves/actual-neutral-type-bridge-v2.lean',text)
gate('actual-neutral-type-bridge-v2-01','lake','env','lean',RUN/'leaves/actual-neutral-type-bridge-v2.lean')
write(RUN/'type-bridge-v2.json',dict(status='all-four-complete-closed-types-kernel-equal-under-explicit-map',neutral_type_file_sha256=sha(RUN/'leaves/neutral-types-v2.lean'),headers_sha256=sha(CONTRACT/'headers-v1.json'),bridge_sha256=sha(RUN/'leaves/actual-neutral-type-bridge-v2.lean'),actual_command_receipt=RUN.joinpath('actual-neutral-type-bridge-v2-01-exit.json').as_posix(),original_failure='actual-neutral-type-bridge-v1-01.log',repair='Move all required imports to beginning of Lean file, keep actual/neutral proposition bodies identical',target_proofs=False,source_fidelity=False,statement_change=False))
write(RUN/'review-scope-v1.md','Contract-only review before production theorem body: actual frozen full four header types/source/signature/DAG/conversion/localAPI/reuse/neutral blind. Search for mismatch, not confirmation. Existing canonical12 are dependency evidence, not new proof growth or silently reaccepted old publication. Source all3 abs support branches and any-support Algorithm2.2 must match actual played policy and same-run eta. New finite sqrtT/one-sided eventual are explicit consequences of source asymptotic example/transfer. Old required publication/nineOTHERChapter1/remaining chapters stay open. Mandatory distinct actors, no human/external/runtimemodel attestation. No fullsource semantics enforced by CLI alone.')
print('Actual/neutral complete four closed types kernel-equal; original import-position failure preserved.')
