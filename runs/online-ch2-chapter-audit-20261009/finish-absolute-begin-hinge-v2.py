from lower_common_v1 import *
import re
d=reviewed();current=headers(1)
b=load(RUN/'absolute-focused-build-v1.json');out=base64.b64decode(b['stdout_base64']).decode('utf8')
k=load(RUN/'absolute-public-value-v1.json');stdout=base64.b64decode(k['stdout_base64']).decode('utf8')
assert b['actual_exit']==k['actual_exit']==0 and 'Build completed successfully' in out and 'error:' not in out+stdout
found=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",stdout,re.S)
assert len(found)==1 and found[0][0]==d['targets'][0]['declaration']
actual_axioms=re.findall(r'[A-Za-z_.]+',found[0][1])
assert set(actual_axioms)=={'propext','Classical.choice','Quot.sound'}
write(RUN/'absolute-evidence-parser-failure-v1.json',dict(actual_helper_exit=1,
 failed_helper='finish-absolute-begin-hinge-v1.py',failure='Literal one-line axiom-output assertion did not accept actual wrapped Lean output.',
 proof_build_actual_exit=b['actual_exit'],public_type_kernel_actual_exit=k['actual_exit'],
 repair='Parse complete actual bracketed axiom record across whitespace; require exact declaration and allowed three standard axioms. No proof, frozen type or compiler-output change; no unnecessary build repeat.'))
write(RUN/'leaf-NS001-compiled-v1.json',dict(phase='candidate compiled finite terminal; distinct BODY/source final acceptance pending',
 declaration=current[0],complete_production_file_sha256=sha(PRODUCTION),attempt_snapshot_sha256=sha(RUN/'leaf-NS001-attempt-v1.lean'),
 focused_build_sha256=sha(RUN/'absolute-focused-build-v1.json'),actual_build_success_marker=out.rstrip().splitlines()[-1],
 actual_public_value_and_axiom_sha256=sha(RUN/'absolute-public-value-v1.json'),axioms=actual_axioms,
 new_production_proof_count=1,source_family='shifted absolute intro',chapter_complete=False,whole_Goal_status='ACTIVE'))
event('absolute-candidate-event-v1','candidate',dict(leaf='NS001',terminal_hash=d['targets'][0]['statement_hash'],
 actual_current_kernel='compiled',body_review_pending=True,proof_receipt=sha(RUN/'leaf-NS001-compiled-v1.json'),chapter_complete=False,goal_complete=False))
event('hinge-proving-event-v1','proving',dict(leaf='NS002',terminal_hash=d['targets'][1]['statement_hash'],
 approved_scope=sha(CONTRACT/'nonsmooth-stabilized-v1.json'),
 ready_dependencies='Actual prior affine convexity/real-epigraph bridge, full hinge support set, singleton differentiability iff and finite real-germ producer; all complete current dependency files match prior scoped review.',
 chapter_complete=False,goal_complete=False))
reviewed();print('NS001 actual standard axioms inspected, parser failure retained; NS002 proving event precedes its new body.')
