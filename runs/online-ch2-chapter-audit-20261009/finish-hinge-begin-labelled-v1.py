from lower_common_v1 import *
import re
d=reviewed();current=headers(2)
b=load(RUN/'hinge-focused-build-v2.json');out=base64.b64decode(b['stdout_base64']).decode('utf8')
assert b['actual_exit']==0 and 'Build completed successfully' in out and 'error:' not in out
assert 'warning: BanditRLProof/OnlineNonsmoothExamples.lean' not in out
t=d['targets'][1];short=t['declaration'].rsplit('.',1)[-1]
scratch='import BanditRLProof.OnlineNonsmoothExamples\nopen scoped InnerProductSpace\n'+t['exact_proposed_header'].replace('theorem '+short,'example',1)+' :=\n  '+t['declaration']+' a\n'
scratch+='\n#print axioms '+t['declaration']+'\n'
write(RUN/'hinge-public-value-v1.lean',scratch)
code,stdout=capture('hinge-public-value-v1','lake','env','lean',RUN/'hinge-public-value-v1.lean')
found=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",stdout,re.S)
assert len(found)==1 and found[0][0]==t['declaration']
actual_axioms=re.findall(r'[A-Za-z_.]+',found[0][1])
assert set(actual_axioms)=={'propext','Classical.choice','Quot.sound'}
write(RUN/'leaf-NS002-compiled-v1.json',dict(phase='candidate compiled finite terminal; distinct actual BODY/source review pending',
 declaration=current[1],complete_production_file_sha256=sha(PRODUCTION),attempt_snapshot_sha256=sha(RUN/'leaf-NS002-attempt-v2.lean'),
 focused_build_sha256=sha(RUN/'hinge-focused-build-v2.json'),actual_build_success_marker=out.rstrip().splitlines()[-1],
 actual_public_value_and_axiom_sha256=sha(RUN/'hinge-public-value-v1.json'),axioms=actual_axioms,
 failed_build_v1_preserved=True,frozen_terminal_unchanged=True,
 source_family='hinge intro: actual convexity and full ambient differentiability iff',chapter_complete=False,whole_Goal_status='ACTIVE'))
event('hinge-candidate-event-v1','candidate',dict(leaf='NS002',terminal_hash=t['statement_hash'],actual_current_kernel='compiled',
 body_review_pending=True,proof_receipt=sha(RUN/'leaf-NS002-compiled-v1.json'),chapter_complete=False,goal_complete=False))
event('labelled-proving-event-v1','proving',dict(leaf='NS003',terminal_hash=d['targets'][2]['statement_hash'],
 approved_scope=sha(CONTRACT/'nonsmooth-stabilized-v1.json'),
 ready_dependencies='NS002 actual focused+whole-type kernel standard-axiom completion; real scalar inner identity and inner_self_ne_zero; construct margin1 point from nonzero effective normal.',
 actual_parent_kernel_receipt=sha(RUN/'leaf-NS002-compiled-v1.json'),chapter_complete=False,goal_complete=False))
reviewed();print('NS002 public whole-type/axiom/build inspected; NS003 actual parent dependency ready and proving event recorded before body.')
