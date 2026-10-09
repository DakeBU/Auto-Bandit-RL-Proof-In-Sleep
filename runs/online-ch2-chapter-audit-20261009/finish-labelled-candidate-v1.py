from lower_common_v1 import *
import re
d=reviewed();current=headers(3)
b=load(RUN/'labelled-focused-build-v1.json');out=base64.b64decode(b['stdout_base64']).decode('utf8')
assert b['actual_exit']==0 and 'Build completed successfully' in out and 'error:' not in out
assert 'warning: BanditRLProof/OnlineNonsmoothExamples.lean' not in out
scratch='import BanditRLProof.OnlineNonsmoothExamples\nopen scoped InnerProductSpace\n'
for t,arg in zip(d['targets'],['c','a','y z']):
 short=t['declaration'].rsplit('.',1)[-1]
 scratch+='\n'+t['exact_proposed_header'].replace('theorem '+short,'example',1)+' :=\n  '+t['declaration']+' '+arg+'\n'
 scratch+='\n#check @'+t['declaration']+'\n#print axioms '+t['declaration']+'\n'
write(RUN/'nonsmooth-all-public-values-v1.lean',scratch)
code,stdout=capture('nonsmooth-all-public-values-v1','lake','env','lean',RUN/'nonsmooth-all-public-values-v1.lean')
found=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",stdout,re.S)
assert [name for name,_ in found]==[t['declaration'] for t in d['targets']]
axioms=[]
for name,record in found:
 values=re.findall(r'[A-Za-z_.]+',record);assert set(values)=={'propext','Classical.choice','Quot.sound'}
 axioms.append(dict(declaration=name,axioms=values))
write(RUN/'leaf-NS003-compiled-v1.json',dict(phase='candidate exact finite terminal and current whole public-value kernel; independent actual BODY acceptance pending',
 declaration=current[2],complete_production_file_sha256=sha(PRODUCTION),attempt_snapshot_sha256=sha(RUN/'leaf-NS003-attempt-v1.lean'),
 focused_build_sha256=sha(RUN/'labelled-focused-build-v1.json'),actual_build_success_marker=out.rstrip().splitlines()[-1],
 actual_public_value_and_axiom_sha256=sha(RUN/'nonsmooth-all-public-values-v1.json'),actual_axiom_records=axioms,
 parent_NS002_actual_compiled_receipt_sha256=sha(RUN/'leaf-NS002-compiled-v1.json'),
 source_family='labelled hinge: same effective-normal trajectory-free function, exact point/global criteria; no unqualified universal nonsmoothness claim',
 chapter_complete=False,whole_Goal_status='ACTIVE'))
write(CONTRACT/'nonsmooth-current-candidate-v1.json',dict(phase='proving -> candidate for exact three finite public terminals only',
 source_contract_sha256=sha(CONTRACT/'nonsmooth-stabilized-v1.json'),contract_reviewer_sha256=REVIEW_SHA,
 public_proof_count=3,source_family_count=2,source_enumeration_v3_sha256=sha(CONTRACT/'complete-source-reconciliation-draft-v3.json'),
 exact_current_native_headers=current,current_production_file=PRODUCTION.relative_to(ROOT).as_posix(),current_production_file_sha256=sha(PRODUCTION),
 all_public_exact_type_kernel_sha256=sha(RUN/'nonsmooth-all-public-values-v1.json'),actual_axioms=axioms,
 new_canary_contract_sha256=sha(CONTRACT/'nonsmooth-canary-contracts-v1.json'),
 no_old_production_Test_root_pin_or_source_changes=True,
 validation_boundary='Actual focused builds and whole public-type kernel succeeded, own final production module warnings0. Canary BODY/semantic review/root/Tests/full harness/reader/shared registry/site/PR delivery not yet passed.',
 chapter_complete=False,book_complete=False,whole_Goal_status='ACTIVE'))
event('labelled-candidate-event-v1','candidate',dict(leaf='NS003',terminal_hash=d['targets'][2]['statement_hash'],actual_current_kernel='compiled',
 body_review_pending=True,proof_receipt=sha(RUN/'leaf-NS003-compiled-v1.json'),chapter_complete=False,goal_complete=False))
write(RUN/'nonsmooth-production-BODY-review-input-v1.json',dict(
 scope='Distinct actual BODY review for three exact compiled production terminals only, before public root/reader/chapter gate integration',
 files=rows([PRODUCTION,CONTRACT/'nonsmooth-current-candidate-v1.json',CONTRACT/'nonsmooth-targets-draft-v1.json',CONTRACT/'nonsmooth-stabilized-v1.json',
  RUN/'source-contract-repair-review-v1.md',RUN/'source-contract-repair-review-v1.json',RUN/'nonsmooth-blind-reconstruction-v1.md',RUN/'nonsmooth-blind-receipt-v1.json',
  RUN/'nonsmooth-all-public-values-v1.lean',RUN/'nonsmooth-all-public-values-v1.json',RUN/'leaf-NS001-compiled-v1.json',RUN/'leaf-NS002-compiled-v1.json',RUN/'leaf-NS003-compiled-v1.json',
  RUN/'absolute-focused-build-v1.json',RUN/'hinge-focused-build-v1.json',RUN/'hinge-focused-build-v2.json',RUN/'labelled-focused-build-v1.json',
  RUN/'hinge-failure-classification-v1.json',RUN/'absolute-evidence-parser-failure-v1.json',ROOT/'BanditRLProof/OnlineHinge.lean',ROOT/'BanditRLProof/OnlineConvexExamples.lean',ROOT/'BanditRLProof/OnlineSubgradientDifferentiability.lean']),
 exact_statement_hashes=[dict(declaration=t['declaration'],statement_hash=t['statement_hash']) for t in d['targets']],
 requested_review='Actual proof BODY constructs convexity, ambient nonsmooth/smooth iff and actual global nonzero-normal boundary; source repair stays explicit; old modules immutable; public values and axiom stdout actual, compiler success distinct from wrapper success. Full chapter/canary/current integration acceptance not requested.',
 canaries='Five exact frozen proposals in nonsmooth-canary-contracts-v1.json have separate blind reconstruction underway; no canary BODY yet and not certified by this production-only pass.',
 chapter_complete=False,whole_Goal_status='ACTIVE'))
reviewed();print('All three exact production terminal bodies compiled; whole-type public kernel and standard axioms inspected, production BODY review ready.')
