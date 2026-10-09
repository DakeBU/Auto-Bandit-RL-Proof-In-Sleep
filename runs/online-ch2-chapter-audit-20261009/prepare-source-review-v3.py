from common_v1 import *
import copy,base64
fixed()
v2=load(CONTRACT/'complete-source-reconciliation-draft-v2.json')
source=load(CONTRACT/'source-fingerprint-v1.json');pages={r['pdf_page']:r for r in source['source_pages']}
v3=copy.deepcopy(v2);v3['stage']='source inventory version3 for independent stabilization review; Chapter2 not accepted'
v3['supersedes_v2']=dict(path=(CONTRACT/'complete-source-reconciliation-draft-v2.json').relative_to(ROOT).as_posix(),sha256=sha(CONTRACT/'complete-source-reconciliation-draft-v2.json'),reason='Actual bounded source query located Chapter7 FTRL pointer in History PDF35, not PDF20. Preserve as historical navigation, not a new mandatory Chapter2 mathematical theorem.')
for r in v3['rows']:
 if r['source_id']=='forward:chapter7-FTL-analysis':
  r.update(source_pages=[pages[35]],container_kind='historical forward navigation; Chapter7 remains required by whole-book Goal',
   required=False,maintext_mathematical_obligation=False,
   mathematical_intent='Section2.4 History PDF35 points to FTRL in Chapter7. Retain historical navigation and source attribution; history is outside the default Chapter2 mathematical proof obligation list. Chapter7 main-text mathematics remains required by the whole-book Goal independently.',
   dependency_status='historical pointer retained; not counted as a new mathematical proof target',
   chapter_gate_policy='No Chapter2 theorem obligation inferred from historical narrative. Existing whole-book Chapter7 required scope is unchanged.')
v3['forward_required_open_count']=8
v3['historical_navigation_extra_count']=1
v3['proof_leaf_total']=None
v3['source_audit_containers']=65
v3['semantic_signature_boundary']='Seven-slot source signatures attach exact native terminal text and complete scoped module RAW hashes, not inventory counts as a proof substitute. Existing full-file matching prior reviews may be reused only in exact source/statement scope. Unresolved new finite source terminals and forward claims stay explicit.'
write(CONTRACT/'complete-source-reconciliation-draft-v3.json',v3)

draft=load(CONTRACT/'nonsmooth-targets-draft-v1.json')
probe='''import Mathlib.Analysis.Calculus.Deriv.Abs
import BanditRLProof.OnlineHinge
import BanditRLProof.OnlineSubgradientDifferentiability

noncomputable section
open scoped InnerProductSpace
'''
for t in draft['targets']:
 h=t['exact_proposed_header'];short=t['declaration'].rsplit('.',1)[-1]
 binders,conclusion=h[len('theorem '+short):].split(' :\n',1)
 probe+='\n#check (∀'+binders+',\n'+conclusion+')\n'
probe+='''
#check ConvexOn.sup
#check ConvexOn.comp_affineMap
#check convexOn_univ_norm
#check convexOn_const
#check AffineMap.const
#check not_differentiableAt_abs_zero
#check DifferentiableAt.abs
#check real_inner_smul_left
#check real_inner_smul_right
#check inner_self_ne_zero
#check BanditRL.OnlineConvex.example_2_27
#check BanditRL.OnlineConvex.theorem_2_22
#check BanditRL.OnlineConvex.sourceDifferentiableAt_regular
'''
write(RUN/'nonsmooth-type-api-probe-v1.lean',probe)
tick=time.monotonic();p=subprocess.run(['lake','env','lean',str(RUN/'nonsmooth-type-api-probe-v1.lean')],cwd=str(ROOT),stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
write(RUN/'nonsmooth-type-api-probe-v1.json',dict(command=['lake','env','lean','OWN nonsmooth-type-api-probe-v1.lean'],actual_exit=p.returncode,
 seconds=time.monotonic()-tick,stdout_sha256=hashlib.sha256(p.stdout).hexdigest(),stdout_base64=base64.b64encode(p.stdout).decode('ascii'),
 boundary='Only proposition elaboration and actual declaration type retrieval, no theorem body/proof or mathematical closure. A missing API name is a retrieval failure, not terminal weakening.'))
print('Proposed types/API probe actual exit',p.returncode)

blind=load(RUN/'nonsmooth-blind-receipt-v1.json')
write(RUN/'nonsmooth-source-contract-review-input-v1.json',dict(
 phase='Exact pre-proof source/contract/repair and source inventory stabilization review input',
 files=rows([CONTRACT/'complete-source-reconciliation-draft-v3.json',CONTRACT/'nonsmooth-targets-draft-v1.json',RUN/'nonsmooth-blind-packet-v1.md',RUN/'nonsmooth-blind-reconstruction-v1.md',RUN/'nonsmooth-blind-receipt-v1.json',RUN/'nonsmooth-type-api-probe-v1.lean',RUN/'nonsmooth-type-api-probe-v1.json',RUN/'current-online-declaration-retrieval-v1.json',RUN/'prior-receipt-current-file-join-v1.json',RUN/'source-enumeration-review-v1.md',RUN/'source-enumeration-review-v1.json',ROOT/'BanditRLProof/OnlineHinge.lean',ROOT/'BanditRLProof/OnlineSubgradientDifferentiability.lean',ROOT/'BanditRLProof/OnlineConvexExamples.lean',ROOT/'BanditRLProof/OnlineConvexClosures.lean',ROOT/'tasks'/(TASK+'.md'),ROOT/'proof-obligations'/(TASK+'.md'),ROOT/'conversion-windows'/(TASK+'.md')]),
 requested_decisions=['version3 complete-source inventory E1-E8 repair and full actual scoped provenance join; no wholeChapter2 acceptance','three exact new nonsmooth types and separate qualified hinge source-repair verdict','dependency-ready/finite allowed edit scope before proving; no source/old proof weakening'],
 frozen_proposed_statement_hashes=[dict(declaration=t['declaration'],statement_hash=t['statement_hash']) for t in draft['targets']],
 proposed_route_refinement='Use actual full hinge subdifferential and Theorem2.22 both ways to obtain differentiability off boundary; no separate local-filter calculus needed. Absolute uses actual translated norm and derivative APIs. Same terminal types as blind packet.',
 chapter_complete=False,whole_Goal_status='ACTIVE'))
fixed();print('Version3 source inventory and separate finite contract/repair review inputs prepared, old drafts/failures preserved.')
