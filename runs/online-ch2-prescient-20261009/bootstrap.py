from common import *
assert Path.cwd()==ROOT and sha(PDF)==PDF_SHA
assert subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()==BASE
assert subprocess.check_output(['git','branch','--show-current'],text=True).strip()==BRANCH
prior=ROOT/'runs/online-ch2-chapter-audit-20261009'
assert sha(prior/'nonsmooth-delivery-review-v1.json')=='8674e236ef7f13bc6a32a49580c6cb2841c33949292cc9c119d7828e205a7e7b'
observation=ROOT/'tmp/online-ch2-nonsmooth-final-delivery-v1/FINAL-clean-remote-observation.json'
o=load(observation);assert o['head']==BASE and not o['dirty'] and o['actual_remote']['headRefOid']==BASE
write(RUN/'prior-PR204-final-observation-v1.json',observation.read_bytes())
paths={Path(x['path']) for x in load(prior/'baseline-v1.json')['rows']}
for dirname in ['BanditRLProof','Tests','website/content','docs/contracts','research-wiki/contribution-contracts']:
    paths.update(p for p in (ROOT/dirname).rglob('*') if p.is_file() and CONTRACT not in p.parents)
paths.update(p for p in prior.rglob('*') if p.is_file() and '__pycache__' not in p.parts)
paths.update(ROOT/p for p in ['BanditRLProof.lean','Tests.lean','lean-toolchain','lakefile.lean','lake-manifest.json','tools/bandit.py','tools/abrl_lifecycle.py'])
write(RUN/'baseline-v1.json',dict(rows=rows(paths),base=BASE,base_PR=204,base_branch='codex/research-online-ch2-chapter-audit',branch=BRANCH,
    shared_git_store=subprocess.check_output(['git','rev-parse','--git-common-dir'],text=True).strip(),canonical_main=subprocess.check_output(['git','-C','E:/ABRL/research','rev-parse','HEAD'],text=True).strip(),
    source_pdf_sha256=sha(PDF),prior_final_delivery_sha256=sha(observation),whole_Goal_status='ACTIVE'))
draft=ROOT/'tmp/online-ch2-prescient-draft-20261009'
for p in draft.iterdir():
    if p.is_file():write(RUN/p.name,p.read_bytes())
write(RUN/'00_context.md','Orabona v10 Chapters1-16 persistent Goal ACTIVE, requested GPT6Astra/medium. Current Chapter2 partial, source inventory65 overlapping containers is enumeration only/null proof denominator; all8 required forward references remain open. Previous bounded nonsmooth package3 proofs/2 source families/5 canaries delivered in OPENdraft/unmerged PR204, final head '+BASE+'. This branch stacks exactly there and reuses the active book checkout/shared Lean/Lake/registry. New package is ONLY a reusable Euclidean affine-loss prescient foundation for the Chapter2 forward observation, not full Algorithm15.8/Theorem15.30/general OMD or Chapter15 work. Source PDF rehashed; PDF26,277,278 freshly read/rendered and root personally viewed. Draft7 exact types/4 definitions reconstructed by distinct osd_blind; independent anti-anchored source review still required before proving. Root stages director/architect/lower roles, distinct automated decoder/reviewer history disclosed; no human/external/runtime attestation. No global SGB/frontier/index, old package, private/frozen/_site mutation, merge/deploy or retirement.')
write(RUN/'10_director-draft-v1.md','Select one dependency-ready Euclidean linear prescient producer chain for Chapter2 source forward reference. Explicitly read current loss vector BEFORE current prediction, construct actual projected proximal minimizer, retain negative movement square and terminal distance, and telescope the SAME generated trajectory. Do not negate ordinary gradient-square energy on a constrained domain. Finite seven terminals form one chain, not7source theorems/chapter proof denominator. Full general convex/subdifferentiable/Bregman and time-varying prescient statements remain required later. Source reviewer must classify this as reusable foundation growth or reject; it cannot close the full prescient source container. First lower leaf after stabilization: exact advance_sharp_bound from actual project variational characterization. No source-facing body before reviewed exact terminal/semantic slots/DAG/conversion window.')
capture('new-task-v1',sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','new-task',TASK,'--kind','lean','--title','Euclidean affine-loss prescient producer foundation for Chapter2 forward reference','--target-lean',PUBLIC.relative_to(ROOT).as_posix())
fixed();print('New OWN draft task created; previous package and all old/global RAW baseline fixed:',len(paths))
