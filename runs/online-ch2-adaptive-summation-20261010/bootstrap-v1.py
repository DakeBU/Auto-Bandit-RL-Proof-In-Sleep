from pathlib import Path
import subprocess, sys, json, base64, hashlib

ROOT=Path.cwd()
RUN=ROOT/'runs/online-ch2-adaptive-summation-20261010'
CONTRACT=ROOT/'docs/contracts/online-ch2-adaptive-summation-v1'
TASK='ONLINE-CH2-ADAPTIVE-SUMMATION-20261010'
BRANCH='codex/research-online-ch2-adaptive-summation'
BASE='8f31042350bd8eeb1c9108257c58e2b3aafaebfb'
assert ROOT.as_posix()=='E:/ABRL/worktrees/research-online-book'
assert subprocess.check_output(['git','branch','--show-current'],encoding='utf8').strip()==BRANCH
assert subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip()==BASE
status=subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],encoding='utf8').splitlines()
assert len(status)==1 and status[0][3:]=='runs/online-ch2-adaptive-summation-20261010/bootstrap-v1.py',status
old=ROOT/'runs/online-ch2-reconciliation-20261010'
text=(old/'common.py').read_text(encoding='utf8')
for a,b in [('online-ch2-reconciliation-v1','online-ch2-adaptive-summation-v1'),('2e06e21d2acb0bf41142b19266d66d89364e17a0',BASE),('codex/research-online-ch2-reconciliation',BRANCH),('ONLINE-CH2-RECONCILIATION-20261010',TASK),("PUBLIC=ROOT/'BanditRLProof.lean'","PUBLIC=ROOT/'BanditRLProof/OnlineAdaptiveSummation.lean'")]:
    assert a in text,a
    text=text.replace(a,b)
assert not (RUN/'common.py').exists()
(RUN/'common.py').write_bytes(text.encode('utf8'))
sys.path.insert(0,str(RUN))
from common import *
tracked=[ROOT/p for p in subprocess.check_output(['git','ls-files','-z']).decode('utf8').split('\0') if p]
write(RUN/'baseline-v1.json',dict(base=BASE,branch=BRANCH,rows=rows(tracked),scope='All prior tracked RAW files immutable during draft/proving; new OWN evidence and separately stabilized NEW production module only.'))
write(RUN/'.gitattributes','* -text\nlifecycle-sessions.jsonl whitespace=blank-at-eol,blank-at-eof,space-before-tab,cr-at-eol\nlifecycle-state.json whitespace=blank-at-eol,blank-at-eof,space-before-tab,cr-at-eol\nown-artifact-journal.md whitespace=blank-at-eol,blank-at-eof,space-before-tab,cr-at-eol\n')
write(CONTRACT/'.gitattributes','* -text\n')
wrapper=(old/'native-scoped.py').read_text(encoding='utf8').replace("bandit.MANIFEST = RUN / 'own-artifact-journal.md'","bandit.MANIFEST = RUN / 'own-artifact-journal.md'\nbandit.RETRIEVAL_INDEX_DIR = RUN / 'reference-index'")
write(RUN/'native-scoped.py',wrapper)
for p in sorted((ROOT/'tmp/online-ch2-adaptive-start-v1').glob('*.json')):
    write(RUN/('start-'+p.name),p.read_bytes())
scope=('First bounded prerequisite for the Chapter2 required adaptive-rate forward claim: Orabona v10 Lemma4.13, printed40/PDF52, a nonnegative finite-increment sum bounded by the integral of a continuous nonincreasing nonnegative function on [0,infinity). '
       'This is reusable foundation growth toward the actual causal OSD guarantees (4.3),(4.4),Theorem4.14; it is not an algorithm, regret consumer or completed adaptive-rate guarantee. '
       'Chapter4 is not promoted to the main chapter; its full inventory remains unenumerated/null. The current Chapter2 forward edge stays required/open until its complete exact mathematical terminal and source reconciliation pass. '
       'All eight Chapter2 forward containers and six future mathematical claims remain required/open; Chapter2 partial/null; whole Chapters1-16 Goal ACTIVE.')
write(RUN/'00_context.md','# '+TASK+'\n\n'+scope+'\n\nStacked on OPEN draft unmerged PR215 exact '+BASE+'. Canonical research/main and origin/main freshly inspected; same retained worktree reused, shared Git/.lake/website links preserved. No prior source/Test/contract/reader/progress/global SGB or anonymous/private source edit.\n\nRequested GPT-6 Astra / medium throughout, not runtime attestation. Reuse distinct decoder/source-reviewer roles required by AGENTS; one lower proof route, no parallel chapter proof writing. Paper title: ABRL: A Target-Faithful Autoformalization Harness and Lean 4 Library for Bandit and Reinforcement Learning Theory. Particular CLI gates plus recorded role conventions are separate, not one runtime-enforced workflow.\n')
write(RUN/'10_director-draft-v1.md','# Director\n\n'+scope+'\n\nNext finite proof leaf is the general integral comparison after exact source/Lean seven-slot contract review. No positivity of each increment or global continuity may be substituted for the source hypotheses. T=0, repeated zero increments and a0=0 are included.\n')
write(RUN/'20_middle-draft-v1.md','# Middle\n\nNew generic module OnlineAdaptiveSummation in the existing shared project; source-facing theorem lemma_4_13 must preserve finite sums, endpoints, continuity/antitonicity/nonnegativity only on Ici0 and arbitrary nonnegative initial offset. Ambient extension outside Ici0 has no mathematical role. No probabilistic information structure is introduced. Source and exact Lean statements freeze before BODY work; actual type elaboration is not proof closure.\n\nAdaptive future target must use current observed supports in the same causal state, skip zero-gradient rounds, retain D=0/T=0/zero-energy cases, and separately review the displayed attained-minimum equality at zero energy. Its future-gradient coefficients cannot define the learner. That later target is not frozen or accepted by this summation leaf.\n')
write(RUN/'30_architect-draft-v1.md','# Architect\n\nOne route: nonnegative cumulative endpoints -> interval integrability from ContinuousOn Ici0 -> constant endpoint integral comparison using antitonicity -> finite sum -> adjacent interval telescope. Reuse pinned Mathlib intervalIntegral.integral_mono_on, ContinuousOn.intervalIntegrable_of_Icc and sum_integral_adjacent_intervals. Search actual local/card APIs before creating a general-purpose theorem. General sum inequality is mathlib-candidate, source-qualified wrapper must remain thin.\n\nFuture inverse-square-root energy summation can reuse the existing public Tsallis.two_mul_sqrt_sub_sqrt_le_sub_div_sqrt supporting-line inequality with reversed endpoints; do not copy its proof. Existing positive-eta weighted_potential_sum cannot cover initial zero energy without explicit branch treatment. Future actual OSD/state and zero-energy minimum correction remain open.\n')
write(RUN/'memory_digest.md','# Draft memory\n\n'+scope+'\n\nPrior delivered generic FTL/provenance package PR215 exact '+BASE+' remains immutable; root/Tests/full harness/site/FINAL/native/postnative/delivery are bound in its RUN. They do not compile this new theorem. Current first leaf BODY unwritten. No source or chapter acceptance yet.\n')
for label,args in [('new-task-help',[sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','new-task','--help']),('event-help',[sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','lifecycle-event','--help']),('reference-help',[sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','reference-index','--help']),('declaration-help',[sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','list-lean-decls','--help'])]:
    capture(label+'-v1',*args)
capture('native-new-task-v1',sys.executable,'-B','-X','utf8',RUN/'native-scoped.py','new-task',TASK,'--kind','theorem','--title','Prove the integral comparison prerequisite for Chapter2 adaptive-rate forward dependency')
templates=[ROOT/d/(TASK+'.md') for d in ['tasks','conversion-windows','proof-obligations']]
write(RUN/'task-templates-exact-v1.json',dict(rows=[dict(path=p.as_posix(),sha256=sha(p),raw_base64=base64.b64encode(p.read_bytes()).decode('ascii')) for p in templates]))
for folder,body in [('tasks',scope+'\n\nState draft; first finite terminal Lemma4.13. No BODY or chapter closure.'),('conversion-windows',scope+'\n\nDraft: only NEW OWN run/contract/task/obligation/retrieval files. After favorable exact source contract review, NEW BanditRLProof/OnlineAdaptiveSummation.lean BODY only with frozen header/context. Old files and root/Test/reader/registry integration require later exact scope review.'),('proof-obligations',scope+'\n\n- [ ] Actual local/Mathlib/card retrieval.\n- [ ] Freeze exact statement/imports/context; neutral reconstruction and anti-anchored source CONTRACT review.\n- [ ] Actual theorem BODY from interval comparison and telescope.\n- [ ] Nondegenerate public canary, axioms, statement fence, focused build and BODY review.\n- [ ] Combined root/Tests/full harness, reader/shared registry/site and FINAL/native/postnative/scoped PR delivery.\n- [ ] Later complete causal adaptive OSD and separately reviewed minimum/infimum edge; not discharged by this leaf.\n\nNo numeric whole-chapter denominator; mandatory total null.'),('research-wiki/retrieval-index',scope+'\n\nCandidate APIs: intervalIntegral.integral_mono_on, sum_integral_adjacent_intervals, ContinuousOn.intervalIntegrable_of_Icc. Read-only prior API/pixel retrieval is evidence of inspection, not proof. Native reference-index redirected to NEW OWN RUN/reference-index; global retrieval files/frontier/journals unchanged.')]:
    p=ROOT/folder/(TASK+'.md')
    data=('# '+TASK+'\n\n'+body+'\n').encode('utf8')
    if p.exists():p.write_bytes(data)
    else:write(p,data)
source=[]
for page in [51,52]:
    image=ROOT/'tmp/online-ch2-next-dependency-readonly'/('source-pdf'+str(page)+'-v1.png')
    dest=RUN/image.name;write(dest,image.read_bytes())
    tp=old/'forward-readonly-retrieval'/('source-pdf'+str(page)+'-text-v1.txt')
    source.append(dict(pdf_page=page,printed_page=page-12,image_path=dest.as_posix(),image_sha256=sha(dest),prior_text_path=tp.as_posix(),prior_text_sha256=sha(tp),text_raw_base64=base64.b64encode(tp.read_bytes()).decode('ascii'),exact_extracted_text=tp.read_text(encoding='utf8')))
write(CONTRACT/'source-fingerprint-v1.json',dict(pdf=PDF.as_posix(),pdf_sha256=PDF_SHA,source_version='arXiv:1912.13213v10, 2026-06-21',source_pages=source,root_viewed_both_original_images=True,source_result='Lemma4.13 printed40/PDF52; adaptive formulas/4.14 are intended downstream references, not closed targets.',required_forward_inventory=rows([ROOT/'docs/contracts/online-ch2-reconciliation-v1/required-forward-dependencies-draft-v1.json']),scope=scope))
event('native-draft-v1','draft',dict(scope=scope,source_fingerprint=sha(CONTRACT/'source-fingerprint-v1.json'),stacked_base=BASE,lean_edit_scope=[],first_leaf='Lemma4.13 contract pending',chapter_complete=False,whole_Goal='active'))
fixed()
print('New bounded summation prerequisite draft initialized; no proof/algorithm/chapter acceptance.',flush=True)
