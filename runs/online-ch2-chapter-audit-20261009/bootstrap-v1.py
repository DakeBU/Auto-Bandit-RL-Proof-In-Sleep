from common_v1 import *
assert Path.cwd()==ROOT and sha(PDF)==PDF_SHA
assert subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip()==BASE
assert subprocess.check_output(['git','branch','--show-current'],encoding='utf8').strip()==BRANCH
prior=ROOT/'tmp/online-c1-chapter-audit-final-delivery-review-v1.json'
assert sha(prior)=='5fda4e3ec3ccd94a90238cc0c30d43cddfd9374530ccc2c75b8b00e13e99c80e'
d=load(prior);assert d['chapter1_local_gate_certified'] and d['final_metadata_delivery_certified'] and d['may_proceed_to_Chapter2']
assert d['actual_final_head']==BASE and d['whole_Goal_status']=='ACTIVE' and not d['goal_complete']
for suffix in ['json','md']:
 p=ROOT/('tmp/online-c1-chapter-audit-final-delivery-review-v1.'+suffix)
 write(RUN/('prior-chapter1-delivery-review-v1.'+suffix),p.read_bytes())
paths=set(Path(r['path']) for r in load(ROOT/'runs/online-c1-chapter-audit-20261009/baseline-v2.json')['rows'])
for dirname in ['BanditRLProof','Tests','website/content','docs/contracts','research-wiki/contribution-contracts']:
 paths.update(p for p in (ROOT/dirname).rglob('*') if p.is_file() and CONTRACT not in p.parents)
paths.update(p for p in (ROOT/'runs/online-c1-chapter-audit-20261009').rglob('*') if p.is_file() and '__pycache__' not in p.parts)
paths.update([prior,Path(d['report']),ROOT/'BanditRLProof.lean',ROOT/'Tests.lean',ROOT/'lean-toolchain',ROOT/'lakefile.lean',ROOT/'lake-manifest.json'])
assert all(p.is_file() for p in paths)
write(RUN/'baseline-v1.json',dict(rows=rows(paths),base=BASE,base_PR=203,base_branch='codex/research-online-c1-chapter-audit',branch=BRANCH,
 origin_main=subprocess.check_output(['git','rev-parse','origin/main'],encoding='utf8').strip(),
 canonical_main=subprocess.check_output(['git','-C','E:/ABRL/research','rev-parse','HEAD'],encoding='utf8').strip(),
 canonical_status=subprocess.check_output(['git','-C','E:/ABRL/research','status','--porcelain'],encoding='utf8'),
 shared_git_store=subprocess.check_output(['git','rev-parse','--git-common-dir'],encoding='utf8').strip(),
 shared_lake_link_retained=True,prior_C1_delivery_receipt_sha256=sha(prior),whole_Goal_status='ACTIVE'))
write(RUN/'00_context.md','Whole Orabona v10 Chapters1-16 Goal ACTIVE, GPT6Astra/medium. Chapter1 current17source-object gate accepted-local-with-explicit-source-correction and finalmetadata PR203 delivery independently certified at exact097359ac; ordinary-limit false-as-written inference is not proved or erased. Prior ignored finaldelivery review/report copied byteexact here. Start Chapter2 complete maintext reconciliation with actual existing reviewed packages, not stale Oct5 next-migration prose. Canonicalmain/origin freshly fetched6847 clean; new branch codex/research-online-ch2-chapter-audit based OPENdraft/unmerged PR203 exact097359ac. Same active worktree/shared Lean/Lake/registry and junctions preserved, no perBook project. Chapter2partial; C3-16unenumerated/null and necessary appendix dependencies REQUIRED. Independent Problems2.1-2.5/history separate optional; maintext formal results whose proofs are exercises REQUIRED. No parallel multichapter proof writing, optional agents, globalSGB/frontier/index/trials/memory mutation, newtopround/final/private/frozen/_site edits, merge/deploy/retirement or mainlive/wholeGoalcomplete. Distinct staged actors required by repository semantic skill; reuse exact prior blind/source receipts with disclosed history, no human/external/absolute-blind/runtime model claims.')
write(RUN/'10_director-draft-v1.md','Re-enumerate numbered and UNNUMBERED Chapter2 statements with source anchors and all branches. Join actual current public contracts/proof values to prior separate source/BODY/reader/native/delivery evidence by exact hashes; no theorem-number or stale manifest status substitution. Prior navigation34=32numbered(including pedagogicalRemark)+2algorithmboxes and18unnumbered groups are overlapping draft containers, NOT52proof obligations. First priority is Theorem2.13 variable branch with same actual causal recurrence, source regularity, lastplayed eta and negative terminal. It already exists: reuse if exact obligations match, no duplicate wrapper. Recheck the full OSD transfer, linearization/causality, extended-real arithmetic, domain/proper/closed, all example guarantees and source convention issues. Additional abs/hinge/uncountability/relative-interior/lookahead claims must not disappear. The lookahead sentence refers to prescientOMD Algorithm15.8/Theorem15.30 (PDF277); classify by separate source review or close a necessary bounded Euclidean leaf, not causal OGD or a full generalOMD claim. Source-as-written, actual Lean, mismatch and proposed repair remain separate. Finite dependency-ready proof leaves only after stabilized contracts; phase outputs may share root actor except mandatory distinct decoder/reviewer. Chapter2 gate cannot reuse Chapter1 acceptance.')
native('new-task-v1','new-task',TASK,'--kind','lean','--title','Chapter2 complete source/contract reconciliation after Chapter1 gate','--target-lean','BanditRLProof/OnlineGradientDescentSource.lean')
from pypdf import PdfReader
import pypdfium2 as pdfium
reader=PdfReader(str(PDF));document=pdfium.PdfDocument(str(PDF));pages=[]
for n in range(20,36):
 txt=RUN/('source-pdf'+str(n)+'-text-v1.txt');png=RUN/('source-pdf'+str(n)+'-v1.png')
 write(txt,reader.pages[n-1].extract_text());assert not png.exists()
 bitmap=document[n-1].render(scale=1.8);bitmap.to_pil().save(str(png));bitmap.close()
 pages.append(dict(pdf_page=n,printed_page=n-12,text_path=txt.as_posix(),text_sha256=sha(txt),image_path=png.as_posix(),image_sha256=sha(png)))
document.close()
write(CONTRACT/'lookahead-reference-source-p277-v1.txt',reader.pages[276].extract_text())
write(CONTRACT/'source-fingerprint-v1.json',dict(title='Online Learning: A Modern Introduction Using Convex Optimization',version='arXiv:1912.13213v10',version_date='2026-06-21',
 url='https://arxiv.org/pdf/1912.13213v10',pdf_path=PDF.as_posix(),pdf_sha256=sha(PDF),source_pages=pages,
 maintext='printed8-22/PDF20-34 before Section2.4 History Bits on PDF34',history='2.4 begins PDF34; prose/history separate',
 independent_problems='2.1-2.5 printed23/PDF35 optional/planned; proof-left-as-exercise maintext remains required',
 future_dependency_reference='PDF277 Section15.5.1/Algorithm15.8/Theorem15.30 is read only to classify Chapter2lookahead claim, not a Chapter15 proof task'))
for name in ['source-navigation-draft-v1.json','unnumbered-source-audit-draft-v2.json']:
 p=ROOT/'runs/online-ch2-enumeration-20261005'/name
 write(CONTRACT/('historical-'+name),p.read_bytes())
fixed();print('Chapter2 bootstrap: prior current Chapter1 gate verified,',len(paths),'old RAW files frozen,16source pages freshly extracted/rendered, actual OWN task created.')
