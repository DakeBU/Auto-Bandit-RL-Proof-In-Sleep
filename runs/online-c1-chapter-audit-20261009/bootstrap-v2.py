from pathlib import Path
import subprocess,json,hashlib,sys

ROOT=Path(__file__).resolve().parents[2]
RUN=Path(__file__).resolve().parent
CONTRACT=ROOT/'docs/contracts/online-c1-chapter-audit-v1'
BASE='a03f304522ed30ee34d43b38bd67deffbbf3b08f'
BRANCH='codex/research-online-c1-chapter-audit'
assert Path.cwd()==ROOT
assert subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip()==BASE
assert subprocess.check_output(['git','branch','--show-current'],encoding='utf8').strip()==BRANCH
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(p,v):
    assert not p.exists(),p
    p.parent.mkdir(parents=True,exist_ok=True)
    p.write_bytes((v.rstrip('\n')+'\n').encode('utf8') if isinstance(v,str) else
        (json.dumps(v,ensure_ascii=False,indent=2)+'\n').encode('utf8'))
paths=[]
for d in ['BanditRLProof','Tests','research-wiki/retrieval-index','website/content']:
    paths.extend(p for p in (ROOT/d).rglob('*') if p.is_file())
paths.extend(ROOT/p for p in ['BanditRLProof.lean','Tests.lean','lean-toolchain','lakefile.lean','lake-manifest.json',
    'runs/active_frontier.json','runs/trials.jsonl','runs/lifecycle_memory.jsonl','runs/lifecycle_sessions.jsonl',
    'docs/contracts/online-book-v1/coverage.json','docs/contracts/online-book-v1/source-inventory.json',
    'website/scripts/book_registry.py'])
paths.extend(p for p in (ROOT/'docs/contracts').rglob('*') if p.is_file() and CONTRACT not in p.parents)
paths.extend((ROOT/'research-wiki/contribution-contracts').glob('*.json'))
pdf=(ROOT/'../research-online-ogd/tmp/pdfs/orabona-v10.pdf').resolve()
assert sha(pdf)=='cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17'
paths.append(pdf)
rows=[dict(path=p.resolve().as_posix(),sha256=sha(p)) for p in sorted(set(paths))]
write(RUN/'baseline-v2.json',dict(rows=rows,base=BASE,basePR=202,branch=BRANCH,
    origin_main=subprocess.check_output(['git','rev-parse','origin/main'],encoding='utf8').strip(),
    canonical_clean_at_start=True,shared_git_store=subprocess.check_output(['git','rev-parse','--git-common-dir'],encoding='utf8').strip(),
    shared_lake_link_retained=True,all_previous_source_bytes_preserved=True,
    original_start_failure_retained='start-baseline-failure-v1.md',goal_active=True))
write(RUN/'00_context.md',
    'Whole-book Goal ACTIVE. Current checkpoint: audit the ENTIRE Chapter1 maintext source mapping against all sixteen preserved original source objects and later accepted scoped packages. This is an integration/source reconciliation node; no theorem count is progress. Pin Orabona v10 exact SHA, printed1-6/PDF13-18; History1.1 and independent Problems1.1/1.2 (printed7/PDF19) remain separately optional. Re-enumerate source for omitted unnumbered results. Legacy coverage seven accepted-local is a HISTORICAL Sept14 claim, not a current fullchapter gate; preserve its receipt and repair current status only through separately reviewed version. Reuse shared Lean registry and proof terms; no perBook library or duplicate theorem. Fresh stacked base PR202 exact'+BASE+' OPEN draft unmerged; canonical origin/main6847 clean. No merge/deployment/main/live update. Distinct automated decoder/reviewer required by repository skill; reused actors disclose prior history, requested GPT6Astra/medium, no runtime/human/external attestation. Root director/architect/formalizer phases may share actor. No optional parallel theorem writing. Chapter1 fullgate required; Chapter2 partial, C3-16 unenumerated/null and necessary appendices required. Preserve global SGB frontier/trials/retrieval, protected/private/frozen/generated paths. Bootstrap v1 wrong memory extension failed before baseline emission; v2 resumes the inventory only.')
write(RUN/'10_director-draft-v1.md',
    'Select fullChapter1 source reconciliation before another helper. Enumerate exact formal statements/definitions/performance claims and necessary source proof estimates, join each to actual public TYPE/VALUE and source-reviewed receipts. Freeze objects, quantifier/algorithm/initialization/feedback/normalization/asymptotic signature and closure mechanism. Literal ordinary-limit definition, upper predicate and separately reviewed proposed correction remain distinct. The bounded same-FTL obstruction is a counterexample, not a proof of false universal convergence. Review each original mandatory claim as supplied, missing, false as written, or represented with explicit delta. Do not delete difficult obligations or promote stale receipt language. Only after semantic contract review select dependency-ready finite closure/audit leaves; preserve actual failures/history.')
from pypdf import PdfReader
import pypdfium2 as pdfium
reader=PdfReader(str(pdf));document=pdfium.PdfDocument(str(pdf))
source=[]
for n in range(13,20):
    txt=RUN/('source-pdf'+str(n)+'-text-v1.txt');image=RUN/('source-pdf'+str(n)+'-v1.png')
    write(txt,reader.pages[n-1].extract_text())
    assert not image.exists()
    bitmap=document[n-1].render(scale=1.8);bitmap.to_pil().save(str(image));bitmap.close()
    source.append(dict(pdf_page=n,printed_page=n-12,text_path=txt.as_posix(),text_sha256=sha(txt),
        image_path=image.as_posix(),image_sha256=sha(image),maintext=n<=18,
        history_exercises_on_pdf19_separately_optional=True))
document.close()
write(CONTRACT/'source-fingerprint-v1.json',dict(title='Online Learning: A Modern Introduction Using Convex Optimization',
    version='arXiv:1912.13213v10',version_date='2026-06-21',url='https://arxiv.org/pdf/1912.13213v10',
    pdf_path=pdf.as_posix(),pdf_sha256=sha(pdf),source_pages=source,
    maintext_ends_at='printed6/PDF18 before 1.1 History Bits; PDF19 historical continuation and independent Problems1.1/1.2 optional'))
print('Corrected baseline captured:',len(rows),'immutable files; seven source pages freshly extracted/rendered.',flush=True)
