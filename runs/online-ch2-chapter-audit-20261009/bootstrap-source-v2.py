from common_v1 import *
fixed()
write(RUN/'bootstrap-source-runtime-failure-v1.json',dict(actual_command='python -B -X utf8 runs/online-ch2-chapter-audit-20261009/bootstrap-v1.py',actual_exit=1,
 error="ModuleNotFoundError: No module named 'pypdfium2'",stage='Baseline/context/OWNnew-task already created; failed before source-page extraction/rendering',
 actual_new_task_exit=load(RUN/'new-task-v1-exit.json')['actual_exit'],old_baseline_unchanged=True,
 repair='Use official load_workspace_dependencies bundled Python with verified pypdf/pypdfium2 imports; no package/toolchain installation or task recreation.'))
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
 future_dependency_reference='PDF277 Section15.5.1/Algorithm15.8/Theorem15.30 read only to classify Chapter2lookahead, not a Chapter15 proof task',
 actual_runtime=sys.executable,bootstrap_v1_exit=1,source_resume_v2_ran=True))
for name in ['source-navigation-draft-v1.json','unnumbered-source-audit-draft-v2.json']:
 p=ROOT/'runs/online-ch2-enumeration-20261005'/name
 write(CONTRACT/('historical-'+name),p.read_bytes())
fixed();print('Source resume:16 actual pages extracted/rendered; original failure retained; no old baseline/code/pin changes.')
