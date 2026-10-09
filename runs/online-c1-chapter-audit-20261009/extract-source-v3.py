from common_v1 import *
from pypdf import PdfReader
fixed()
reader=PdfReader(str(PDF));source=[]
for n in range(13,20):
    txt=RUN/('source-pdf'+str(n)+'-text-v1.txt');png=RUN/('source-pdf'+str(n)+'-v1.png')
    write(txt,reader.pages[n-1].extract_text());assert not png.exists()
    gate('source-render-pdf'+str(n)+'-v3','pdftoppm','-f',str(n),'-l',str(n),'-singlefile',
        '-r','130','-png',PDF,png.with_suffix(''))
    assert png.exists()
    source.append(dict(pdf_page=n,printed_page=n-12,text_path=txt.as_posix(),text_sha256=sha(txt),
        image_path=png.as_posix(),image_sha256=sha(png),maintext=n<=18,
        history_exercises_on_pdf19_separately_optional=True))
write(CONTRACT/'source-fingerprint-v1.json',dict(title='Online Learning: A Modern Introduction Using Convex Optimization',
    version='arXiv:1912.13213v10',version_date='2026-06-21',url='https://arxiv.org/pdf/1912.13213v10',
    pdf_path=PDF.as_posix(),pdf_sha256=sha(PDF),source_pages=source,
    maintext_ends_at='printed6/PDF18 before 1.1 History Bits; PDF19 historical continuation and independent Problems1.1/1.2 optional',
    rendering='Existing Poppler pdftoppm; unavailable pypdfium2 v2 failure retained; no installation/source edit'))
fixed()
print('Seven current original source pages extracted and rendered; personal pixel inspection still required.',flush=True)
