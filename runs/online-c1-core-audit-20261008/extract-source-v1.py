from common_v1 import *
from pypdf import PdfReader
import pypdfium2 as pdfium

fixed()
reader=PdfReader(str(PDF));document=pdfium.PdfDocument(str(PDF))
rows=[]
for n in [13,14,15,16]:
    text=reader.pages[n-1].extract_text()
    p=RUN/('source-pdf'+str(n)+'-text-v1.txt');write(p,text)
    page=document[n-1];bitmap=page.render(scale=2);png=RUN/('source-pdf'+str(n)+'-v1.png')
    assert not png.exists();bitmap.to_pil().save(png)
    rows.append(dict(pdf_page=n,printed_page=n-12,text_path=p.as_posix(),text_sha256=sha(p),
        original_render_path=png.as_posix(),render_sha256=sha(png)))
write(RUN/'source-extraction-v1.json',dict(pdf_sha256=sha(PDF),page_count=len(reader.pages),rows=rows,
    actual_cached_version_reverified=True,original_PDF_unmodified=True))
print('Actual pinned source pages13–16 extracted and rendered; explicit text and pixel review next.')
