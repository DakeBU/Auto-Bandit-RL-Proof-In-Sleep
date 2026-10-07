"""Render the fixed PDF with the configured bundled dependency runtime."""
from common_v1 import *
import pypdfium2 as pdfium
fixed();passed('prepare-contract-v1-01')
source=load(CONTRACT/'source-card-v1.json');assert sha(source['cached_PDF'])==source['SHA256']
pdf=pdfium.PdfDocument(source['cached_PDF']);rows=[]
for page in [28,31,32,33]:
 p=RUN/f'source-pdf{page}-v1.png';assert not p.exists();pdf[page-1].render(scale=1.7).to_pil().save(p)
 rows.append(dict(pdf_page=page,path=p.as_posix(),sha256=sha(p)))
write(RUN/'source-image-bindings-v1.json',dict(PDF_sha256=source['SHA256'],status='actual fixed PDF images; root/reviewer pixel inspection pending',images=rows))
print('Four actual source PDF page images rendered without installing/upgrading dependencies.')
