"""Render the unchanged frozen PDF using configured bundled document runtime."""
from common_v2 import *
import pypdfium2 as pdfium
fixed();passed('repair-contract-metadata-v2-01')
source=load(CONTRACT/'source-card.json');assert sha(source['cached_PDF'])==source['sha256']
pdf=pdfium.PdfDocument(source['cached_PDF']);images=[]
for page in [28,31,32,33]:
 path=RUN/f'source-pdf{page}-v2.png';assert not path.exists();pdf[page-1].render(scale=1.7).to_pil().save(path);images.append(dict(pdf_page=page,path=path.as_posix(),sha256=sha(path)))
write(RUN/'source-image-bindings-v2.json',dict(status='actual frozen PDF page rendering; pixel inspection pending',PDF_sha256=source['sha256'],images=images,bundled_document_runtime_only=True,no_install_or_Lean_pin_change=True,original_render_failure_preserved=True))
print('Four actual frozen-source pages rendered with configured runtime; root/reviewer pixel inspections pending.')
