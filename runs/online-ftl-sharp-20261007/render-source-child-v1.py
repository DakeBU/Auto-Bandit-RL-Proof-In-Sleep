from pathlib import Path
import hashlib,json,pypdfium2 as pdfium
p=Path('../research-online-ogd/tmp/pdfs/orabona-v10.pdf')
assert hashlib.sha256(p.read_bytes()).hexdigest()=='cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17'
d=pdfium.PdfDocument(str(p))
for n in [16,17,18]:
 out=Path('runs/online-ftl-sharp-20261007/source-pdf%d-v1.png'%n);assert not out.exists()
 page=d[n-1];page.render(scale=2).to_pil().save(str(out));page.close();print(json.dumps(dict(pdf_page=n,image=str(out),sha256=hashlib.sha256(out.read_bytes()).hexdigest())))
d.close()
