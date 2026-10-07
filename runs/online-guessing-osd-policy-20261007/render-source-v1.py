from pathlib import Path
import hashlib,json
import pypdfium2 as pdfium
root=Path.cwd();run=root/'runs/online-guessing-osd-policy-20261007'
pdf=root/'../research-online-ogd/tmp/pdfs/orabona-v10.pdf'
assert hashlib.sha256(pdf.read_bytes()).hexdigest()=='cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17'
document=pdfium.PdfDocument(pdf);rows=[]
for physical in [13,27,31,32]:
 path=run/f'source-pdf{physical}-v1.png';assert not path.exists()
 document[physical-1].render(scale=1.55).to_pil().save(path)
 rows.append(dict(physical_page=physical,path=path.relative_to(root).as_posix(),sha256=hashlib.sha256(path.read_bytes()).hexdigest()))
output=run/'source-render-v1.json';assert not output.exists()
output.write_bytes((json.dumps(dict(PDF_sha256=hashlib.sha256(pdf.read_bytes()).hexdigest(),actual_renderer='bundled pypdfium2',rows=rows),indent=2)+'\n').encode())
print('Four current pinned-source pages actually rendered; pixel review separate.')
