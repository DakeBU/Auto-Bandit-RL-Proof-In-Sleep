from pathlib import Path
import hashlib,json
import pypdfium2 as pdfium
root=Path.cwd();assert root==Path('E:/ABRL/worktrees/research-online-book')
run=root/'runs/online-log-lower-20261008';source=root/'../research-online-ogd/tmp/pdfs/orabona-v10.pdf'
assert hashlib.sha256(source.read_bytes()).hexdigest()=='cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17'
out=run/'source-pdf16-v1.png';assert not out.exists()
doc=pdfium.PdfDocument(str(source));page=doc[15];page.render(scale=1.6).to_pil().save(out)
print(json.dumps(dict(path=out.as_posix(),sha256=hashlib.sha256(out.read_bytes()).hexdigest(),pdf_page=16,printed_page=4)))
