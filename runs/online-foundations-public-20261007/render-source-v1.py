from common_v1 import *
fixed()
runtime='C:/Users/admin/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/python.exe'
script=RUN/'render-source-child-v1.py'
write(script,'''from pathlib import Path
import hashlib,json
import pypdfium2 as pdfium
p=Path('../research-online-ogd/tmp/pdfs/orabona-v10.pdf')
assert hashlib.sha256(p.read_bytes()).hexdigest()=='cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17'
d=pdfium.PdfDocument(str(p)); out=Path('runs/online-foundations-public-20261007/source-pdf16-v1.png'); assert not out.exists()
page=d[15]; bitmap=page.render(scale=2); bitmap.to_pil().save(str(out)); page.close(); d.close()
print(json.dumps(dict(pdf_page=16,render_scale=2,image=str(out),sha256=hashlib.sha256(out.read_bytes()).hexdigest())))
''')
gate('source-render-v1',runtime,'-B','-X','utf8',script)
fixed();print('Actual pinned PDF16 rendered; root visual read required separately.')
