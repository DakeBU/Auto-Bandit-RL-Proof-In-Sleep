from common_v2 import *
from pypdf import PdfReader
import pypdfium2
p=Path('../research-online-ogd/tmp/pdfs/orabona-v10.pdf');assert sha(p)=='cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17'
write(RUN/'source-printed19-pdf31.txt',PdfReader(str(p)).pages[30].extract_text())
img=Path('tmp/online-lipschitz-source-pdf31-v1.png');assert not img.exists()
doc=pypdfium2.PdfDocument(str(p));page=doc[30];bitmap=page.render(scale=1.7);bitmap.to_pil().save(str(img));bitmap.close();page.close();doc.close()
write(RUN/'source-cache-read-v1.json',dict(version='arXiv1912.13213v10,21June2026',PDF=p.as_posix(),sha256=sha(p),printed_page=19,PDF_page=31,image=img.as_posix(),image_sha256=sha(img),actually_viewed_by_root=False,source='Definition2.29/Theorem2.30; adjacent unnumbered nondifferentiability example and Lemma2.31 remain required separate obligations.',chapter_complete=False,goal_complete=False))
print('Exact source PDF rehashed, printed19 extracted and original page rendered; actual visual read still required.')
