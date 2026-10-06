from common_v2 import *
from pypdf import PdfReader
import shutil
p=Path('../research-online-ogd/tmp/pdfs/orabona-v10.pdf');assert sha(p)=='cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17'
write(RUN/'source-printed19-pdf31.txt',PdfReader(str(p)).pages[30].extract_text())
img=Path('tmp/online-lipschitz-source-pdf31-v1.png');assert not img.exists()
gate('source-render-poppler-v2-01',shutil.which('pdftoppm'),'-f','31','-l','31','-singlefile','-r','130','-png',p,img.with_suffix(''))
assert img.exists()
write(RUN/'source-cache-read-v2.json',dict(version='arXiv1912.13213v10,21June2026',PDF=p.as_posix(),sha256=sha(p),printed_page=19,PDF_page=31,image=img.as_posix(),image_sha256=sha(img),actually_viewed_by_root=False,source='Definition2.29/Theorem2.30; adjacent unnumbered nondifferentiability example and Lemma2.31 remain required separate obligations.',source_read_v1_failure='DefaultPython38 pypdfium2 ModuleNotFoundError before source writes; existing Poppler used, no installation or source modification.',chapter_complete=False,goal_complete=False))
print('Exact source cache rehashed/read/rendered by installed Poppler; actual root visual read stillrequired.')
