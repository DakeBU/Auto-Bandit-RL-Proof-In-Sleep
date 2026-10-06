"""Saved, versioned initializer for the next required source convention audit."""
from pathlib import Path
import hashlib,json,subprocess
r=Path(__file__).resolve().parent;old=Path('runs/online-affine-subgradient-migration-20261007')
assert Path('.').resolve()==r.parents[1]
assert subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf-8').strip()=='971fd6a2e07cced18217d5ba48dc65a64c6fb481'
assert subprocess.check_output(['git','branch','--show-current'],encoding='utf-8').strip()=='codex/research-online-lipschitz-migration'
def write(p,x):
 assert not p.exists(),p;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(x if isinstance(x,bytes) else (x.rstrip('\n')+'\n').encode())
write(r/'.gitattributes','* -text')
write(r/'run-command.py',(old/'run-command.py').read_bytes())
t=(old/'common_v2.py').read_text(encoding='utf-8')
for a,b in [('online-affine-subgradient-migration-v1','online-lipschitz-migration-v1'),('ONLINE-AFFINE-SUBGRADIENT-MIGRATION-20261007','ONLINE-LIPSCHITZ-MIGRATION-20261007'),("ROUTE='online-affine-subgradient'","ROUTE='online-lipschitz'"),('OnlineAffineSubgradient','OnlineLipschitzSubgradient'),('42da35d05a3cbc26f5ec6b5082ef9135b7d7caf7','971fd6a2e07cced18217d5ba48dc65a64c6fb481')]:t=t.replace(a,b)
compile(t,str(r/'common_v2.py'),'exec');write(r/'common_v2.py',t)
for n in ['scoped-reference-index-v1.py','preserve-native-prefix-v1.py']:
 t=(old/n).read_text(encoding='utf-8');compile(t,str(r/n),'exec');write(r/n,t)
write(r/'source-read-v1.py','''from common_v2 import *
from pypdf import PdfReader
import pypdfium2
p=Path('../research-online-ogd/tmp/pdfs/orabona-v10.pdf');assert sha(p)=='cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17'
write(RUN/'source-printed19-pdf31.txt',PdfReader(str(p)).pages[30].extract_text())
img=Path('tmp/online-lipschitz-source-pdf31-v1.png');assert not img.exists()
doc=pypdfium2.PdfDocument(str(p));page=doc[30];bitmap=page.render(scale=1.7);bitmap.to_pil().save(str(img));bitmap.close();page.close();doc.close()
write(RUN/'source-cache-read-v1.json',dict(version='arXiv1912.13213v10,21June2026',PDF=p.as_posix(),sha256=sha(p),printed_page=19,PDF_page=31,image=img.as_posix(),image_sha256=sha(img),actually_viewed_by_root=False,source='Definition2.29/Theorem2.30; adjacent unnumbered nondifferentiability example and Lemma2.31 remain required separate obligations.',chapter_complete=False,goal_complete=False))
print('Exact source PDF rehashed, printed19 extracted and original page rendered; actual visual read still required.')
''')
rows=[dict(path=p.as_posix(),sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in r.glob('*.py')]
write(r/'initialized-before-first-use-v1.json',json.dumps(dict(before_first_use=True,rows=rows),indent=2))
write(r/'readonly-bootstrap-diagnostics-v1.json',json.dumps(dict(prior_affine_delivery_not_mutated=True,mathematical_or_Lean_failure=False,diagnostics=['Exploratory rg used explicit Windows runs/online-lipschitz* path and failed os123; repeated with rg --files runs -g patterns successfully, no source mutation.','Exploratory Get-Content guessed freeze-draft-v1.py and prepare-contract-review-v1.py/prepare-body-review-v1.py; absent files gave read errors. Actual catalog identified bootstrap-v1.py/review-packets-v1.py, which were read. No gate inferred.','Exploratory chapter JSON filter guessed id key and failed KeyError; defer to actual schema inspection before editing.'],chapter_complete=False,goal_complete=False),indent=2))
print('Task-local raw-byte policy and safe shared adapters initialized before first use.')
