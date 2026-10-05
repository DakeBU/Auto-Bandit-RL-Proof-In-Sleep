"""Add leading qualification only after contract stabilization, preserving all actual code."""
from pathlib import Path
import hashlib,json,re,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header,_strip_lean_comments
run=Path(__file__).parent;load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
freeze=load(run/'draft-freeze-v1.json');assert load(run/'contract-binding-audit-v1.json')['status']=='passed'
p=Path('BanditRLProof/OnlineConvexOptimality.lean');original=run/'original-OnlineConvexOptimality.lean.txt'
assert sha(p)==freeze['module'][p.as_posix()]==sha(original)
comment='''Source: Orabona, Online Learning, arXiv:1912.13213v10, Theorem 2.8
and the following unnumbered interior-gradient-zero consequence; printed p.11,
PDF p.23. The actual terminal explicitly generalizes source neighborhood
convexity to convexity only on V. U is arbitrary open, contains V and supplies
finite values and differentiability of canonical F(z)=(f z).toReal. Finite
embeddings on U justify that derivative locally; no global finite/noBottom
or convexity premise outside U is added. This is not equivalence of premise sets.
minOn_real_iff_gradient is an everywhere-real library helper on V, with x in V
and an ambient derivative at x; no open-set or EReal bridge premise. The finite
minimum-order helper needs finite values only on V and explicit x membership,
not convexity, openness or differentiability. These are not printed theorems.
IsMinOn compares values but does not supply membership. Boundary minima need
only nonnegative feasible inner products; zero-gradient iff additionally needs
ambient interior V. No existence, uniqueness, closedness or boundedness claim.
Complete real inner-product spaces explicitly generalize source Euclidean spaces.
All four existing headers/proof tokens and public canary bytes are preserved.'''
p.write_bytes(('/-\n'+comment+'\n-/\n').replace('\n','\r\n').encode()+original.read_bytes())
tokens=lambda s:re.sub(r'\s+',' ',_strip_lean_comments(s)).strip()
assert tokens(p.read_text(encoding='utf-8'))==tokens(original.read_text(encoding='utf-8'))
for n,h in freeze['headers'].items():assert hashlib.sha256(lean_declaration_header(p,n).encode()).hexdigest()==h
for q,h in freeze['canary'].items():assert sha(q)==h
out=run/'public-comment-delta-v1.json';assert not out.exists()
with out.open('w',encoding='utf-8',newline='\n') as f:
 json.dump(dict(status='passed',original_module_sha256=sha(original),qualified_module_sha256=sha(p),frozen_headers=freeze['headers'],
  all_code_tokens_unchanged=True,canary_bytes_unchanged=True,retained_proofs=4,new_proofs=0,leading_comment_only=True),f,indent=2);f.write('\n')
print('Leading source qualification only; all4headers/proof tokens/canary bytes unchanged.')
