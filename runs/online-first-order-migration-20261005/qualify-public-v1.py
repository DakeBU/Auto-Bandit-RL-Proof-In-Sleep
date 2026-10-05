"""Add source qualification only; audit all existing public code and canary bytes."""
from pathlib import Path
import hashlib,json,re,sys,subprocess
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header,_strip_lean_comments
run=Path(__file__).parent
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
freeze=load(run/'draft-freeze-v1.json')
p=Path('BanditRLProof/OnlineConvexFirstOrder.lean');original=run/'original-OnlineConvexFirstOrder.lean.txt'
assert sha(p)==freeze['module'][p.as_posix()]==sha(original)
comment='''Source: Orabona, Online Learning, arXiv:1912.13213v10, Theorem 2.7,
printed p.11 / PDF p.23. The source terminal assumes globally no negative
infinity, convexity, ambient interior of effectiveDomain and differentiability
at x. It compares every y, including the positive-infinity branch outside
the domain. The canonical real function F(z)=(f z).toReal agrees with f only
locally near x after embedding, as proved by finitePart_eventually; infinite
values are not globally replaced by zero. Complete real inner-product spaces
explicitly generalize the source Euclidean setting.
finitePart_eventually is a local representation helper; convex_gradient_lower_bound
is a generalized everywhere-real ConvexOn helper on V with x,y in V and an
ambient derivative at x. It needs neither open V nor the extended-real local
representation bridge. These helpers are not additional printed theorems.
This migration preserves all three headers, proof tokens and canary bytes.'''
p.write_bytes(('/-\n'+comment+'\n-/\n').replace('\n','\r\n').encode()+original.read_bytes())
tokens=lambda s:re.sub(r'\s+',' ',_strip_lean_comments(s)).strip()
assert tokens(p.read_text(encoding='utf-8'))==tokens(original.read_text(encoding='utf-8'))
for n,h in freeze['headers'].items():
    assert hashlib.sha256(lean_declaration_header(p,n).encode()).hexdigest()==h
for q,h in freeze['canary'].items():assert sha(q)==h
out=run/'public-comment-delta-v1.json';assert not out.exists()
with out.open('w',encoding='utf-8',newline='\n') as f:
    json.dump(dict(status='passed',original_module_sha256=sha(original),qualified_module_sha256=sha(p),
        all_code_tokens_unchanged=True,frozen_headers=freeze['headers'],canary_bytes_unchanged=True,
        retained_proofs=3,new_proofs=0,leading_comment_only=True),f,indent=2);f.write('\n')
print('Leading source qualification only; all3 headers/code tokens and canary bytes unchanged.')
