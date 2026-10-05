"""Add a dependency qualification comment; preserve all production code."""
from pathlib import Path
import hashlib,json,re,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header,_strip_lean_comments
run=Path(__file__).parent;sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
freeze=load(run/'draft-freeze-v1.json');assert load(run/'contract-binding-audit-v1.json')['status']=='passed'
p=Path('BanditRLProof/OnlineExpectation.lean');original=run/'original-OnlineExpectation.lean.txt'
assert sha(p)==freeze['module'][p.as_posix()]==sha(original)
comment='''Representation dependency for Orabona, Online Learning, arXiv:1912.13213v10,
Theorem 2.9, printed p.11/PDF p.23. These seven helpers and three definitions
are library foundations, not seven printed source results or Jensen acceptance.
The definitions use total ENNReal lintegrals and EReal subtraction for arbitrary
measures/functions. Mathematical signed-integral use needs an appropriate
measurable interpretation and at least one finite part. Both parts infinite
is not a legitimate signed expectation; pinned total top-top equals bottom.
Real Bochner compatibility retains actual Integrable, and the positive-infinite
branch explicitly requires finite negative part. No parent loss integrability
premise is introduced; Jensen must prove negative-part finiteness separately.
The two-atom mass-two and infinite counting-measure canaries are signed-integral
examples, not probability Jensen examples or normalized expectations.
All ten retained headers, definitions/proof tokens and canary bytes unchanged.'''
p.write_bytes(('/-\n'+comment+'\n-/\n').replace('\n','\r\n').encode()+original.read_bytes())
tokens=lambda s:re.sub(r'\s+',' ',_strip_lean_comments(s)).strip()
assert tokens(p.read_text(encoding='utf-8'))==tokens(original.read_text(encoding='utf-8'))
for n,h in freeze['headers'].items():assert hashlib.sha256(lean_declaration_header(p,n).encode()).hexdigest()==h
for q,h in freeze['canary'].items():assert sha(q)==h
out=run/'public-comment-delta-v1.json';assert not out.exists()
with out.open('w',encoding='utf-8',newline='\n') as handle:
 json.dump(dict(status='passed',original_module_sha256=sha(original),qualified_module_sha256=sha(p),frozen_headers=freeze['headers'],all_definition_proof_tokens_unchanged=True,canary_bytes_unchanged=True,retained_proofs=7,retained_definitions=3,new_proofs=0,leading_comment_only=True),handle,indent=2);handle.write('\n')
print('Leading dependency qualification only; all10headers/definition/proof tokens/canary bytes unchanged.')
