"""Prepend dependency qualification while retaining exact original proof bytes."""
from pathlib import Path
import hashlib,json
run=Path(__file__).parent;module=Path('BanditRLProof/OnlineConvexBarycenter.lean')
original=(run/'original-OnlineConvexBarycenter.lean.txt').read_bytes()
assert module.read_bytes()==original
assert json.loads((run/'contract-binding-audit-v1.json').read_text(encoding='utf-8'))['status']=='passed'
comment='''/-
Necessary nonclosed-convex-set barycenter dependency of Orabona v10 Theorem 2.9
(printed p.11/PDF p.23), not three printed source results or Jensen acceptance.
The AE functional-value equality helper uses a complete real normed space and
probability/integrability; the supplied functional may be zero. The geometric
helper uses finite dimension and ambient interior, producing nonzero non-strict
support at level a(x), without a measure. The actual-set barycenter retains its
finite-dimensional Borel context, probability, Integrable X and AE membership.
No closedness, full ambient interior or finite support is assumed. Its body
produces the centered proper-kernel lift, integrability, zero mean and strict
rank descent, then recurses to membership in the original set itself.
All three declaration headers and original proof bytes remain fixed in the
20261005 retained migration; Chapter 2 and the whole-book Goal remain open.
-/
'''
module.write_bytes(comment.encode('utf-8')+original)
out=run/'public-comment-qualification-v1.json';assert not out.exists()
with out.open('w',encoding='utf-8',newline='\n') as f:
 json.dump(dict(path=module.as_posix(),original_sha256=hashlib.sha256(original).hexdigest(),qualified_sha256=hashlib.sha256(module.read_bytes()).hexdigest(),delta='leading dependency qualification comment only',exact_original_bytes_retained_as_suffix=True),f,indent=2);f.write('\n')
print('Leading source-dependency comment added; exact original proof bytes retained.')
