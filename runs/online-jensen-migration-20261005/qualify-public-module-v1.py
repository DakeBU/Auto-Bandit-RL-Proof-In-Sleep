"""Prepend source/scope qualification and preserve both exact original proof bodies."""
from pathlib import Path
import hashlib,json
run=Path(__file__).parent;module=Path('BanditRLProof/OnlineJensen.lean')
original=(run/'original-OnlineJensen.lean.txt').read_bytes();assert module.read_bytes()==original
assert json.loads((run/'contract-binding-audit-v1.json').read_text(encoding='utf-8'))['status']=='passed'
comment='''/-
Orabona v10 Theorem 2.9, printed p.11/PDF p.23, and its required library
negative-part producer. Two retained proofs, not two printed source results.
Source E[X] exists is interpreted as ordinary finite Lebesgue coordinate
expectations; finite-dimensional coordinate integrability is genuine Bochner
Integrable, not the total nonintegrable-zero fallback or a principal value.
Actual public scope is finite-dimensional real normed E with measurable/Borel
structure, including the source Euclidean setting; no supplied CompleteSpace
or inner-product parameter and no arbitrary infinite-dimensional claim.
The proof produces finite negative part using an integrable affine minorant.
Positive-infinite loss expectation is allowed. Otherwise it produces an actual
integrable real loss representative and its original nonclosed epigraph mean.
No loss-integrability, closedness, lsc, full-dimensional domain or finite-support
law assumption is added. Both-infinite total subtraction is unreachable here.
All original headers/proof bytes and whole probability canary remain fixed.
Chapter 2 and the whole Chapters 1-16 Goal remain incomplete.
-/
'''
module.write_bytes(comment.encode('utf-8')+original)
out=run/'public-comment-qualification-v1.json';assert not out.exists()
with out.open('w',encoding='utf-8',newline='\n') as f:
 json.dump(dict(path=module.as_posix(),original_sha256=hashlib.sha256(original).hexdigest(),qualified_sha256=hashlib.sha256(module.read_bytes()).hexdigest(),delta='leading source/scope qualification comment only',exact_original_bytes_retained_as_suffix=True),f,indent=2);f.write('\n')
print('Source/scope comment added; exact two original proof bodies remain fixed.')
