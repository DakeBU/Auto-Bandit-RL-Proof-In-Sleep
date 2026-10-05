"""Prepend reviewed dependency qualification and preserve exact original bytes."""
from pathlib import Path
import hashlib,json
run=Path(__file__).parent;module=Path('BanditRLProof/OnlineConvexMinorant.lean')
original=(run/'original-OnlineConvexMinorant.lean.txt').read_bytes();assert module.read_bytes()==original
assert json.loads((run/'contract-binding-audit-v1.json').read_text(encoding='utf-8'))['status']=='passed'
comment='''/-
Four necessary affine-support/minorant library dependencies of Orabona v10
Theorem 2.9 (printed p.11/PDF p.23), not four printed results or Jensen acceptance.
All actual public types use finite-dimensional real normed E, without supplied
Borel/measurable/probability/CompleteSpace parameters. Finite-neighbourhood
support requires neighbourhood finiteness, produces global no-bottom, and uses
Fermat only for auxiliary identity/linear functions. Its separator's vertical
coefficient is proved negative before division; the output slope may be zero.
The two ambient-domain-interior helpers respectively retain or drop contact.
The global minorant assumes only no-bottom, convex real epigraph and nonempty
effective domain. Its body produces the intrinsic-interior affine-span
restriction, direction-space interior and actual linear extension/intercept
correction, without closedness, lsc or loss differentiability assumptions.
All four original headers/proof bytes remain fixed in the 20261005 migration.
Jensen's finite-negative-part producer, Chapter 2 and the whole Goal stay open.
-/
'''
module.write_bytes(comment.encode('utf-8')+original)
out=run/'public-comment-qualification-v1.json';assert not out.exists()
with out.open('w',encoding='utf-8',newline='\n') as f:json.dump(dict(path=module.as_posix(),original_sha256=hashlib.sha256(original).hexdigest(),qualified_sha256=hashlib.sha256(module.read_bytes()).hexdigest(),delta='leading dependency qualification comment only',exact_original_bytes_retained_as_suffix=True),f,indent=2);f.write('\n')
print('Leading dependency comment added; exact original four proof bytes retained.')
