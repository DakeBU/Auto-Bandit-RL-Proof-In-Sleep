"""Actual existing retrieval and proposition elaboration, before semantic review/body."""
from common_v1 import *
fixed();passed('pinned-APIs-v1-01')
gate('target-types-v1-01','lake','env','lean',RUN/'leaves/target-types-v1.lean')
sys.path.insert(0,str(ROOT));from tools import bandit
import argparse
index=RUN/'retrieval-snapshot-v1';assert not index.exists()
before=sha('MANIFEST.md');indexes={p.as_posix():sha(p) for p in Path('research-wiki/retrieval-index').glob('*.json')}
bandit.RETRIEVAL_INDEX_DIR=index;bandit.MANIFEST=RUN/'reference-index-manifest-v1.md'
assert bandit.cmd_reference_index(argparse.Namespace())==0
assert sha('MANIFEST.md')==before
for p,h in indexes.items():assert sha(p)==h,p
write(RUN/'reference-index-scope-v1.json',dict(status='passed',implementation='Current tools.bandit.cmd_reference_index, explicit output-directory/MANIFEST adapter because CLI has no scoped-output option',canonical_indexes_and_MANIFEST_unchanged=True,not_a_separate_Lean_Book_registry=True,rows=[dict(path=p.as_posix(),sha256=sha(p)) for p in sorted(index.glob('*.json'))]))
for label,command,args in [
 ('mathlib-cards-v1-01','list-mathlib',[]),('paper-cards-v1-01','list-papers',[]),('weapon-cards-v1-01','list-weapons',[]),
 ('memory-countability-v1-01','search-memory',['uncountability']),('declarations-nondiff-v1-01','list-lean-decls',['nondifferentiab','--statement']),
 ('declarations-segment-v1-01','list-lean-decls',['coordinate_segment','--statement'])]:native(label,command,*args)
native('retrieval-record-v1-01','retrieval-record','--task',TASK,'--query','source real2 nonsmooth locus and closed-segment uncountability','--candidate','Cardinal.Real.Icc_countable_iff','--candidate','Set.Countable.preimage','--candidate','Set.Countable.mono','--candidate',PRE+'convex_nondifferentiable_segment','--compiled-scratch',str(RUN/'leaves/pinned-APIs-v1.lean'),'--provenance','Pinned local Mathlib source/types and actual project declarations; source v10 printed19/PDF31. No external unchecked library.','--output',str(RUN/'native-retrieval-v1.json'))
write(RUN/'readiness-v1.json',dict(status='actual-types-and-retrieval-checked',pinned_API_checks=9,target_type_checks=2,proof_compiled=False,source_package_accepted=False,reuse_decision='adapt_existing',route='Injective interval-to-source-segment embedding/countable preimage and subset obstruction; then actual accepted segment-to-nonsmooth-locus inclusion.',external_imports_added=False,new_generic_mathlib_leaf=False,new_public_definitions=0,new_public_proofs=2,chapter_complete=False,goal_complete=False))
packet='''Restricted neutral packet. Requested GPT6Astra/medium. Read ONLY this packet; no source/repository/history/proof/prior verdict. Decode P1/P2 independently in natural language/LaTeX and all seven semantic slots. Fully elaborated target PROPOSITIONS, not yet theorem bodies. Write ONLY blind-reconstruction-v1.md and blind-receipt-v1.json adjacent, recording raw packet/report SHA256 and actor/requested settings, no runtime attestation or source acceptance.

```lean
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Real.Cardinality
def Q (x : EuclideanSpace ℝ (Fin 2)) : ℝ := |x 0|
-- P1
¬ (segment ℝ (0 : EuclideanSpace ℝ (Fin 2)) (PiLp.single 2 1 1)).Countable
-- P2
ConvexOn ℝ Set.univ Q ∧
¬ ({x : EuclideanSpace ℝ (Fin 2) | ¬ DifferentiableAt ℝ Q x}).Countable
```

The space is the actual real two-dimensional Euclidean L2 plane. Lean0 is first coordinate and Lean1 second. PiLp.single2 index1 1 is(0,1). segment is CLOSED, containing convex combinations with nonnegative real weights adding to1; both endpoints included. Set.Countable means at most countable (finite sets included). DifferentiableAt real means AMBIENT Frechet differentiability at a real-plane query, not a within-segment or restricted-function derivative. Q is actual everywhere-real valued, no EReal projection. P1 is NOT a differentiability statement. P2 is a conjunction for this same Q, not existence of a different function. No exact cardinal/measure-zero/a.e/probability/algorithm/feedback claim is encoded. Inspect all semantics; do not infer a source.

Actual elaboration output with neutral definition name:
```text
'''
packet+=(RUN/'target-types-v1-01.log').read_text(encoding='utf-8').replace(PRE+'coordinateAbsolute','Q').replace('coordinateAbsolute','Q')+'\n```\n'
assert 'Orabona' not in packet and PRE not in packet
write(RUN/'blind-packet-v1.md',packet)
event('draft',dict(source=(CONTRACT/'source-card.json').as_posix(),target_headers=(CONTRACT/'headers.json').as_posix(),proof_compiled=False,raw_and_native_fingerprints_distinct=True))
print('Actual target/API/retrieval ready; neutral contract packet prepared, theorem proofs and source acceptance pending.')
