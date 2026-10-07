"""Correct only three pinned API namespaces; both original failed attempts retained."""
from common_v2 import *
fixed();passed('target-types-v1-01');assert load(RUN/'pinned-APIs-v1-01-exit.json')['exit_code']==1
t=(RUN/'leaves/pinned-APIs-v1.lean').read_text(encoding='utf-8')
for a,b in [('Set.segment','segment'),('Set.left_mem_segment','left_mem_segment'),('Set.right_mem_segment','right_mem_segment')]:t=t.replace(a,b)
write(RUN/'leaves/pinned-APIs-v2.lean',t)
write(RUN/'readiness-API-repair-v3.json',dict(actual_failed_attempt='prepare-readiness-v2-01',actual_nested_failure='pinned-APIs-v1-01',cause='Three guessed Set-qualified segment names are actually global in pinned Mathlib.',resolution='Correct exact three namespace references in new API probe, leave all frozen source/definition/target proposition bytes unchanged.',target_types_v1_actual_passed=True,mathematical_repairs=[],old_API_probe_logs_preserved=True))
gate('pinned-APIs-v2-01','lake','env','lean',RUN/'leaves/pinned-APIs-v2.lean')
write(RUN/'source-visual-read-v1.json',dict(path=load(CONTRACT/'source-card.json')['image'],sha256=load(CONTRACT/'source-card.json')['image_sha256'],actual_view_image_original=True,actor='/root',finding='Fresh actual printed19/PDF31 originalpixels: realR2/absfirstcoordinate/convex/notdifferentiableentire(0,0)-(0,1)segment; not EReal or verticalrestriction derivative.'))
write(RUN/'readiness-v1.json',dict(status='target-types-and-retrieval-checked',proof_compiled=False,source_package_accepted=False,target_type_checks=3,pinned_API_checks=15,reuse_decision='adapt_existing',route='Pinned convexrealnorm through PiLp projection; horizontal derivative restriction contradicts scalarabs at0; trueclosedsegment membership coordinate0.',external_imports_added=False,new_generic_mathlib_leaf=False,initial_DAG=(CONTRACT/'initial-dependency-DAG.json').as_posix(),chapter_complete=False,goal_complete=False))
write(RUN/'private-workflow-binding-v1.json',dict(path='E:/ABRL/papers/long/main/harness.tex',sha256=sha('E:/ABRL/papers/long/main/harness.tex'),private_content_not_copied=True,paper_title='ABRL: A Target-Faithful Autoformalization Harness and Lean 4 Library for Bandit and Reinforcement Learning Theory',commands_versus_file_actor_conventions_distinct=True))
headers=load(CONTRACT/'headers.json')
write(CONTRACT/'native-statement-fingerprints-v1.json',{n:hashlib.sha256(re.sub(r'\s+',' ',r['statement']).strip().encode()).hexdigest() for n,r in headers.items()})
packet='''Restricted neutral packet. RequestedGPT6Astra/medium. Read ONLY this packet; no repository/source/history/proof/prior verdict. Decode definition Q and THREE prospective propositions P1/P2/P3 separately in natural language/LaTeX with all seven semantic slots. These are fully elaborated target PROPOSITIONS and actual definition, not already proved theorem bodies. Write ONLY blind-reconstruction-v1.md and blind-receipt-v1.json adjacent to packet, exact raw packet/report SHA, actor/requested settings, no runtime attestation/source acceptance.

```lean
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Normed.Module.Convex
def Q (x : EuclideanSpace ℝ (Fin 2)) : ℝ := |x 0|
-- P1
ConvexOn ℝ Set.univ Q
-- P2
∀ x : EuclideanSpace ℝ (Fin 2), x 0 = 0 → ¬ DifferentiableAt ℝ Q x
-- P3
ConvexOn ℝ Set.univ Q ∧
∀ x ∈ segment ℝ (0 : EuclideanSpace ℝ (Fin 2)) (PiLp.single 2 1 1),
  ¬ DifferentiableAt ℝ Q x
```

EuclideanSpace real Fin2 is the actual L2-normed two-dimensional real space. First coordinate has Lean index0, second index1. PiLp.single2 index1 1 is (0,1). segment is CLOSED: {z | existsa,b:real,0<=a and0<=b anda+b=1 anda*x+b*y=z}. DifferentiableAt real is AMBIENT Frechet differentiability on real2, not DifferentiableWithinAt and not differentiability of Q restricted to that segment. P2 quantifies all second coordinates with no interval premise. Q is everywhere actual real-valued, no EReal.toReal. No stochastic/algorithm/feedback/regret claim. Do not infer a source or source completion.

Actual target-proposition/definition elaboration output (neutral names):
```text
'''
actual=(RUN/'target-types-v1-01.log').read_text(encoding='utf-8').replace(PRE+'coordinateAbsolute','Q').replace('coordinateAbsolute','Q')
packet+=actual+'\n```\n';assert 'Orabona' not in packet and PRE not in packet
write(RUN/'blind-packet-v1.md',packet)
event('draft',dict(source=(CONTRACT/'source-card.json').as_posix(),target_headers=(CONTRACT/'headers.json').as_posix(),proof_compiled=False,explicit_raw_and_native_normalized_fingerprints=True))
print('Draftsource/types/API/retrieval ready; neutralpacket prepared. Actualtheorem body/proving CONTRACT review pending.')
