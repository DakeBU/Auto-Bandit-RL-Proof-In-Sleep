from common import *
sys.path.insert(0,str(ROOT))
from tools import abrl_lifecycle as lifecycle
fixed()
canary=CONTRACT/'canary-v1'
a='(fun t : ℕ => if t = 1 then (0 : ℝ) else 1 / 2)'
f='(fun x : ℝ => max (1 - x) 0)'
summation=f'(∑ t ∈ range 3, {a} t * {f} (0 + ∑ i ∈ range (t + 1), {a} i))'
integral=f'(∫ x in (0 : ℝ)..(0 + ∑ i ∈ range 3, {a} i), {f} x)'
main=f'''theorem nonconstant_zero_increment_canary :
    {summation} ≤ {integral} ∧
    {summation} = 1 / 4 ∧
    {integral} = 1 / 2 ∧
    {summation} < {integral} ∧
    {f} 0 ≠ {f} 1 ∧
    {a} 0 = 1 / 2 ∧ {a} 1 = 0 ∧ {a} 2 = 1 / 2'''
q='(fun x : ℝ => max (3 - x) 0)'
zero=f'''theorem zero_boundaries_canary :
    (∑ t ∈ range 0, (1 : ℝ) * {q} (2 + ∑ _i ∈ range (t + 1), (1 : ℝ))) ≤
      (∫ x in (2 : ℝ)..(2 + ∑ _i ∈ range 0, (1 : ℝ)), {q} x) ∧
    (∑ t ∈ range 3, (0 : ℝ) * {q} (2 + ∑ _i ∈ range (t + 1), (0 : ℝ))) ≤
      (∫ x in (2 : ℝ)..(2 + ∑ _i ∈ range 3, (0 : ℝ)), {q} x) ∧
    {q} 2 = 1'''
context='''import BanditRLProof.OnlineAdaptiveSummation
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section
open Set Finset MeasureTheory

namespace Tests.OnlineAdaptiveSummationCanary

end Tests.OnlineAdaptiveSummationCanary
'''
write(canary/'definition-context-draft-v1.lean.txt',context)
headers=[dict(declaration='Tests.OnlineAdaptiveSummationCanary.'+name,exact_header=h,normalized_header_sha256=lifecycle.statement_hash(h)) for name,h in [('nonconstant_zero_increment_canary',main),('zero_boundaries_canary',zero)]]
write(canary/'frozen-headers-draft-v1.json',dict(rows=headers,BODY='unwritten',state='draft'))
probe_context=context.replace('import BanditRLProof.OnlineAdaptiveSummation','import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic').replace('Tests.OnlineAdaptiveSummationCanary','NeutralSummationCanaryTypesV1')
props=[h.split(' :\n',1)[1] for h in [main,zero]]
packet=probe_context.replace('end NeutralSummationCanaryTypesV1\n','\n'.join('#check ('+p+')' for p in props)+'\nend NeutralSummationCanaryTypesV1\n')
write(RUN/'NeutralSummationCanaryTypesV1.lean',packet)
capture('canary-full-type-probe-v1','lake','env','lean',RUN/'NeutralSummationCanaryTypesV1.lean')
write(canary/'canary-intent-v1.md','''# Two concrete canary targets, draft

First full canary: initial offset zero, three increments [1/2,0,1/2], and f(x)=max(1-x,0). The weighted right-endpoint sum is exactly1/4 and the integral over the same cumulative endpoints is exactly1/2, so the inequality is strict. The theorem also checks f(0)!=f(1) and all three actual increments. Its inequality conjunct must directly instantiate the public production Lemma4.13; proving only the rational inequality would not meet the BODY contract. This simultaneously exercises nonconstant continuous antitone nonnegative f, repeated endpoints, both nonzero increments and the initial zero endpoint. No regret algorithm claim.

Second full canary separately instantiates the public theorem at horizon0 with positive offset2, unconstrained positive increment stream1 and f(x)=max(3-x,0), and at horizon3 with zero increments and the same offset/function. It also checks f(2)=1. Both inequality conjuncts must use the public theorem, even though the resulting zero comparisons could be proved by simplification alone. These are boundary canaries, not nondegeneracy evidence by themselves.

Current exact complete Prop probe uses only Mathlib imports because production BODY is absent; this proves type well-formedness only. Final Test context adds the reviewed public production import, with no local definitions or hidden scoped premises. No Test BODY is authored before a distinct source contract review, and public Test integration requires separately scoped review. Frozen exact headers are in the adjacent JSON. Future BODY must retain these complete conjuncts, use the production terminal for all three bound instantiations and compute exact endpoints/integral separately. Source identity, chapter status and prior verdict are removed from the neutral type packet for distinct reconstruction.
''')
fixed()
print('Canary draft full types prepared; no proof authored.',flush=True)
