from common import *
sys.path.insert(0, str(ROOT))
from tools.abrl_lifecycle import statement_hash
context = '''import BanditRLProof.OnlineOptimalStep
import BanditRLProof.OnlineAdaptiveOSD

noncomputable section
open Set Finset BanditRL.OnlineConvex BanditRL.OnlineAdaptiveOSD
namespace BanditRL.OnlineAdaptiveBenchmark
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
'''
write(CONTRACT/'benchmark-context-draft-v1.lean.txt', context)
image = '{b : ℝ | ∃ η : ℝ, 0 < η ∧ b = BanditRL.OnlineOptimalStep.upperBound (D ^ 2) S η}'
texts = {
'benchmark_isGLB': '''theorem benchmark_isGLB (D S : ℝ) (hD : 0 ≤ D) (hS : 0 ≤ S) :
    IsGLB '''+image+''' (D * Real.sqrt S) := by
''',
'source_benchmark_value': '''theorem source_benchmark_value (D S : ℝ) (hD : 0 ≤ D) (hS : 0 ≤ S) :
    D * Real.sqrt (2 * S) = Real.sqrt 2 * sInf
      '''+image+''' := by
''',
'benchmark_attained_iff': '''theorem benchmark_attained_iff (D S : ℝ) (hD : 0 ≤ D) (hS : 0 ≤ S) :
    (∃ η : ℝ, 0 < η ∧ BanditRL.OnlineOptimalStep.upperBound (D ^ 2) S η = D * Real.sqrt S) ↔
      (0 < D ∧ 0 < S) ∨ (D = 0 ∧ S = 0) := by
''',
'benchmark_positive_minimum': '''theorem benchmark_positive_minimum (D S : ℝ) (hD : 0 < D) (hS : 0 < S) :
    0 < D / Real.sqrt S ∧
    BanditRL.OnlineOptimalStep.upperBound (D ^ 2) S (D / Real.sqrt S) = D * Real.sqrt S ∧
    ∀ η : ℝ, 0 < η →
      D * Real.sqrt S ≤ BanditRL.OnlineOptimalStep.upperBound (D ^ 2) S η ∧
      (BanditRL.OnlineOptimalStep.upperBound (D ^ 2) S η = D * Real.sqrt S ↔
        η = D / Real.sqrt S) := by
'''}
source = (CONTRACT/'specialization-source_theorem4_14-header-draft-v1.lean.txt').read_text(encoding='utf8')
source = source.replace('theorem source_theorem4_14', 'theorem source_theorem4_14_infimum', 1)
source = source.rstrip()[:-len(':= by')].rstrip()
source += ''' ∧
    D * Real.sqrt (2 * energy V (Real.sqrt 2 / 2) D loss x₁ p T) =
      Real.sqrt 2 * sInf {b : ℝ | ∃ η : ℝ, 0 < η ∧
        b = BanditRL.OnlineOptimalStep.upperBound (D ^ 2)
          (energy V (Real.sqrt 2 / 2) D loss x₁ p T) η} := by
'''
texts['source_theorem4_14_infimum'] = source
headers = {}
for name, text in texts.items():
    path = CONTRACT/('benchmark-'+name+'-header-draft-v1.lean.txt')
    write(path, text)
    headers[name] = dict(path=path.as_posix(), raw_sha256=sha(path),
        normalized_statement_hash=statement_hash(text.rstrip()[:-len(':= by')].rstrip()))
write(CONTRACT/'benchmark-fingerprints-draft-v1.json', dict(headers=headers,
    context_sha256=sha(CONTRACT/'benchmark-context-draft-v1.lean.txt'),
    scope='Five complete benchmark/attainment/repaired source-conjunction draft headers, no proof bodies.'))
neutral0 = (CONTRACT/'specialization-neutral-packet-v2.lean.txt').read_text(encoding='utf8')
neutral = neutral0.split('\ntheorem certificate_1')[0]
neutral += '\nnoncomputable def B (A S η : ℝ) : ℝ := A / (2 * η) + η * S / 2\n'
import re
for i, (name, text) in enumerate(texts.items(), 1):
    text = text.replace('theorem '+name, 'theorem certificate_'+str(i), 1)
    text = text.replace('BanditRL.OnlineOptimalStep.upperBound', 'B')
    for before, after in {'regret':'F', 'energy':'Q', 'LegalFeedback':'L'}.items():
        text = re.sub(r'\b'+before+r'\b', after, text)
    neutral += '\n'+text.rstrip()[:-len(':= by')].rstrip()+'\n'
neutral += '\nend NeutralDynamics\n'+neutral0.split('end NeutralDynamics\n', 1)[1]
write(CONTRACT/'benchmark-neutral-packet-v1.lean.txt', neutral)
write(CONTRACT/'benchmark-source-card-draft-v1.md', '''# Separate exact infimum/attainment repair contract

Pinned Orabona v10 2026-06-21 SHA cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17, Theorem4.14 printed40/PDF52. Original unchanged. ROOT again personally viewed original PDF52 in this draft round. The source displays D sqrt(2S)=sqrt2 min_(eta>0)[D²/(2eta)+eta S/2]. The separate mathematical repair review potential-canary-BODY-minimum-review-v1 accepted the all-nonnegative infimum interpretation and exact attainment classification, not any Lean BODY. No author endorsement or published erratum is claimed. This is distinct from the rejected and withdrawn false missing-/2 allegation on printed14.

Freeze S as one realized energy coefficient and D>=0. For all D,S>=0, the positive-eta image of shared OnlineOptimalStep.upperBound(D²) S has greatest lower bound D sqrtS. The factor sqrt2 produces D sqrt(2S); source_benchmark_value expresses the corrected equality using real sInf and must prove nonempty image/boundedness through IsGLB, not rely on a junk empty-set value. Attainment holds iff both coefficients positive or both zero. The positive case has unique eta=D/sqrtS, its exact value and the full all-positive-eta lower-bound/equality iff certificate. At D>0,S0 and D0,S>0 the infimum0 is not attained; existing shared strict-improvement lemmas give direct obstructions. Bothzero every positive eta gives0 via existing zero_coefficients. These source-compatible boundary cases must remain included; no D/S positivity may be added to the whole regret guarantee.

The fifth header conjoins the complete already-drafted explicit-convex source Theorem4.14 same-run performance bound with the repaired sqrt2*infimum equality, using that very run's observed energy. This combines claims rather than replacing a performance guarantee by scalar algebra. The original literal attained-minimum statement is not certified in false one-zero regimes. Source convexity, actual-prefix legality, initial/comparator feasibility and shared Domain remain exactly as in the four performance contracts. Canonical policy can be instantiated using actual canonical_feedback; no separate learner, future-energy schedule or cross-rerun optimization is inferred.

Initial DAG: existing OnlineOptimalStep.lower_bound/distance_energy_argmin/optimal_unique/zero_distance_decreases/zero_energy_decreases/zero_coefficients -> benchmark_isGLB and exact attainment/positive minimum; benchmark_isGLB -> source_benchmark_value via IsGLB.csInf_eq and sqrt_mul; source_theorem4_14 plus actual energy_nonneg plus source_benchmark_value -> complete repaired source conjunction. Source wrapper dependency must actually compile and be BODY-reviewed before final conjunction proving. Four scalar headers and full final conjunction need neutral reconstruction/anti-anchored exact CONTRACT review and finite leaf windows before production. New module proposed OnlineAdaptiveBenchmark.lean, pinned existing shared imports only, no old-source mutation or toolchain/dependency change.

All package/algorithm canary/combined root Tests harness/axiom/registry reader/site/native/delivery gates remain required. Chapter2 required forward dependency only, no Chapter4 task/gate/count or whole Goal completion.
''')
write(CONTRACT/'benchmark-conversion-window-draft-v1.md', '''Propose one new shared module, no existing production changes. Prove IsGLB first: lower_bound on A=D², sqrt_sq hD; greatestness by actual optimum for D,Spositive, bothzero eta1, and explicit arbitrarily small values for one-zero cases. Preserve the zero regimes and no canceled sqrtS at S0. Next sInf value uses IsGLB.csInf_eq with witness eta1 and sqrt_mul2; attainment iff uses existing strict-improvement lemmas to contradict an attained lower value in each one-zero regime; positive minimum uses existing distance_energy_argmin/optimal_unique. Final complete source conjunction depends on separately compiled/BODY-reviewed source_theorem4_14 and the actual same-run energy_nonneg. Freeze all five exact headers/context; only dependency-ready finite groups after semantic CONTRACT review. No imported theorem is silently weakened; required literal-source mismatch/repair remains explicit.
''')
probe = context
for name, text in texts.items():
    stmt = text.rstrip()[len('theorem '+name+' '):-len(':= by')].strip()
    probe += '#check (∀ '+stmt.replace(' :\n', ',\n', 1)+')\n'
probe += '''#check BanditRL.OnlineOptimalStep.lower_bound
#check BanditRL.OnlineOptimalStep.distance_energy_argmin
#check BanditRL.OnlineOptimalStep.optimal_unique
#check BanditRL.OnlineOptimalStep.zero_distance_decreases
#check BanditRL.OnlineOptimalStep.zero_energy_decreases
#check IsGLB.csInf_eq
end BanditRL.OnlineAdaptiveBenchmark
'''
write(RUN/'BenchmarkTypeProbeV1.lean', probe)
code, out = capture('benchmark-type-probe-v1', 'lake', 'env', 'lean', RUN/'BenchmarkTypeProbeV1.lean')
print('\n'.join(out.splitlines()[-25:]), flush=True)
print('neutral_packet', sha(CONTRACT/'benchmark-neutral-packet-v1.lean.txt'), flush=True)
