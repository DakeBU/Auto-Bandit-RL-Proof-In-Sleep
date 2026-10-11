from common import *
sys.path.insert(0, str(ROOT))
from tools.abrl_lifecycle import statement_hash
assert sha(PDF) == PDF_SHA
context = CONTRACT/'algorithm-definition-context-draft-v2.lean.txt'
assert sha(context) == '21d6e4fac472283549824746a573d44e1c5f34ad007f14f7f2ee7bc294676e71'
headers = {}
for name, alpha, canonical, rhs in [
    ('source_eq4_4', '1', False, '(3 / 2 : ℝ) * D * Real.sqrt (energy V 1 D loss x₁ p T)'),
    ('canonical_eq4_4', '1', True, '(3 / 2 : ℝ) * D * Real.sqrt (energy V 1 D loss x₁ BanditRL.OnlineSubgradientPolicy.canonicalPolicy T)'),
    ('source_theorem4_14', '(Real.sqrt 2 / 2)', False, 'D * Real.sqrt (2 * energy V (Real.sqrt 2 / 2) D loss x₁ p T)'),
    ('canonical_theorem4_14', '(Real.sqrt 2 / 2)', True, 'D * Real.sqrt (2 * energy V (Real.sqrt 2 / 2) D loss x₁ BanditRL.OnlineSubgradientPolicy.canonicalPolicy T)')]:
    p = 'BanditRL.OnlineSubgradientPolicy.canonicalPolicy' if canonical else 'p'
    text = 'theorem '+name+' (V : Domain (E := E)) (D : ℝ) (hD : 0 ≤ D)\n'
    text += '    (loss : ℕ → E → EReal) (x₁ : E)'+('' if canonical else ' (p : SupportPolicy (E := E))')+' (hx₁ : x₁ ∈ V.carrier)\n'
    text += '    (T : ℕ) (hconvex : ∀ t < T, IsConvexExtended (loss t))\n'
    text += '    (hloss : ∀ t < T, BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t))\n'
    if not canonical:
        text += '    (hlegal : LegalFeedback V '+alpha+' D loss x₁ p T)\n'
    text += '    (hdiam : ∀ x ∈ V.carrier, ∀ y ∈ V.carrier, ‖x - y‖ ≤ D) (u : E) (hu : u ∈ V.carrier) :\n'
    text += '    regret V '+alpha+' D loss x₁ '+p+' u T ≤\n      '+rhs+' := by\n'
    path = CONTRACT/('specialization-'+name+'-header-draft-v1.lean.txt')
    write(path, text)
    headers[name] = dict(path=path.as_posix(), raw_sha256=sha(path),
        normalized_statement_hash=statement_hash(text.rstrip()[:-len(':= by')].rstrip()))
write(CONTRACT/'specialization-fingerprints-draft-v1.json', dict(headers=headers,
    context_sha256=sha(context), boundary='Four draft complete source-facing endpoints, no proof bodies. No benchmark assertion.'))
neutral = (CONTRACT/'algorithm-neutral-packet-v1.lean.txt').read_text(encoding='utf8').split('\ntheorem certificate_one')[0]
import re
replacements = {'regret':'F', 'energy':'Q', 'output':'X', 'selected':'G',
    'eta':'R', 'LegalFeedback':'L', 'history':'H', 'state':'A'}
for i, (name, row) in enumerate(headers.items(), 1):
    text = Path(row['path']).read_text(encoding='utf8').replace('theorem '+name, 'theorem certificate_'+str(i), 1)
    for before, after in replacements.items():
        text = re.sub(r'\b'+before+r'\b', after, text)
    neutral += '\n'+text.rstrip()[:-len(':= by')].rstrip()+'\n'
neutral += '\nend NeutralDynamics\n'
write(CONTRACT/'specialization-neutral-packet-v1.lean.txt', neutral)
write(CONTRACT/'specialization-source-card-draft-v1.md', '''# Eq4.4 and Theorem4.14 source specialization contracts

Pinned Orabona arXiv:1912.13213v10,2026-06-21, PDF SHA cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17. Printed39-40/PDF51-52, actual images and extracted source already reread in this ongoing run; original unchanged. These are necessary Chapter2 forward dependencies, not Chapter4 inventory/completion.

Eq4.3 alpha1 uses D/sqrt(inclusive selected squared norms), skip current zero vector, and Eq4.4 gives (3/2) D sqrt(total energy). Theorem4.14 uses alpha=sqrt2/2 with the same recurrence, source eta=sqrt2 D/(2 sqrt(inclusive energy)), and gives D sqrt(2 total energy). Both source endpoints require convex proper extended-real losses subdifferentiable on the closed nonempty convex domain and feasible initial/comparator; explicit pairwise diameter<=D is used, not existence of a maximizing pair. Domain structural assumptions are shared in Domain. Source t1..T -> Lean t0..<T; source x_(T+1) -> outputT, energyT is the same realized selected-vector energy, not an exogenous stream or future-selected eta. The shared IsConvexExtended (convex real epigraph) is retained explicitly in all four source-facing headers, even if the general support-sufficient parent makes it redundant for proof. Per-prefix SubdifferentiableOn includes SourceProper and global supports at feasible points. Actual LegalFeedback on the played prefix allows arbitrary fixed policies; the canonical variants discharge that premise using the existing shared canonicalPolicy, not an added oracle or a new chooser.

All natural T including0 and D>=0 are included as explicit algebraic/algorithmic boundary extensions: zero feedback always skips, total division is only an observer at a zero prefix, D0 forces singleton outputs. No positive energy, gradient/Lipschitz bound, stochastic premise, off-path OracleLaw or known horizon is added. The general parent's negative terminal residual is retained there; these faithful source displays drop its nonnegative subtrahend to match their printed bound. Theorem4.14's additional printed equality to sqrt2 times an attained min is deliberately NOT claimed by these four headers. Its separately approved mathematical infimum/attainment repair still requires exact Lean contracts, proof and review. This is not an exclusion of a required source component; it is an open obligation in the same package.

Initial DAG: actual regret_bound -> source_eq4_4/source_theorem4_14 -> their canonical variants, with actual canonical_feedback supplying legality. All wrappers must use the SAME fixed alpha run in regret, energy and feedback. Parent BODY review must be favorable before any of these production BODYs. Distinct neutral reconstruction, anti-anchored CONTRACT review and finite append window are required before proving. Focused/public/axiom/fence/VALUE/BODY review and actual algorithm canary/full-package/registry/reader/site/delivery gates remain separate. Whole Goal active; chapter partial.
''')
write(CONTRACT/'specialization-conversion-window-draft-v1.md', '''One lower route proposed: source_eq4_4 specializes parent alpha1 then drops only the proven nonnegative terminal term. source_theorem4_14 specializes parent alpha=sqrt2/2, proves alpha>0 and coefficient=sqrt2 with sqrt2²=2, drops only the nonnegative terminal and rewrites sqrt(2*actual energy). Two canonical variants reuse these exact source endpoints and actual canonical_feedback. No imports/context/definitions/helpers change proposed. Four exact unchanged headers/BODYs only after distinct reconstruction, favorable parent BODY and favorable source CONTRACT edit-window review. This draft itself authorizes no production mutation. Benchmark/algorithm canary/root/registry/reader are separate windows.
''')
probe = '''import BanditRLProof.OnlineAdaptiveOSD
noncomputable section
open Set Finset BanditRL.OnlineConvex
open scoped InnerProductSpace
namespace BanditRL.OnlineAdaptiveOSD
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
local instance : DecidableEq E := Classical.decEq E
'''
for name, row in headers.items():
    raw = Path(row['path']).read_text(encoding='utf8').rstrip()
    stmt = raw[len('theorem '+name+' '):-len(':= by')].strip()
    probe += '#check (∀ '+stmt.replace(' :\n', ',\n', 1)+')\n'
probe += '#check IsConvexExtended\n#check canonical_feedback\n#check Real.sqrt_mul\n#check Real.sq_sqrt\nend BanditRL.OnlineAdaptiveOSD\n'
write(RUN/'SpecializationTypeProbeV1.lean', probe)
code, out = capture('specialization-type-probe-v1', 'lake', 'env', 'lean', RUN/'SpecializationTypeProbeV1.lean')
print(out, flush=True)
write(RUN/'director-specializations-draft-v1.md', 'Close exactly both printed adaptive performance displays on the already constructed causal run, retaining explicit source convexity and lawful canonical instantiations. Preserve the separate required min/infimum benchmark and all chapter boundaries.')
write(RUN/'architect-specializations-draft-v1.md', 'Four finite draft endpoints share actual parent and canonical_feedback, no new learner. Freeze complete statements; obtain neutral and anti-anchored review before BODY append. Actual parent dependency review remains pending.')
print('neutral_packet', sha(CONTRACT/'specialization-neutral-packet-v1.lean.txt'), flush=True)
