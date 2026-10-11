from common import *
import re
sys.path.insert(0, str(ROOT))
from tools.abrl_lifecycle import statement_hash
assert sha(PDF) == PDF_SHA
context = '''import BanditRLProof.OnlineAdaptiveBenchmark
import BanditRLProof.OnlineGuessingOGD

noncomputable section
open Set Finset BanditRL.OnlineConvex BanditRL.OnlineAdaptiveOSD
namespace AdaptiveProbe
abbrev V := BanditRL.OnlineGradientDescent.unitInterval

def W : Domain (E := ℝ) where
  carrier := {0}
  nonempty := ⟨0, rfl⟩
  closed := isClosed_singleton
  convex := convex_singleton 0

def feedback (t : ℕ) : ℝ := if t = 1 then 3 else if t = 3 then -4 else 0
def loss (t : ℕ) (x : ℝ) : EReal := ((feedback t * x : ℝ) : EReal)
def policy : SupportPolicy (E := ℝ) := fun t _ _ _ => feedback t
def futureLoss (t : ℕ) (x : ℝ) : EReal := if t < 2 then loss t x else (7 : EReal)
def zeroLoss (_ : ℕ) (_ : ℝ) : EReal := 0
def zeroPolicy : SupportPolicy (E := ℝ) := fun _ _ _ _ => 0
abbrev x (α : ℝ) (t : ℕ) := output V α 1 loss (1 / 2) policy t
abbrev q (α : ℝ) (t : ℕ) := energy V α 1 loss (1 / 2) policy t
abbrev r (α : ℝ) (t : ℕ) := eta V α 1 loss (1 / 2) policy t
'''
texts = {
'loss_regular': '''theorem loss_regular (U : Domain (E := ℝ)) (t : ℕ) :
    IsConvexExtended (loss t) ∧
    BanditRL.OnlineSubgradientDescent.SubdifferentiableOn U (loss t) ∧
    ∀ z : ℝ, feedback t ∈ SourceSubdifferential (loss t) z := by
''',
'feedback_energy': '''theorem feedback_energy :
    (∀ α : ℝ, ∀ t : ℕ, selected V α 1 loss (1 / 2) policy t = feedback t) ∧
    (∀ α : ℝ, ∀ T : ℕ, T ≤ 4 →
      q α T = if T ≤ 1 then 0 else if T ≤ 3 then 9 else 25) := by
''',
'trace_canary': '''theorem trace_canary :
    x 1 0 = 1 / 2 ∧ x 1 1 = 1 / 2 ∧ x 1 2 = 0 ∧ x 1 3 = 0 ∧ x 1 4 = 4 / 5 ∧
    r 1 0 = 0 ∧ r 1 1 = 1 / 3 ∧ r 1 2 = 1 / 3 ∧ r 1 3 = 1 / 5 ∧
    regret V 1 1 loss (1 / 2) policy 0 4 = 3 / 2 ∧ ‖x 1 4 - 0‖ ^ 2 = 16 / 25 ∧
    BanditRL.OnlineGradientDescent.project V (-1 / 2) = 0 ∧ (-1 / 2 : ℝ) ≠ 0 := by
''',
'performance_canary': '''theorem performance_canary :
    regret V 1 1 loss (1 / 2) policy 0 4 ≤ 59 / 10 ∧
    regret V 1 1 loss (1 / 2) policy 0 4 ≤ 15 / 2 ∧
    regret V (Real.sqrt 2 / 2) 1 loss (1 / 2) policy 0 4 ≤ Real.sqrt 50 ∧
    Real.sqrt 50 = Real.sqrt 2 * sInf {b : ℝ | ∃ η : ℝ, 0 < η ∧
      b = BanditRL.OnlineOptimalStep.upperBound 1 25 η} := by
''',
'prefix_canary': '''theorem prefix_canary :
    state V 1 1 loss (1 / 2) policy 2 = state V 1 1 futureLoss (1 / 2) policy 2 ∧
    loss 2 ≠ futureLoss 2 ∧ loss 1 = futureLoss 1 := by
''',
'zero_energy_canary': '''theorem zero_energy_canary :
    (∀ t : ℕ, output V 1 1 zeroLoss (1 / 2) zeroPolicy t = 1 / 2) ∧
    (∀ T : ℕ, energy V 1 1 zeroLoss (1 / 2) zeroPolicy T = 0) ∧
    regret V 1 1 zeroLoss (1 / 2) zeroPolicy 0 4 = 0 ∧
    ‖output V 1 1 zeroLoss (1 / 2) zeroPolicy 4 - 0‖ ^ 2 = 1 / 4 ∧
    regret V 1 1 zeroLoss (1 / 2) zeroPolicy 0 4 ≤ 0 := by
''',
'zero_diameter_canary': '''theorem zero_diameter_canary :
    output W 1 0 loss 0 policy 2 = 0 ∧ energy W 1 0 loss 0 policy 2 = 9 ∧
    selected W 1 0 loss 0 policy 1 = 3 ∧ regret W 1 0 loss 0 policy 0 2 = 0 ∧
    regret W 1 0 loss 0 policy 0 2 ≤ 0 := by
'''}
write(CONTRACT/'algorithm-canary-context-draft-v1.lean.txt', context)
headers = {}
for name, text in texts.items():
    path = CONTRACT/('algorithm-canary-'+name+'-header-draft-v1.lean.txt')
    write(path, text)
    headers[name] = dict(path=path.as_posix(), raw_sha256=sha(path),
        normalized_statement_hash=statement_hash(text.rstrip()[:-len(':= by')].rstrip()))
write(CONTRACT/'algorithm-canary-fingerprints-draft-v1.json', dict(
    context_sha256=sha(CONTRACT/'algorithm-canary-context-draft-v1.lean.txt'), headers=headers,
    boundary='Draft TYPEs only. Seven full multi-component canaries; no production/Test BODY created.'))
probe = context
for name, text in texts.items():
    stmt = text.rstrip()[len('theorem '+name):-len(':= by')].strip()
    probe += '#check '+('('+stmt[1:].strip()+')' if stmt.startswith(':') else '(∀ '+stmt.replace(' :\n', ',\n', 1)+')')+'\n'
probe += '''#check BanditRL.OnlineGradientDescent.project_unitInterval
#check BanditRL.OnlineConvex.convexExtended_iff_toReal
#check BanditRL.OnlineAdaptiveOSD.energy_eq_sum
#check BanditRL.OnlineAdaptiveOSD.output_succ
#check BanditRL.OnlineAdaptiveOSD.state_prefix
#check BanditRL.OnlineAdaptiveOSD.regret_bound
#check BanditRL.OnlineAdaptiveOSD.source_eq4_4
#check BanditRL.OnlineAdaptiveBenchmark.source_theorem4_14_infimum
end AdaptiveProbe
'''
write(RUN/'AlgorithmCanaryTypeProbeV1.lean', probe)
code, out = capture('algorithm-canary-type-probe-v1', 'lake', 'env', 'lean', RUN/'AlgorithmCanaryTypeProbeV1.lean', required=False)
print(out, flush=True)
if code:
    sys.exit(code)
neutral0 = (CONTRACT/'specialization-neutral-packet-v2.lean.txt').read_text(encoding='utf8')
neutral = neutral0.split('\ntheorem certificate_1')[0]
neutral += '\nnoncomputable def B (A S η : ℝ) : ℝ := A / (2 * η) + η * S / 2\n'
canary_context = context.split('namespace AdaptiveProbe\n', 1)[1]
for before, after in {'state':'A', 'history':'H', 'energy':'Q', 'output':'X', 'selected':'G', 'eta':'R', 'regret':'F'}.items():
    canary_context = re.sub(r'\b'+before+r'\b', after, canary_context)
neutral += '\n'+canary_context
for i, (name, text) in enumerate(texts.items(), 1):
    text = text.replace('theorem '+name, 'theorem certificate_'+str(i), 1)
    text = text.replace('BanditRL.OnlineOptimalStep.upperBound', 'B')
    for before, after in {'state':'A', 'history':'H', 'energy':'Q', 'output':'X', 'selected':'G', 'eta':'R', 'regret':'F'}.items():
        text = re.sub(r'\b'+before+r'\b', after, text)
    neutral += '\n'+text.rstrip()[:-len(':= by')].rstrip()+'\n'
neutral += '\nend NeutralDynamics\n'+neutral0.split('end NeutralDynamics\n', 1)[1]
neutral += '''
/- Exact imported notation needed to decode the real fixture:
unitInterval has carrier Icc (0:ℝ) 1; project is the unique nearest-point projection.
SourceSubdifferential f z = {g | ∀ y, f z + (inner ℝ g (y-z) : EReal) ≤ f y}.
SourceProper f = (∀ z, f z ≠ ⊥) ∧ ∃ z c, f z = (c : EReal).
SubdifferentiableOn U f = SourceProper f ∧ ∀ z ∈ U.carrier, (SourceSubdifferential f z).Nonempty.
SupportPolicy inputs: current natural time, full strict-past loss functions,
full feasible/history points through current point, current whole loss function.
No source identity or previous verdict is included. The concrete policy ignores
those inputs other than time; no universal off-path oracle law is asserted.
-/
'''
write(CONTRACT/'algorithm-canary-neutral-packet-v1.lean.txt', neutral)
write(CONTRACT/'algorithm-canary-source-card-draft-v1.md', '''# Actual-run adaptive projection canaries

Pinned Orabona v10 2026-06-21 SHA cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17. These are derived synthetic real fixtures of the already frozen actual recurrence and necessary Chapter2 forward performance dependencies (Eq4.4/Theorem4.14), not additional printed source theorems or Chapter4 completion.

Unit interval, feasible x1=1/2, alpha=D=1, fixed time-only support policy [0,3,0,-4,...], affine extended-real losses g_t*x. Selected vectors arise from the very same policy/state. Actual energy through T4 is [0,0,9,9,25], points [1/2,1/2,0,0,4/5], inclusive eta [0,1/3,1/3,1/5]. First nonzero raw update=-1/2 is actively clipped to0. Leading zero and zero after positive energy exercise true skip, with no division cancellation at zero. Comparator0 gives regret3/2 and terminal squared distance16/25. Actual parent upper bound including negative terminal residual evaluates59/10; dropping it gives Eq4.4 bound15/2. The same fixed time-policy makes energy25 for every alpha, so at alpha=sqrt2/2 the separately instantiated source guarantee is sqrt50; no equality of two alpha trajectories is assumed. Benchmark holds that realized energy fixed and uses the reviewed infimum repair, not clairvoyant reruns.

The full state at2 is unchanged when whole losses at/after2 become constant7; changed current loss at2 is explicitly unequal and loss1 unchanged. Common policy/initial/domain/alpha/D are fixed, not reselected using the future. Zero-loss fixture on a nontrivial interval has zero energy but terminal distance1/4 and bound0; this checks energy weighting, not an assumption that terminal distance vanishes. Singleton D0 fixture has selected gradient3 and energy9 atT2 while outputs/regret/parent bound remain0: zero diameter does not imply zero supports. No arbitrary off-path OracleLaw or horizon-universal chosen-policy optimality is claimed.

Seven exact full headers: regularity/support (3 blocks), actual selected/energy (2), trace (13), performance (4), prefix (3), zero energy (5), zero diameter (5). All conjuncts must be publicly instantiated and audited, not projected to a convenient subset. The four performance proof branches must actually reference intended public parent/source_eq4_4/source_theorem4_14_infimum declarations in compiled VALUE, rather than merely prove numeral inequalities. Zero boundary bound branches must likewise use regret_bound. Existing shared real projection/domain/convex/support APIs only. New Tests/OnlineAdaptiveOSDCanary.lean proposed; no existing source/root/Test-root/registry/reader edit in this proof window.
''')
write(CONTRACT/'algorithm-canary-conversion-window-draft-v1.md', '''Single lower route, seven frozen headers and exact context only in a new Test module. First loss_regular proves global affine source supports/properness and convex real epigraph, with no supplied assumptions. feedback_energy uses actual energy_eq_sum and fixed policy. trace_canary uses actual output_succ/eta_eq_energy and shared project_unitInterval, all13 components. performance_canary calls actual regret_bound, source_eq4_4 and complete source_theorem4_14_infimum on the same fixed run/appropriate alpha; preserves all4 blocks and checks compiled branch VALUE. prefix_canary applies actual state_prefix and witnesses changed whole loss. zero_energy_canary uses actual recurrence at zero support and parent regret_bound; zero_diameter_canary uses actual singleton update/energy and parent bound. Proposed individual ordered sequence in that order; focused actual success before appending downstream. CONTRACT/neutral/source review must approve before production BODY, exact headers/context no helper or extra import. Local BODY repair allowed after real failure; statement changes require version/review. Full combined package gates remain open.
''')
write(RUN/'director-algorithm-canary-draft-v1.md', 'Exercise the actual same-run trajectory and named performance parents, including active projection, leading/stalled zero energy, nonzero terminal residual and D0 with nonzero selected support. No new learner or theorem count inflation.')
write(RUN/'architect-algorithm-canary-draft-v1.md', 'Seven exact complete headers/context TYPE-checked; finite new-Test window proposed after distinct decoder and source CONTRACT review. Existing public graph remains unchanged. Benchmark BODY favorable prerequisite for repaired performance consumer.')
print('neutral_packet', sha(CONTRACT/'algorithm-canary-neutral-packet-v1.lean.txt'), flush=True)
