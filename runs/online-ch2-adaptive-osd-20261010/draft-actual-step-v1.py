from common import *
sys.path.insert(0, str(ROOT))
from tools.abrl_lifecycle import statement_hash
import re
args = '''(V : Domain (E := E)) (α D : ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E))'''
signed = '''(V : Domain (E := E)) (α D : ℝ) (hα : 0 < α) (hD : 0 < D)
    (loss : ℕ → E → EReal) (x₁ : E) (p : SupportPolicy (E := E))'''
legal = ''' (t : ℕ)
    (hloss : BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t))
    (hg : selected V α D loss x₁ p t ∈ SourceSubdifferential (loss t) (output V α D loss x₁ p t))'''
headers = {
'energy_step_mono':args+''' (t : ℕ) :
    energy V α D loss x₁ p t ≤ energy V α D loss x₁ p (t + 1)''',
'energy_pos_of_selected_ne_zero':args+''' (t : ℕ)
    (hg : selected V α D loss x₁ p t ≠ 0) :
    0 < energy V α D loss x₁ p (t + 1)''',
'eta_pos_of_selected_ne_zero':signed+''' (t : ℕ)
    (hg : selected V α D loss x₁ p t ≠ 0) :
    0 < eta V α D loss x₁ p t''',
'zero_feedback_step':args+legal+'''
    (hz : selected V α D loss x₁ p t = 0) (u : E) (hu : u ∈ V.carrier) :
    output V α D loss x₁ p (t + 1) = output V α D loss x₁ p t ∧
    (loss t (output V α D loss x₁ p t)).toReal - (loss t u).toReal ≤ 0''',
'one_step_chain':signed+legal+'''
    (hnz : selected V α D loss x₁ p t ≠ 0) (u : E) (hu : u ∈ V.carrier) :
    eta V α D loss x₁ p t * ((loss t (output V α D loss x₁ p t)).toReal - (loss t u).toReal) ≤
      eta V α D loss x₁ p t * inner ℝ (selected V α D loss x₁ p t) (output V α D loss x₁ p t - u) ∧
    eta V α D loss x₁ p t * inner ℝ (selected V α D loss x₁ p t) (output V α D loss x₁ p t - u) ≤
      ‖output V α D loss x₁ p t - u‖ ^ 2 / 2 -
      ‖output V α D loss x₁ p (t + 1) - u‖ ^ 2 / 2 +
      (eta V α D loss x₁ p t) ^ 2 / 2 * ‖selected V α D loss x₁ p t‖ ^ 2''',
'one_step':signed+legal+''' (u : E) (hu : u ∈ V.carrier) :
    (loss t (output V α D loss x₁ p t)).toReal - (loss t u).toReal ≤
      (‖output V α D loss x₁ p t - u‖ ^ 2 - ‖output V α D loss x₁ p (t + 1) - u‖ ^ 2) *
        Real.sqrt (energy V α D loss x₁ p (t + 1)) / (2 * α * D) +
      α * D / 2 * (‖selected V α D loss x₁ p t‖ ^ 2 / Real.sqrt (energy V α D loss x₁ p (t + 1)))''',
'regret_zero_diameter':'''(V : Domain (E := E)) (α : ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (hx₁ : x₁ ∈ V.carrier) (T : ℕ)
    (hdiam : ∀ x ∈ V.carrier, ∀ y ∈ V.carrier, ‖x - y‖ ≤ (0 : ℝ))
    (u : E) (hu : u ∈ V.carrier) :
    regret V α 0 loss x₁ p u T = 0 ∧ ‖output V α 0 loss x₁ p T - u‖ = 0'''}
context = (CONTRACT/'algorithm-definition-context-draft-v2.lean.txt').read_text(encoding='utf8')
probe = '''import BanditRLProof.OnlineAdaptiveOSD
noncomputable section
open Set Finset BanditRL.OnlineConvex
open scoped InnerProductSpace
namespace BanditRL.OnlineAdaptiveOSD
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
local instance : DecidableEq E := Classical.decEq E
'''
neutral = context+'\n'
fingerprints = {}
for i, (name, statement) in enumerate(headers.items(), 1):
    header = 'theorem '+name+' '+statement+' := by\n'
    path = CONTRACT/('actual-step-'+name+'-header-draft-v1.lean.txt')
    write(path, header)
    fingerprints[name] = dict(path=path.as_posix(), raw_sha256=sha(path),
        normalized_statement_hash=statement_hash(header.rstrip()[:-len(':= by')]))
    probe += '#check (∀ '+statement.replace(' :\n', ',\n', 1)+')\n\n'
    neutral += 'theorem certificate_%d ' % i+statement+'\n\n'
probe += 'end BanditRL.OnlineAdaptiveOSD\n'
neutral += 'end BanditRL.OnlineAdaptiveOSD\n'
for old, new in load(CONTRACT/'algorithm-neutral-renaming-v1.json')['renamings']:
    neutral = re.sub(r'(?<![\w.])'+re.escape(old)+r'(?!\w)', new, neutral)
write(CONTRACT/'actual-step-neutral-packet-v1.lean.txt', neutral)
write(CONTRACT/'actual-step-fingerprints-draft-v1.json', dict(headers=fingerprints,
    context_sha256=sha(CONTRACT/'algorithm-definition-context-draft-v2.lean.txt'),
    state='draft exact Prop headers only; no BODY authorized',
    parent_regret_header_sha256=sha(CONTRACT/'algorithm-regret_bound-header-draft-v1.lean.txt')))
write(CONTRACT/'actual-step-source-card-draft-v1.md', '''# Actual same-run one-step contract

Orabona v10 SHA cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17, printed39–40/PDF51–52, Eq4.4/Theorem4.14 inclusive observed energy and explicit g=0 skip, with projected support-step mechanism from Lemma2.31. These seven finite leaves supply the exact unproved parent regret_bound, not seven new source theorems. Same eight actual Nat.rec definitions, fixed V/alpha/D/x1/p information boundary, no exogenous eta or desired-regret/stability premise. Every current support refers to the actual generated history.

Three energy/eta facts: energy is nondecreasing without sign or legality assumptions; a nonzero selected vector makes inclusive energy positive even when preceding energy is zero; positive alpha,D then make eta positive. Zero-feedback conjunction holds for arbitrary real alpha,D: actual output skips and legal zero global support gives nonpositive current real regret gap. Positive-alpha/positive-D nonzero chain preserves BOTH support linearization and actual projection-distance inequalities. Its all-feedback one_step consumer uses inverse-energy weight sqrt(Snext)/(2alphaD) and alphaD/2 times squared-norm/sqrt(Snext), covering a zero vector after positive or zero energy. No feasibility of x1 is imposed on these local inequalities: lawful global support makes the current point's loss finite, while comparator feasibility and current SubdifferentiableOn supply comparator finiteness. This deliberate source-support sufficient generalization remains explicit, not a source convexity-equivalence assertion.

Zero diameter is a separate algebraic/geometric adapter: feasible actual outputs and feasible comparator must coincide, so regret and terminal norm vanish for arbitrary losses/policy/alpha, without falsely inferring legality from diameter. T0 is included. The parent still has D>=0 and arbitrary T; local positive-D division does not delete D0 or the all-zero-energy case. All division remains total, and no loss constancy is inferred from zero chosen support. Canonical source-convex performance and the separate min/infimum source repair remain future obligations.

Actual APIs searched: shared lemma_2_31 and project_spec, existing OnlineLinearization.support_gap, prior OnlineSubgradientPolicy.one_step_chain/one_step, and existing same-run bootstrap declarations. Reuse lemma_2_31 directly for the two-chain and its eta=1 support component in the zero case. Importing a second linear-policy interface solely for its two-line support wrapper is unnecessary; no new general-purpose support lemma is proposed. Default one lower route. No production BODY yet; complete neutral decode, source contract review and a bounded sequential window must precede tactics.
''')
write(RUN/'ActualStepTypeProbeV1.lean', probe)
code, out = capture('actual-step-type-probe-v1', 'lake', 'env', 'lean', RUN/'ActualStepTypeProbeV1.lean', required=False)
print(out, flush=True)
sys.exit(code)
