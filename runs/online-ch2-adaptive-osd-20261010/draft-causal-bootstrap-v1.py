from common import *
sys.path.insert(0, str(ROOT))
from tools.abrl_lifecycle import statement_hash
import re
args = '''(V : Domain (E := E)) (α D : ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E))'''
headers = {
'energy_succ': args+''' (t : ℕ) :
    energy V α D loss x₁ p (t + 1) =
      energy V α D loss x₁ p t + ‖selected V α D loss x₁ p t‖ ^ 2''',
'output_succ': args+''' (t : ℕ) :
    output V α D loss x₁ p (t + 1) =
      if selected V α D loss x₁ p t = 0 then output V α D loss x₁ p t else
        BanditRL.OnlineGradientDescent.project V
          (output V α D loss x₁ p t - eta V α D loss x₁ p t • selected V α D loss x₁ p t)''',
'energy_eq_sum': args+''' (T : ℕ) :
    energy V α D loss x₁ p T = ∑ t ∈ range T, ‖selected V α D loss x₁ p t‖ ^ 2''',
'history_mem': args+''' (hx₁ : x₁ ∈ V.carrier) (t : ℕ) (i : Fin (t + 1)) :
    history V α D loss x₁ p t i ∈ V.carrier''',
'output_mem': args+''' (hx₁ : x₁ ∈ V.carrier) (t : ℕ) :
    output V α D loss x₁ p t ∈ V.carrier''',
'energy_nonneg': args+''' (T : ℕ) :
    0 ≤ energy V α D loss x₁ p T''',
'eta_eq_energy': args+''' (t : ℕ) :
    eta V α D loss x₁ p t = α * D / Real.sqrt (energy V α D loss x₁ p (t + 1))''',
'trajectory_finite_loss': args+''' (hx₁ : x₁ ∈ V.carrier) (t : ℕ)
    (hloss : BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t))
    (u : E) (hu : u ∈ V.carrier) :
    loss t (output V α D loss x₁ p t) = ((loss t (output V α D loss x₁ p t)).toReal : EReal) ∧
    loss t u = ((loss t u).toReal : EReal)''',
'oracle_feedback': args+''' (hx₁ : x₁ ∈ V.carrier) (T : ℕ)
    (hp : BanditRL.OnlineSubgradientPolicy.OracleLaw V p)
    (hloss : ∀ t < T, BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t)) :
    LegalFeedback V α D loss x₁ p T''',
'canonical_feedback': '''(V : Domain (E := E)) (α D : ℝ) (loss : ℕ → E → EReal)
    (x₁ : E) (hx₁ : x₁ ∈ V.carrier) (T : ℕ)
    (hloss : ∀ t < T, BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V (loss t)) :
    LegalFeedback V α D loss x₁ BanditRL.OnlineSubgradientPolicy.canonicalPolicy T'''}
context = (CONTRACT/'algorithm-definition-context-draft-v2.lean.txt').read_text(encoding='utf8')
probe = context+'\n'
neutral = context+'\n'
fingerprints = {}
for i, (name, statement) in enumerate(headers.items(), 1):
    header = 'theorem '+name+' '+statement+' := by\n'
    path = CONTRACT/('bootstrap-'+name+'-header-draft-v1.lean.txt')
    write(path, header)
    fingerprints[name] = dict(path=path.as_posix(), raw_sha256=sha(path),
        normalized_statement_hash=statement_hash(header.rstrip()[:-len(':= by')]))
    probe += '#check (∀ '+statement.replace(' :\n', ',\n', 1)+')\n\n'
    neutral += 'theorem certificate_%d ' % i + statement+'\n\n'
probe += 'end BanditRL.OnlineAdaptiveOSD\n'
neutral += 'end BanditRL.OnlineAdaptiveOSD\n'
for old, new in load(CONTRACT/'algorithm-neutral-renaming-v1.json')['renamings']:
    neutral = re.sub(r'(?<![\w.])'+re.escape(old)+r'(?!\w)', new, neutral)
write(CONTRACT/'bootstrap-neutral-packet-v1.lean.txt', neutral)
write(CONTRACT/'bootstrap-fingerprints-draft-v1.json', dict(
    context_sha256=sha(CONTRACT/'algorithm-definition-context-draft-v2.lean.txt'),
    headers=fingerprints, state='draft, BODY not authorized',
    semantic_family='Actual generated history/energy/feasibility/finite loss/lawful policy bootstrap; not ten source results'))
write(RUN/'BootstrapTypeProbeV1.lean', probe)
code, out = capture('bootstrap-type-probe-v1', 'lake', 'env', 'lean', RUN/'BootstrapTypeProbeV1.lean', required=False)
print(out)
sys.exit(code)
