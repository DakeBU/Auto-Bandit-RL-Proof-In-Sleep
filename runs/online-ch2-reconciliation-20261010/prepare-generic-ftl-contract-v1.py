from common import *

fixed()
leaf = CONTRACT / 'generic-ftl-v1'
definitions = '''import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Extr

noncomputable section
open Set Finset
namespace BanditRL.OnlineFTLSelector
variable {X : Type*} {n : ℕ}

def cumulative (past : Fin n → X → ℝ) (x : X) : ℝ :=
  ∑ i, past i x

def minimizers (V : Set X) (past : Fin n → X → ℝ) : Set X :=
  {x | x ∈ V ∧ IsMinOn (cumulative past) V x}

def select (V : Set X) (past : Fin n → X → ℝ) : Option X := by
  classical
  exact if h : (minimizers V past).Nonempty then some (Classical.choose h) else none

def predict (V : Set X) (initial : V) (loss : ℕ → X → ℝ) (t : ℕ) : Option X :=
  if t = 0 then some (initial : X) else select V (fun i : Fin t => loss i.val)
'''
targets = [
    ('cumulative_prefix', '(loss : ℕ → X → ℝ) (t : ℕ) (x : X)', 'cumulative (fun i : Fin t => loss i.val) x = ∑ i ∈ range t, loss i x'),
    ('select_some_spec', '(V : Set X) (past : Fin n → X → ℝ) (p : X) (h : select V past = some p)', 'p ∈ V ∧ IsMinOn (cumulative past) V p'),
    ('select_none_iff', '(V : Set X) (past : Fin n → X → ℝ)', 'select V past = none ↔ ¬ ∃ p, p ∈ V ∧ IsMinOn (cumulative past) V p'),
    ('select_congr', '(V : Set X) (past past\' : Fin n → X → ℝ) (h : ∀ i, EqOn (past i) (past\' i) V)', 'select V past = select V past\''),
    ('select_eq_some_of_unique', '(V : Set X) (past : Fin n → X → ℝ) (p : X) (hp : p ∈ V) (hmin : IsMinOn (cumulative past) V p) (hunique : ∀ q ∈ V, IsMinOn (cumulative past) V q → q = p)', 'select V past = some p'),
    ('predict_zero', '(V : Set X) (initial : V) (loss : ℕ → X → ℝ)', 'predict V initial loss 0 = some (initial : X)'),
    ('predict_some_spec', '(V : Set X) (initial : V) (loss : ℕ → X → ℝ) (t : ℕ) (p : X) (h : predict V initial loss t = some p)', 'p ∈ V ∧ IsMinOn (fun x => ∑ i ∈ range t, loss i x) V p'),
    ('predict_none_iff', '(V : Set X) (initial : V) (loss : ℕ → X → ℝ) (t : ℕ)', 'predict V initial loss t = none ↔ ¬ ∃ p, p ∈ V ∧ IsMinOn (fun x => ∑ i ∈ range t, loss i x) V p'),
    ('predict_prefix', '(V : Set X) (initial : V) (loss loss\' : ℕ → X → ℝ) (t : ℕ) (h : ∀ s < t, EqOn (loss s) (loss\' s) V)', 'predict V initial loss t = predict V initial loss\' t'),
]
write(leaf / 'definition-context-v1.lean.txt', definitions + '\nend BanditRL.OnlineFTLSelector\n')
headers = []
probe = definitions + '\n'
neutral = definitions.replace('BanditRL.OnlineFTLSelector', 'Candidate')
renames = [('cumulative', 'C'), ('minimizers', 'M'), ('select', 'S'), ('predict', 'P')]
import re
for a, b in renames:
    neutral = re.sub(r'\b' + a + r'\b', b, neutral)
neutral += '\n'
for i, (name, binders, conclusion) in enumerate(targets, 1):
    header = 'theorem ' + name + ' ' + binders + ' :\n    ' + conclusion
    proposition = '∀ ' + binders + ', ' + conclusion
    headers.append(dict(declaration='BanditRL.OnlineFTLSelector.' + name, exact_header=header,
        normalized_header_sha256=hashlib.sha256(' '.join(header.split()).encode('utf8')).hexdigest(),
        exact_Prop=proposition, BODY='unwritten', current_terminal_closed=False))
    probe += '#eval IO.println "TYPE-PROBE-' + str(i) + '"\n#check (' + proposition + ')\n\n'
    neutral_prop = proposition
    for a, b in renames:
        neutral_prop = re.sub(r'\b' + a + r'\b', b, neutral_prop)
    neutral += '-- Terminal ' + str(i) + '\n#check (' + neutral_prop + ')\n\n'
probe += '#check Fin.sum_univ_eq_sum_range\n#check isMinOn_iff\n#check Classical.choose_spec\nend BanditRL.OnlineFTLSelector\n'
neutral += 'end Candidate\n'
write(leaf / 'frozen-headers-draft-v1.json', dict(rows=headers,
    authority='Draft exact source text and complete definition context; actual Prop type probe follows, not named theorem BODY compilation.',
    source_contract_review='pending', production_module='BanditRLProof/OnlineFTLSelector.lean', Tests_module='Tests/OnlineFTLSelectorCanary.lean'))
write(RUN / 'GenericFTLTypeProbeV1.lean', probe)
write(RUN / 'NeutralFiniteSelectorPacketV1.lean', neutral)
capture('generic-ftl-type-probe-v1', 'lake', 'env', 'lean', RUN / 'GenericFTLTypeProbeV1.lean')
receipt = load(RUN / 'generic-ftl-type-probe-v1.json')
stdout = base64.b64decode(receipt['stdout_base64'])
assert hashlib.sha256(stdout).hexdigest() == receipt['stdout_sha256']
for i in range(1, 10):
    assert ('TYPE-PROBE-' + str(i)).encode('utf8') in stdout
for name in ['Fin.sum_univ_eq_sum_range', 'isMinOn_iff', 'Classical.choose_spec']:
    assert name.encode('utf8') in stdout
write(leaf / 'source-card-v1.md', '''# Generic strict-past FTL source foundation

Orabona, Online Learning: A Modern Introduction Using Convex Optimization, arXiv:1912.13213v10, 2026-06-21; PDF SHA cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17. Chapter2 printed11-12/PDF23-24: choose an argmin over V of losses from rounds1 through t-1; first-round action may be any feasible point. This is one algorithm-definition source family, not nine printed theorems or a performance guarantee.

The ambient X generalizes finite-dimensional Euclidean space. Real-valued losses on V are represented by ambient extensions. Only their restrictions to V determine selection; the exact restricted-prefix theorem makes this representation boundary explicit. No convexity, compactness, closedness, differentiability or probability assumption is added for the conditional mathematical selector.

The first output is the supplied subtype witness initial. Later outputs classically choose a feasible minimizer of the finite strict-past tuple exactly when one exists; otherwise none. The same fixed initial action and selection convention are used in prefix comparison. This is a partial rule, not an unconditional complete valid online run, no recovery/no-recovery assertion and no regret result. Ties allow an arbitrary fixed classical choice; only uniqueness licenses identifying a specific result. No executable, measurable or efficient algorithm is claimed.

Lean time0 is source round1; prediction at t minimizes exactly indices i<t. The displayed source sum is connected to the Fin t sum by the explicit cumulative_prefix endpoint. Source definition and mathematical partial-choice completion are distinguished; the book does not prescribe an Option failure representation.
''')
write(leaf / 'DAG-draft-v1.json', dict(nodes=[
    dict(id='definitions', dependencies=['Finset finite sum', 'Set', 'IsMinOn', 'Classical.choose'], ready=True),
    dict(id='cumulative_prefix', dependencies=['definitions', 'Fin.sum_univ_eq_sum_range'], ready=True),
    dict(id='select_some_spec', dependencies=['definitions', 'Classical.choose_spec'], ready=True),
    dict(id='select_none_iff', dependencies=['definitions', 'Option constructors'], ready=True),
    dict(id='select_congr', dependencies=['definitions', 'finite sum congruence', 'set extensionality'], ready=True),
    dict(id='select_eq_some_of_unique', dependencies=['select_some_spec', 'select_none_iff'], ready=False),
    dict(id='predict_zero', dependencies=['definitions'], ready=True),
    dict(id='predict_some_spec', dependencies=['select_some_spec', 'cumulative_prefix', 'predict_zero'], ready=False),
    dict(id='predict_none_iff', dependencies=['select_none_iff', 'cumulative_prefix', 'predict_zero'], ready=False),
    dict(id='predict_prefix', dependencies=['select_congr'], ready=False)],
    first_proof_leaf='select_some_spec', allowed_edits_after_stabilization=['NEW BanditRLProof/OnlineFTLSelector.lean theorem BODY/private helpers only; four definitions and nine public types frozen', 'NEW OWN leaf evidence'],
    root_Tests_reader_registry_changes='later distinct scoped integration review', chapter_complete=False))
write(RUN / 'generic-ftl-contract-attempt-v1.json', dict(
    source_inventory_repair='R1 of source-model-review-v1', proposed_outcome='reusable-interface',
    source_family='Generic arbitrary-loss strict-past FTL definition; conditional existence',
    proof_terminals=9, mathematical_source_result_count='one definition family; not nine source results',
    searched_existing=['Actual OnlineFTLFailure linear minimizer/prefix', 'OnlineLearningFTLState mean recursion', 'OnlineLearningFoundations.lemma_1_2 supplied hindsight leaders', 'OnlinePrescientBregman.advance partial proximal selector', 'Mathlib IsMinOn/isMinOn_iff', 'Mathlib Function.argmin requires well-founded codomain; real loss does not meet that hypothesis'],
    reuse_decision='new_route_local generic finite-history interface, using shared Mathlib definitions; no copied projection/Bregman/regret theory',
    public_test_plan=['actual quadratic prediction initial3/4 ->1/4 ->1/2', 'current/future losses may differ with the same past restricted loss', 'tie contains distinct feasible zero/one minimizers without specifying chosen tie', 'unbounded affine loss on nonempty closed convex full space has no attained minimum', 'empty-domain finite-history selector returns none'],
    graph_delta=dict(Lean='new module/declarations only after genuine proof compilation; planned dependency DAG remains overlay', Overview='one currently missing Chapter2 definition foundation, Chapter2 remains partial', Functor='none-found-with-reason: routine conditional-minimum foundation; no new transport or certified functor'),
    reader_delta='later adjacent source formula, finite-history argument, initialization, conditional attainment and folded exact code; no badge or chapter acceptance now',
    neutral_decoder='pending /root/osd_blind; packet contains definitions/terminal Props only, no source identity/verdict',
    source_reviewer='pending distinct /root/source_reviewer', source_fingerprint=sha(PDF),
    actual_type_probe='generic-ftl-type-probe-v1.json', theorem_bodies_compiled=False, chapter_complete=False, whole_Goal='ACTIVE'))
event('native-generic-ftl-draft-v1', 'draft', dict(
    scope='Source-model R1 generic strict-past FTL foundation', contract='generic-ftl-v1/frozen-headers-draft-v1.json',
    first_leaf='select_some_spec', actual_Prop_type_probe=True, actual_named_theorem_BODY=False,
    terminal_review='pending', chapter_complete=False))
fixed()
print('Nine actual proposition types and four definition bodies elaborated; neutral/source contract review pending, no theorem bodies written.', flush=True)
