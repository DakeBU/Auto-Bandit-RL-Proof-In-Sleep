from generic_ftl_proof import *
import re

fixed()
check_context()
CANARY = LEAF / 'canary-v1'
context = '''import BanditRLProof.OnlineFTLSelector
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

noncomputable section
open Set Finset BanditRL.OnlineFTLSelector
namespace Tests.OnlineFTLSelector

def interval : Set ℝ := Icc 0 1

def initial : interval := ⟨3 / 4, by norm_num [interval]⟩

def otherInitial : interval := ⟨1 / 4, by norm_num [interval]⟩

def quadraticLoss (t : ℕ) (x : ℝ) : ℝ :=
  if t = 0 then (x - 1 / 4) ^ 2 else (x - 3 / 4) ^ 2

def changedLoss (t : ℕ) (x : ℝ) : ℝ :=
  if t < 2 then quadraticLoss t x else x + 100

def offDomainLoss (t : ℕ) (x : ℝ) : ℝ :=
  if x ∈ interval then quadraticLoss t x else x + 7

def affineThenQuadratic (t : ℕ) (x : ℝ) : ℝ :=
  if t = 0 then x else x ^ 2 - x

end Tests.OnlineFTLSelector
'''
headers = [
'''theorem quadratic_trajectory :
    (initial : ℝ) = 3 / 4 ∧
    predict interval initial quadraticLoss 0 = some (3 / 4) ∧
    predict interval initial quadraticLoss 1 = some (1 / 4) ∧
    predict interval initial quadraticLoss 2 = some (1 / 2) ∧
    (1 / 4 : ℝ) ≠ 1 / 2 ∧
    quadraticLoss 0 (1 / 4) ≠ quadraticLoss 0 (3 / 4) ∧
    (∀ t ∈ range 3, ∃ p, predict interval initial quadraticLoss t = some p ∧
      p ∈ interval ∧ IsMinOn (fun x => ∑ i ∈ range t, quadraticLoss i x) interval p)''',
'''theorem current_future_independence :
    quadraticLoss 2 0 ≠ changedLoss 2 0 ∧
    quadraticLoss 3 0 ≠ changedLoss 3 0 ∧
    predict interval initial quadraticLoss 2 = predict interval initial changedLoss 2''',
'''theorem off_domain_invariance :
    (2 : ℝ) ∉ interval ∧
    quadraticLoss 0 2 ≠ offDomainLoss 0 2 ∧
    (∀ t, EqOn (quadraticLoss t) (offDomainLoss t) interval) ∧
    select interval (fun i : Fin 2 => quadraticLoss i.val) =
      select interval (fun i : Fin 2 => offDomainLoss i.val) ∧
    predict interval initial quadraticLoss 2 = predict interval initial offDomainLoss 2''',
'''theorem tied_minimizers :
    (0 : ℝ) ∈ interval ∧ (1 : ℝ) ∈ interval ∧ (0 : ℝ) ≠ 1 ∧
    IsMinOn (cumulative (fun _ : Fin 1 => fun _ : ℝ => 0)) interval 0 ∧
    IsMinOn (cumulative (fun _ : Fin 1 => fun _ : ℝ => 0)) interval 1 ∧
    (∃ p, select interval (fun _ : Fin 1 => fun _ : ℝ => 0) = some p ∧
      p ∈ interval ∧ IsMinOn (cumulative (fun _ : Fin 1 => fun _ : ℝ => 0)) interval p)''',
'''theorem empty_domain :
    select (∅ : Set ℝ) (fun _ : Fin 1 => fun x : ℝ => x ^ 2) = none''',
'''theorem empty_history_and_initialization :
    (∃ p, select interval (fun i : Fin 0 => Fin.elim0 i) = some p ∧ p ∈ interval) ∧
    predict interval initial quadraticLoss 0 = some (3 / 4) ∧
    predict interval otherInitial quadraticLoss 0 = some (1 / 4) ∧
    predict interval initial quadraticLoss 0 ≠ predict interval otherInitial quadraticLoss 0''',
'''theorem affine_nonattainment :
    (univ : Set ℝ).Nonempty ∧ IsClosed (univ : Set ℝ) ∧ Convex ℝ (univ : Set ℝ) ∧
    select univ (fun _ : Fin 1 => fun x : ℝ => x) = none ∧
    predict univ ⟨0, mem_univ 0⟩ (fun _ : ℕ => fun x : ℝ => x) 0 = some 0 ∧
    predict univ ⟨0, mem_univ 0⟩ (fun _ : ℕ => fun x : ℝ => x) 1 = none''',
'''theorem recovery_after_nonattainment :
    predict univ ⟨0, mem_univ 0⟩ affineThenQuadratic 1 = none ∧
    predict univ ⟨0, mem_univ 0⟩ affineThenQuadratic 2 = some 0 ∧
    IsMinOn (fun x => ∑ i ∈ range 2, affineThenQuadratic i x) univ 0 ∧
    (∀ x, (∑ i ∈ range 2, affineThenQuadratic i x) = x ^ 2)'''
]
items = []
for index, h in enumerate(headers, 1):
    name = h.split()[1]
    items.append(dict(declaration='Tests.OnlineFTLSelector.' + name, exact_header=h,
        normalized_header_sha256=hashlib.sha256(' '.join(h.split()).encode('utf8')).hexdigest(),
        exact_Prop=h.split(' :\n', 1)[1].strip(), neutral_id='Terminal' + str(index),
        BODY='unwritten', accepted=False))
write(CANARY / 'definition-context-v1.lean.txt', context)
write(CANARY / 'frozen-headers-draft-v1.json', dict(rows=items,
    production_context=rows([MODULE, LEAF / 'definition-context-v1.lean.txt']),
    actual_Test_module='Tests/OnlineFTLSelectorCanary.lean',
    scope='Eight constructed mathematical instantiations/boundary checks, not eight printed source results.'))
end = 'end Tests.OnlineFTLSelector\n'
probe = context[:-len(end)]
for index, item in enumerate(items, 1):
    probe += '#eval IO.println "CANARY-TYPE-PROBE-' + str(index) + '"\n'
    probe += '#check (' + item['exact_Prop'] + ' : Prop)\n\n'
probe += end
write(RUN / 'GenericFTLCanaryTypeProbeV1.lean', probe)

# Neutral packet contains complete definitions, no production names or theorem bodies.
production = (LEAF / 'definition-context-v1.lean.txt').read_text(encoding='utf8')
extra_imports = '\n'.join(context.splitlines()[1:4]) + '\n'
neutral = extra_imports + production + '\n' + '\n'.join(context.splitlines()[5:]) + '\n'
neutral = neutral[:-len(end)]
for item in items:
    neutral += '#check (' + item['exact_Prop'] + ' : Prop)\n\n'
neutral += end
neutral = neutral.replace('import BanditRLProof.OnlineFTLSelector\n', '')
neutral = neutral.replace('BanditRL.OnlineFTLSelector', 'FiniteSelectionPacket')
neutral = neutral.replace('Tests.OnlineFTLSelector', 'FiniteSelectionExamples')
mapping = dict(cumulative='C', minimizers='M', select='S', predict='P',
    interval='D', initial='a', otherInitial='b', quadraticLoss='q',
    changedLoss='qChanged', offDomainLoss='qExtended', affineThenQuadratic='r')
neutral = re.sub(r'\b(' + '|'.join(mapping) + r')\b', lambda m: mapping[m.group(0)], neutral)
assert 'OnlineFTL' not in neutral and 'Orabona' not in neutral
write(RUN / 'NeutralFiniteSelectorCanaryPacketV1.lean', neutral)
write(CANARY / 'contract-v1.md', '''# FTL selector canary CONTRACT v1

This is a separately frozen proposed Test package for the accepted generic definition contract. The eight exact headers, seven complete concrete definitions, production four-definition context and all nine frozen production types are explicit inputs. No Test BODY/root import/shared metadata edit is authorized before neutral reconstruction and distinct anti-anchored CONTRACT review. Type-probe elaboration is not theorem BODY compilation.

The constructed examples are mathematical tests, not new source theorem attributions. The interval quadratic run starts at 3/4, chooses 1/4 after its first loss, then 1/2 after the next loss centered at 3/4. Feasibility and actual cumulative minimality must be derived for each prefix. Current/future losses and off-domain extensions differ concretely while actual prefix predictions coincide. Ties expose two distinct feasible minimizers without forcing a particular selected one. Empty select domain is distinct from empty history; zero-time prediction returns its supplied initial.

The affine example explicitly uses the nonempty closed convex full real line with no minimum. The last example has first loss x and next loss x^2-x, so its failed first prefix recovers to the unique zero minimizer of x^2 at the second prefix. This is a direct per-prefix partial predictor, not an absorbing recursive run. There is no regret, measurability, efficiency or unconditional attainment claim.

Permitted after exact source review: NEW Tests/OnlineFTLSelectorCanary.lean with these fixed imports/context/definitions/headers, actual proofs and necessary named private helpers; create-only OWN evidence. Production public types/definitions remain frozen. Root, native acceptance, readers, registry, site, complete chapter and Goal acceptance are separate later gates.
''')
capture('generic-ftl-canary-type-probe-v1', 'lake', 'env', 'lean', RUN / 'GenericFTLCanaryTypeProbeV1.lean')
capture('neutral-finite-selector-canary-type-probe-v1', 'lake', 'env', 'lean', RUN / 'NeutralFiniteSelectorCanaryPacketV1.lean')
fixed()
print('Eight canary propositions and complete concrete context frozen; no Test BODY authored.', flush=True)
