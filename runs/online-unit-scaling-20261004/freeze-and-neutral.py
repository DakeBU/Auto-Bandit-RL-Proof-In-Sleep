"""Native draft fences and a source-neutral, unproved semantic packet model."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
sys.path.insert(0,str(Path('.').resolve()))
from tools.abrl_lifecycle import lean_declaration_header
run=Path(__file__).parent
contract=Path('docs/contracts/online-unit-scaling-v1');contract.mkdir(exist_ok=False)
context=(run/'leaves/context-v1.lean.txt').read_text(encoding='utf-8')
headers=json.loads((run/'draft-headers-v1.json').read_text(encoding='utf-8'))
assert json.loads((run/'draft-types-01-exit.json').read_text(encoding='utf-8'))['exit_code']==0
(contract/'context.lean.txt').write_bytes((run/'leaves/context-v1.lean.txt').read_bytes())
def save(p,o):
    with Path(p).open('w',encoding='utf-8',newline='\n') as f:
        json.dump(o,f,ensure_ascii=False,indent=2);f.write('\n')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def assumptions(header):
    out=[]
    for m in re.finditer(r'\(h\w*\s*:',header):
        depth=0
        for j in range(m.start(),len(header)):
            if header[j]=='(':depth+=1
            if header[j]==')':
                depth-=1
                if depth==0:out.append(header[m.start():j+1]);break
    return out
freeze={}
for name,h in headers.items():
    native=lean_declaration_header(run/'leaves/target-v1.lean.txt',name)
    freeze[name]=hashlib.sha256(native.encode('utf-8')).hexdigest()
    (contract/(name+'-header.txt')).write_text(native+'\n',encoding='utf-8')
    cmd=[sys.executable,'tools/bandit.py','statement-fence','--declaration','BanditRL.OnlineUnitScaling.'+name,
         '--file',(run/'leaves/target-v1.lean.txt').as_posix(),'--output',(contract/(name+'.json')).as_posix()]
    for a in assumptions(native):cmd+=['--source-assumption',a]
    subprocess.run([sys.executable,str(run/'run-command.py'),'fence-'+name]+cmd,check=True)
save(run/'draft-freeze.json',dict(stage='draft',context_sha256=sha(contract/'context.lean.txt'),headers=freeze,
    source_pdf_sha256='cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17',
    source_intent_sha256=sha(run/'source-card.md'),body_proof_started=False,context_types_compiled=True,
    type_probe='draft-types-01',target_file_boundary='Empty := by markers exist only in uncompiled .txt for native header extraction; no accepted proof bodies.'))
neutral='''import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Tactic

noncomputable section
open Set Finset
open scoped InnerProductSpace
namespace NeutralUnits
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
structure C (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  carrier : Set E
  nonempty : carrier.Nonempty
  closed : IsClosed carrier
  convex : Convex ℝ carrier
def K : C E := ⟨univ, univ_nonempty, isClosed_univ, convex_univ⟩
def J (z : E) : E := Classical.choose
  (exists_norm_eq_iInf_of_complete_convex K.nonempty K.closed.isComplete K.convex z)
def Q (f : E → EReal) : Prop := (∀ x, f x ≠ ⊥) ∧ ∃ x, ∃ r : ℝ, f x = (r : EReal)
def S (f : E → EReal) (x : E) : Set E :=
  {g | ∀ y, f x + (inner ℝ g (y - x) : EReal) ≤ f y}
def B (f : E → EReal) : Prop := Q f ∧ ∀ x ∈ K.carrier, (S f x).Nonempty
abbrev P := (t : ℕ) → (Fin t → E → EReal) → (Fin (t + 1) → E) → (E → EReal) → E
def H (k : C E) (η : ℕ → ℝ) (loss : ℕ → E → EReal) (x₁ : E) (p : P (E := E)) :
    (t : ℕ) → Fin (t + 1) → E :=
  Nat.rec (motive := fun t => Fin (t + 1) → E) (fun _ => x₁)
    (fun t h => Fin.snoc h (J (h (Fin.last t) - η t • p t (fun i => loss i.val) h (loss t))))
def Z (k : C E) (η : ℕ → ℝ) (loss : ℕ → E → EReal) (x₁ : E) (p : P (E := E)) (t : ℕ) : E :=
  H k η loss x₁ p t (Fin.last t)
def G (k : C E) (η : ℕ → ℝ) (loss : ℕ → E → EReal) (x₁ : E) (p : P (E := E)) (t : ℕ) : E :=
  p t (fun i => loss i.val) (H k η loss x₁ p t) (loss t)
def L (k : C E) (η : ℕ → ℝ) (loss : ℕ → E → EReal) (x₁ : E) (p : P (E := E)) (T : ℕ) : Prop :=
  ∀ t < T, G k η loss x₁ p t ∈ S (loss t) (Z k η loss x₁ p t)
def R (k : C E) (η : ℕ → ℝ) (loss : ℕ → E → EReal) (x₁ : E) (p : P (E := E)) (u : E) (T : ℕ) : ℝ :=
  ∑ t ∈ range T, ((loss t (Z k η loss x₁ p t)).toReal - (loss t u).toReal)
def F (c : ℝ) (f : E → EReal) : E → EReal := fun y => f (c • y)
def e (c : ℝ) (η : ℕ → ℝ) : ℕ → ℝ := fun t => η t / c ^ 2
def a (c : ℝ) (p : P (E := E)) : P (E := E) :=
  fun t past h f => c • p t (fun i => F c⁻¹ (past i)) (fun i => c • h i) (F c⁻¹ f)
def U (A B η : ℝ) : ℝ := A / (2 * η) + η * B / 2

'''
mapping={'BanditRL.OnlineSubgradientDescent.SubdifferentiableOn V':'B',
    'BanditRL.OnlineOptimalStep.upperBound':'U','SourceProper':'Q','SourceSubdifferential':'S',
    'SupportPolicy':'P','LegalFeedback':'L','history':'H','output':'Z','selected':'G','regret':'R',
    'scaledLoss':'F','scaledEta':'e','scaledPolicy':'a','V':'K'}
neutral_headers={}
for i,(name,h) in enumerate(headers.items(),1):
    n='N'+str(i).zfill(2)
    h=re.sub(r'^theorem '+re.escape(name)+r'\b','theorem '+n,h)
    for old,new in mapping.items():h=re.sub(r'(?<!\w)'+re.escape(old)+r'(?!\w)',new,h)
    assert 'BanditRL' not in h
    neutral_headers[n]=h
types=neutral+'\n'.join('#check (∀ '+h.split(' ',2)[2].replace(' :\n',',\n',1)+')' for h in neutral_headers.values())+'\nend NeutralUnits\n'
(run/'leaves/neutral-types-v1.lean').write_text(types,encoding='utf-8')
save(run/'neutral-headers-v1.json',neutral_headers)
save(run/'private-neutral-name-map.json',dict(zip(neutral_headers,headers)))
save(run/'neutral-context-correspondence.json',dict(scope='unproved private mathematical context only, no second public library',
    full_space_projection='J is literal same full-space nearest choice; H uses this fixed full-space J. Its dummy k is not a general-domain implementation; all22 targets instantiate K only.',
    original_context_sha256=sha(contract/'context.lean.txt'),neutral_defs=len(re.findall(r'^(?:def|abbrev|structure) ',neutral,re.M)),
    feedback='Exact shared finite-past losses/outputs/current whole loss recursion and support/proper predicates translated; no causal or performance statement assumed.'))
(run/'blind-packet-v1.md').write_text('Read only the mathematical Lean block below. Reconstruct each unproved N01–N22 in seven slots: objects/spaces, quantifier order, assumptions, conclusion/metric, constants, information/probability, boundaries. No theorem bodies or proof acceptance are supplied. K is the fixed whole-space domain; J is its nearest-point choice. The parameter k in H/Z/G/L/R is a uniform interface placeholder and every target passes K. Other-domain behavior is outside this packet. P is an exogenous deterministic finite-history support policy, receiving past whole losses, played outputs including current output, then the current whole loss. Dimension variables D use additive exponent notation for multiplication/division of abstract units. Pure EReal toReal identities are algebraic; finite-loss semantics require the proper/legality conditions given in their corresponding targets. Do not consult source, provenance, project aliases, prior verdicts or other files.\n\n```lean\n'+neutral+'\n\n'.join(neutral_headers.values())+'\nend NeutralUnits\n```\n',encoding='utf-8')
print('Native22 fences/frozen headers; source-neutral unproved model and packet authored.')
