"""Freeze retained supporting-gradient statements before distinct source review."""
from pathlib import Path
import json,hashlib,subprocess,sys,re
from pypdf import PdfReader
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header
run=Path(__file__).parent;contract=Path('docs/contracts/online-first-order-migration-v1');task='ONLINE-FIRST-ORDER-MIGRATION-20261005'
assert not contract.exists();contract.mkdir()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(p,x):
    p=Path(p);assert not p.exists(),p;p.parent.mkdir(parents=True,exist_ok=True)
    with p.open('w',encoding='utf-8',newline='\n') as f:
        if isinstance(x,str):f.write(x.rstrip('\n')+'\n')
        else:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
def replace_scaffold(p,x):
    p=Path(p);assert p.is_file()
    with p.open('w',encoding='utf-8',newline='\n') as f:f.write(x.rstrip('\n')+'\n')
def gate(label,*args):subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),label,*args],check=True)
source=Path('../research-online-ogd/tmp/pdfs/orabona-v10.pdf');assert sha(source)=='cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17'
pdf=PdfReader(source);write(run/'source-printed10-11-pdf22-23.txt','\n'.join(pdf.pages[i].extract_text() for i in [21,22]))
module=Path('BanditRLProof/OnlineConvexFirstOrder.lean');canary=Path('Tests/OnlineConvexFirstOrderCanary.lean')
names=['finitePart_eventually','convex_gradient_lower_bound','theorem_2_7'];text=module.read_text(encoding='utf-8')
assert re.findall(r'(?m)^theorem\s+(\S+)',text)==names
prefix=text[:text.index('theorem finitePart_eventually')]
write(contract/'context.lean.txt',prefix)
for p in [module,canary]:
    dst=run/('original-'+p.name+'.txt');dst.parent.mkdir(exist_ok=True);dst.write_bytes(p.read_bytes())
intent='''Orabona v10 (21June2026), Theorem2.7 printed11/PDF23. f:Rd→(-infinity,+infinity] convex, x in interior domf, differentiable at x; for EVERY y in Rd, f(x)+inner(gradient f(x),y-x)<=f(y). No global differentiability, closed/bounded domain, finite comparator, nonempty-domain or Lipschitz hypothesis is added. Source has noBottom globally; domain f<top and real-height epigraph are the accepted shared definitions. Complete real inner-product-space generality includes all source finite-dimensional Euclidean spaces; not a finite-dimensional restriction silently replaced by a different algorithm.

Actual gradient/differentiability use the canonical real function z→(f z).toReal. Its embedding equals f on a neighborhood of interior x, proved by finitePart_eventually under noBottom; no assertion that infinite loss globally equals zero. The source terminal retains every y, and separately proves the outside-domain case f(y)=top. Arithmetic at x is finite. The real ConvexOn helper only assumes derivative at x and x,y∈V; V need not be open, closed, bounded or nonempty beyond those points. It is an explicit generalized helper connected to the printed terminal, not a second printed theorem. The neighborhood lemma is a representation bridge. Three existing proofs/zero production definitions; zero new proof code or graph nodes at this migration. Historical same-model sequential review is retained but not relabeled distinct/external acceptance. Default one lower route reuses the actual bodies after distinct contract review, fresh elaboration/canary/axioms/guards, separate body review, root/Tests/full/shared registry/site/reader/PR gates.

Existing meaningful canary loss(x)=x if x>0, top otherwise: open domain(0,infinity), distinct finite values1/2, real derivative1/nonzero gradient at1, bound for every y and explicit outside y=-1/top. One canary definition/eight named proofs/one anonymous instance, preserved byte-exact; replay pending. All actual3 native headers/scoped assumptions must stay frozen. Only source qualification comment/selected online-first-order reader data may change after reviewed stabilization; mathematical statement change requires versioned source repair. Keep earlier accepted finite-loss/convex/FTL/OGD inputs immutable via explicit raw snapshots before shared surface edits. Whole Goal active; Chapter2 totalnull/incomplete/19legacy semantic migrations at start; no Chapter3 proof writing, merge/deploy/retirement/model upgrade.'''
write(contract/'source-intent.md',intent)
write(contract/'source-card.json',dict(source_path=source.as_posix(),source_sha256=sha(source),url='https://arxiv.org/pdf/1912.13213v10',printed_pages=[11],pdf_pages=[23],number='Theorem2.7',
    source_terminal='Every y supporting-gradient lower bound at interior differentiability point',actual_representation='Canonical local finite-part derivative with proved neighborhood identity',retained_proofs=3,new_proofs=0))
headers={}
for n in names:
    h=lean_declaration_header(module,n);digest=hashlib.sha256(h.encode()).hexdigest();headers[n]=digest
    write(contract/(n+'-header.txt'),h)
    assumptions=['(hbot : ∀ z, f z ≠ ⊥)','(hx : x ∈ interior (effectiveDomain f))'] if n=='finitePart_eventually' else (
        ['(hf : ConvexOn ℝ V f)','(hx : x ∈ V)','(hy : y ∈ V)','(hd : DifferentiableAt ℝ f x)'] if n=='convex_gradient_lower_bound' else
        ['(hbot : ∀ z, f z ≠ ⊥)','(hf : IsConvexExtended f)','(hx : x ∈ interior (effectiveDomain f))','(hd : DifferentiableAt ℝ (fun z => (f z).toReal) x)'])
    write(contract/(n+'.json'),dict(name='BanditRL.OnlineConvex.'+n,statement=h,statement_hash=digest,source_assumptions=assumptions,classification='retained-source-terminal' if n=='theorem_2_7' else 'retained-explicit-helper',context_hash=sha(contract/'context.lean.txt')))
    args=[sys.executable,'-X','utf8','tools/bandit.py','statement-fence','--declaration','BanditRL.OnlineConvex.'+n,'--file',module.as_posix(),'--output',str(run/('native-draft-fences/'+n+'.json'))]
    for a in assumptions:args+=['--source-assumption',a]
    gate('draft-fence-'+n+'-v1',*args)
    assert json.loads((run/('native-draft-fences/'+n+'.json')).read_text(encoding='utf-8'))['statement_hash']==digest
context='''import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Data.EReal.Basic
noncomputable section
open Set Filter
open scoped Topology
namespace Neutral
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
def Q0 (f : E → EReal) : Set E := {x | f x < ⊤}
def Q1 (f : E → EReal) : Set (E × ℝ) := {p | f p.1 ≤ (p.2 : EReal)}
def Q2 (f : E → EReal) : Prop := Convex ℝ (Q1 f)
'''
neutral=context+'\n'
for i,n in enumerate(names,1):
    h=lean_declaration_header(module,n).replace('theorem '+n,'theorem M'+str(i).zfill(2),1).replace('effectiveDomain','Q0').replace('IsConvexExtended','Q2')
    neutral+=h+'\n\n'
neutral+='end Neutral\n'
write(run/'blind-packet-v1.md','Fresh restricted-input reconstruction, requested GPT-6 Astra / medium. Read ONLY this packet this pass, no source/public-name map/proof bodies/prior verdict/other files. Q0/Q1/Q2 definitions and M01/M02/M03 unproved actual headers, complete scoped context. Reconstruct all six objects in seven semantic slots; retain local versus global finite-part facts, interior point, global noBottom, all-y bound, derivative-at-point and full real ConvexOn helper hypotheses. Imported gradient/toReal conventions are interpretations, not inspected runtime definitions. Write ONLY blind-reconstruction-v1.md/blind-receipt-v1.json here with exact raw packet/report SHA, sole input currentpass, prior history not erased, no compilation/source/human/external/runtime attestation claim.\n\n```lean\n'+neutral+'```')
dag='finitePart_eventually <- open interior/effectiveDomain/noBottom/coe_toReal; convex_gradient_lower_bound <- affine-line derivative/ConvexOn slope/gradient derivative; theorem_2_7 <- both local helpers + shared convexExtended_iff_toReal + explicit outside-domain top case.'
write(run/'draft-freeze-v1.json',dict(stage='draft',headers=headers,module={module.as_posix():sha(module)},canary={canary.as_posix():sha(canary)},source_sha256=sha(source),context_sha256=sha(contract/'context.lean.txt'),source_intent_sha256=sha(contract/'source-intent.md'),retained_proofs=3,new_proofs=0,definitions=0,source_accepted=False,DAG=dag))
write(run/'00_context.md','Whole Chapters1-16 real Goal ACTIVE/unbudgeted. Previous finite-loss two-terminal package delivered OPENdraftPR157 finalexacta6607d8213860619965c7018e4dd2effff58422a, canonical originmain6847 unchanged/unmerged. Same isolated checkout new branchcodex/research-online-first-order-migration based on that exact verified head.3retained first-order proofs/0newproofs, source Theorem2.7 p11PDF23 reread/hash verified; full contract/blind/source gates now draft. Earlier accepted artifacts/globalSGB/sharedGit/.lake/otherworktrees preserved. This migration does not yet decrement19remaining legacy modules or accept Chapter2.')
write(run/'10_upper_director-v1.md','Select next retained source Theorem2.7 supporting-gradient endpoint for distinct contract/body migration. Source differentiability at interior effective-domain point must correspond to proved local canonical finite-part representation. Preserve all-y comparison including top outside; no global finite-loss or differentiability rewrite. Three proof statements/zero definitions/newproofs. One lower reuse route after stabilization; separate required semantic actors, requested GPT6Astra/medium.')
write(run/'20_architect-v1.md',intent+'\n\nDAG: '+dag)
window=intent+'\n\nDAG: '+dag+'\nAllowed edits: leading source comment and only online-first-order reader subtree; exact public headers/proof code and current canary bytes fixed. Actual local/type/API retrieval and compiled graph readiness before proving; no new proof-count credit.'
replace_scaffold('tasks/'+task+'.md','# Supporting-gradient migration\n\n'+window)
replace_scaffold('conversion-windows/'+task+'.md','# First-order conversion window v1\n\n'+window)
replace_scaffold('proof-obligations/'+task+'.md','# Fixed source terminal and exact local bridges\n\n'+window+'\nRemaining gates:distinct source contract/body/final reader, current axioms/canary/guards/root/Tests/full harness/shared registry/site/scoped raw/contributor/PR. No chapter/book completion.')
write(run/'proof-obligations-v1.json',dict(stage='draft',required=[dict(name=n,statement_hash=h,state='source-review-pending') for n,h in headers.items()],terminal='theorem_2_7',DAG=dag,retained_proofs=3,new_proofs=0,chapter_complete=False,goal_complete=False))
gate('existing-public-retrieval-v1',sys.executable,'-X','utf8','tools/bandit.py','list-lean-decls','--include-tests','--statement','theorem_2_7')
gate('draft-lifecycle-v1',sys.executable,'-X','utf8','tools/bandit.py','lifecycle-event','--session',task,'--event','draft','--payload-json',json.dumps(dict(run_id=run.name,retained_proofs=3,new_proofs=0,frozen_headers=headers,source_accepted=False,chapter_complete=False,goal_complete=False)))
print('Three retained exact targets/source/local conversion context/DAG frozen; distinct review pending, no new proofs.')
