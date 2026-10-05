"""Freeze retained optimality targets and source-neighborhood scope before distinct review."""
from pathlib import Path
import json,hashlib,subprocess,sys,re
from pypdf import PdfReader
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header
run=Path(__file__).parent;contract=Path('docs/contracts/online-optimality-migration-v1');task='ONLINE-OPTIMALITY-MIGRATION-20261005'
assert not contract.exists();contract.mkdir()
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(p,x):
 p=Path(p);assert not p.exists(),p;p.parent.mkdir(parents=True,exist_ok=True)
 with p.open('w',encoding='utf-8',newline='\n') as f:
  if isinstance(x,str):f.write(x.rstrip('\n')+'\n')
  else:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
def scaffold(p,x):
 with Path(p).open('w',encoding='utf-8',newline='\n') as f:f.write(x.rstrip('\n')+'\n')
def gate(label,*args):subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),label,*args],check=True)
source=Path('../research-online-ogd/tmp/pdfs/orabona-v10.pdf');assert sha(source)=='cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17'
pdf=PdfReader(source);write(run/'source-printed10-11-pdf22-23.txt','\n'.join(pdf.pages[i].extract_text() for i in [21,22]))
module=Path('BanditRLProof/OnlineConvexOptimality.lean');canary=Path('Tests/OnlineConvexOptimalityCanary.lean')
names=['minOn_real_iff_gradient','minOn_finitePart_iff','theorem_2_8','interior_min_iff_gradient_zero']
text=module.read_text(encoding='utf-8');assert re.findall(r'(?m)^theorem\s+(\S+)',text)==names
prefix=text[:text.index('theorem minOn_real_iff_gradient')];write(contract/'context.lean.txt',prefix)
for p in [module,canary]:(run/('original-'+p.name+'.txt')).write_bytes(p.read_bytes())
intent='''Source Orabona v10 (21June2026), Theorem2.8 and subsequent unnumbered interior-gradient-zero consequence, printed11/PDF23. V nonempty convex, x in V, function convex and differentiable over an OPEN set containing V. Terminal: x is a minimizer over V iff inner(gradient f x,y-x)>=0 for every y in V. No existence, uniqueness, strict convexity, closedness or boundedness conclusion/premise. Boundary minimum may have nonzero gradient; interior V membership is additional for zero-gradient iff. Unnumbered main-text consequence mandatory, not an optional exercise.

Actual four retained APIs: minOn_real_iff_gradient has everywhere-real f, ConvexOn V, x in V and ambient DifferentiableAt f x; no open set or finite-part representation hypothesis. minOn_finitePart_iff has arbitrary EReal f and point/set, x membership and finite values (neTop AND neBottom) on V; no convexity, topology or differentiability premise beyond actual shared Hilbert context. IsMinOn compares values but does NOT supply x membership, so hx explicit. theorem_2_8 retains nonempty convex V, x membership, arbitrary open U containing V, finite values and differentiability of CANONICAL F(z)=(f z).toReal on U, and ConvexOn V F. Existing terminal is an explicit stronger result requiring convexity only on V instead of the source neighborhood convexity. No assertion that these premise sets are equivalent. ConvexOn U F implies the needed V premise by restriction for source instances; canary actually constructs this stronger premise on its U then restricts it. U is not required convex by the actual retained terminal, and no global convexity/finite/noBottom condition outside U is assumed. Source-neighborhood convexity interpretation/embedding must be separately reviewed against the text, not silently asserted equivalent. Canonical F embeds as f on finite U by proved EReal coercion laws; both infinities outside U unrestricted. Complete real inner-product-space generality explicitly includes Euclidean source instances.

interior_min_iff_gradient_zero carries the same actual finite/open/differentiability/convex-on-V hypotheses plus ambient x interior V, not relative interior. Empty interior gives no witness; arbitrary nonclosed/unbounded V allowed. Proof necessity uses actual local-minimum Fermat/fderiv-zero API, sufficiency uses the retained feasible-direction criterion. Actual hd still ensures canonical gradient has derivative meaning, even though pinned fderiv_eq_zero includes a fallback-zero branch for nondifferentiability. Do not erase the derivative premise or claim stationarity suffices for nonconvex losses/boundary points. Four unchanged proofs/zero production definitions/new proof code/registry nodes.

Existing public canary has loss x onpositive halfline/top outside, U=(0,infinity), V=[1,infinity); proves actual convexity on U and restricts to V, finite values, differentiability, minimum1 with NONZERO gradient1, smaller loss at0.5outsideV and larger loss2inside. Second nonconstant quadratic x^2 over open nonclosed V=(-1,infinity), U=univ, actual gradient0 and interior minimum0, distinct values0/1. One canary definition/eight named proofs, with imported preceding accepted loss instance; byte-exact replay pending. Source theorem+unnumbered consequence+two library helpers, not four printed results. Default single lower retained reuse route after distinct blind/source stabilization; fresh actual module/canary/13names/4guards/root/Tests/full harness/shared registry/site/reader/contributor/raw/PR gates. Only leading source qualification comment and online-optimality reader subtree may change; all4headers/proof tokens/canary bytes fixed. Mathematical repairs need new version/source review. Earlier first-order/finite-loss/convex/FTL/OGD acceptance immutable through exact original snapshots. Whole Chapters1-16 real GoalACTIVE/unbudgeted, Chapter2totalnull/incomplete/18legacy migrations before this package; no chapter/book/main/live/merge/retirement/model-upgrade claim.'''
dag='minOn_real_iff_gradient <- accepted real supporting bound + actual derivative/tangent-cone feasible segment; minOn_finitePart_iff <- both-infinity exclusions/coe_toReal/order; theorem_2_8 <- both helpers + open-neighborhood derivative; interior_min_iff_gradient_zero <- finite minimum bridge + ambient interior/local Fermat + theorem_2_8.'
write(contract/'source-intent.md',intent)
write(contract/'source-card.json',dict(source_path=source.as_posix(),source_sha256=sha(source),url='https://arxiv.org/pdf/1912.13213v10',printed_pages=[11],pdf_pages=[23],number='Theorem2.8 and subsequent unnumbered interior consequence',
 source_terminal='Constrained minimizer iff nonnegative all-feasible inner products; ambient interior iff gradientzero',actual_delta='Convexity only on V; canonical finite representation on arbitrary open U; complete real Hilbert generality',retained_proofs=4,new_proofs=0))
headers={}
for n in names:
 header=lean_declaration_header(module,n);digest=hashlib.sha256(header.encode()).hexdigest();headers[n]=digest
 write(contract/(n+'-header.txt'),header)
 assumptions=['(hf : ConvexOn ℝ V f)','(hx : x ∈ V)','(hd : DifferentiableAt ℝ f x)'] if n==names[0] else (
  ['(hx : x ∈ V)','(hfin : ∀ z ∈ V, f z ≠ ⊤ ∧ f z ≠ ⊥)'] if n==names[1] else
  ['(hV : Convex ℝ V)','(hne : V.Nonempty)','(hx : x ∈ V)','(hU : IsOpen U)','(hVU : V ⊆ U)',
   '(hfin : ∀ z ∈ U, f z ≠ ⊤ ∧ f z ≠ ⊥)','(hf : ConvexOn ℝ V (fun z => (f z).toReal))','(hd : DifferentiableOn ℝ (fun z => (f z).toReal) U)'])
 if n==names[3]:assumptions.append('(hxi : x ∈ interior V)')
 write(contract/(n+'.json'),dict(name='BanditRL.OnlineConvex.'+n,statement=header,statement_hash=digest,source_assumptions=assumptions,
  classification='retained-printed-terminal-explicit-generalization' if n==names[2] else ('retained-unnumbered-main-consequence' if n==names[3] else 'retained-explicit-library-helper'),context_hash=sha(contract/'context.lean.txt')))
 args=[sys.executable,'-X','utf8','tools/bandit.py','statement-fence','--declaration','BanditRL.OnlineConvex.'+n,'--file',module.as_posix(),'--output',str(run/('native-draft-fences/'+n+'.json'))]
 for a in assumptions:args+=['--source-assumption',a]
 gate('draft-fence-'+n+'-v1',*args)
 assert json.loads((run/('native-draft-fences/'+n+'.json')).read_text(encoding='utf-8'))['statement_hash']==digest
neutral=prefix.replace('import BanditRLProof.OnlineConvexFirstOrder','import Mathlib.Analysis.Convex.Deriv\nimport Mathlib.Analysis.Calculus.Gradient.Basic\nimport Mathlib.Data.EReal.Basic').replace('namespace BanditRL.OnlineConvex','namespace Neutral')
for i,n in enumerate(names,1):neutral+=lean_declaration_header(module,n).replace('theorem '+n,'theorem M'+str(i).zfill(2),1)+'\n\n'
neutral+='end Neutral\n'
write(run/'blind-packet-v1.md','Fresh restricted-input reconstruction GPT-6 Astra / medium. Read ONLY this packet this pass; no source identity/names/proofs/prior verdict/other files. Four actual unproved headers/imported scoped complete Hilbert context neutralized. Reconstruct seven semantic slots per target, canonical conversion on finite set/neighborhood, ambient versus within derivative/interior, candidate membership versus IsMinOn comparison, all-feasible criterion/boundary and gradientzero extra condition. Imported semantics are interpretation, not inspected implementation. Write ONLY blind-reconstruction-v1.md/blind-receipt-v1.json here with sole-current-input packet/report SHA, prior history not erased, no compilation/source/human/external/runtime attestation claim.\n\n```lean\n'+neutral+'```')
write(run/'draft-freeze-v1.json',dict(stage='draft',headers=headers,module={module.as_posix():sha(module)},canary={canary.as_posix():sha(canary)},source_sha256=sha(source),context_sha256=sha(contract/'context.lean.txt'),source_intent_sha256=sha(contract/'source-intent.md'),retained_proofs=4,new_proofs=0,definitions=0,source_accepted=False,DAG=dag))
write(run/'00_context.md','Persistent whole Chapters1-16 real GoalACTIVE/unbudgeted. Prior OPENdraftPR158 finalexactc9b47c8ba79a234d0dfa6e8ef5643a43677dd33a remote/REST verified, clean checkout; canonical mainorigin6847 unchanged. Same isolated worktree new codex/research-online-optimality-migration stacked exactPR158, not main. Four retained optimality APIs/Theorem2.8+mandatory unnumbered interior consequence/two helpers; zero newproofcode/nodes. Sourcehash/page freshread; proof-count unchanged. Current18legacybeforepackage/Chapter2null/incomplete. Freeze source-premise delta explicitly; distinct actors/body/gates required.')
write(run/'10_upper_director-v1.md','Select next dependency-ready constrained optimality chain after Theorem2.7 acceptance. Boundary criterion is nonnegative feasible-direction inner products, not zero gradient. Retain extra ambient interior for zero-gradient consequence. Inspect source neighborhood convexity versus actual ConvexOn V before stabilization; stronger target explicit, no premise equivalence. Four retained bodies/zero newproofs; single lower route, required distinct semantic actors GPT6Astra/medium.')
write(run/'20_architect-v1.md',intent+'\n\nDAG: '+dag)
for p,title in [('tasks/'+task+'.md','Optimality source migration'),('conversion-windows/'+task+'.md','Optimality conversion window v1'),('proof-obligations/'+task+'.md','Optimality retained exact obligations')]:scaffold(p,'# '+title+'\n\n'+intent+'\n\nDAG: '+dag)
write(run/'proof-obligations-v1.json',dict(stage='draft',required=[dict(name=n,statement_hash=h,state='source-review-pending') for n,h in headers.items()],terminals=names[2:],DAG=dag,retained_proofs=4,new_proofs=0,chapter_complete=False,goal_complete=False))
write(run/'leaves/actual-public-types-v1.lean','import BanditRLProof\n'+''.join('#check @BanditRL.OnlineConvex.'+n+'\n' for n in names)+
 '#check @IsLocalMinOn.hasFDerivWithinAt_nonneg\n#check @sub_mem_posTangentConeAt_of_segment_subset\n#check @IsLocalMin.fderiv_eq_zero\n#check @EReal.coe_toReal\n')
gate('existing-public-retrieval-v1',sys.executable,'-X','utf8','tools/bandit.py','list-lean-decls','--include-tests','--statement','theorem_2_8')
gate('draft-lifecycle-v1',sys.executable,'-X','utf8','tools/bandit.py','lifecycle-event','--session',task,'--event','draft','--payload-json',json.dumps(dict(run_id=run.name,retained_proofs=4,new_proofs=0,frozen_headers=headers,source_accepted=False,chapter_complete=False,goal_complete=False)))
print('Four actual optimality headers/source neighborhood delta/interior consequence/context/DAG frozen; distinct review pending.')
