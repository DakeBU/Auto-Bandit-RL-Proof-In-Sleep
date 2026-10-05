"""Freeze retained signed-integral semantics before distinct contract review."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
from pypdf import PdfReader
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header
run=Path(__file__).parent;prior=Path('runs/online-optimality-migration-20261005')
contract=Path('docs/contracts/online-expectation-migration-v1');task='ONLINE-EXPECTATION-MIGRATION-20261005'
assert not contract.exists();contract.mkdir()
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(p,x):
 p=Path(p);assert not p.exists(),p;p.parent.mkdir(parents=True,exist_ok=True)
 with p.open('w',encoding='utf-8',newline='\n') as h:
  if isinstance(x,str):h.write(x.rstrip('\n')+'\n')
  else:json.dump(x,h,ensure_ascii=False,indent=2);h.write('\n')
def gate(label,*args):subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),label,*args],check=True)
assert subprocess.check_output(['git','branch','--show-current'],encoding='utf-8').strip()=='codex/research-online-expectation-migration'
assert subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf-8').strip()=='7c3b241a13b1b43d1efcd08429f33c93b890a981'
aux=[]
for name in ['run-command.py','commit-owned-v1.py','verify-public-fences-v1.py','check-scoped-diff-v1.py']:
 src=prior/name;out=run/name;assert not out.exists()
 text=src.read_text(encoding='utf-8').replace('online-optimality-migration','online-expectation-migration').replace('ONLINE-OPTIMALITY-MIGRATION','ONLINE-EXPECTATION-MIGRATION').replace('OnlineConvexOptimality','OnlineExpectation').replace('c9b47c8ba79a234d0dfa6e8ef5643a43677dd33a','7c3b241a13b1b43d1efcd08429f33c93b890a981')
 if name=='verify-public-fences-v1.py':text=text.replace('guards=4','guards=10').replace('Four actual guards','Ten actual guards')
 write(out,text);aux.append(dict(path=out.as_posix(),source=src.as_posix(),source_sha256=sha(src),prepared_sha256=sha(out)))
write(run/'auxiliary-workflow-preparation-v1.json',dict(rows=aux,scope='Workflow helpers only, adapted before first execution; no mathematical proof/code change.'))
source=Path('../research-online-ogd/tmp/pdfs/orabona-v10.pdf')
assert sha(source)=='cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17'
pdf=PdfReader(source);write(run/'source-printed11-pdf23.txt',pdf.pages[22].extract_text())
module=Path('BanditRLProof/OnlineExpectation.lean');canary=Path('Tests/OnlineExpectationCanary.lean')
text=module.read_text(encoding='utf-8')
definitions=re.findall(r'(?m)^def\s+(\S+)',text);proofs=re.findall(r'(?m)^theorem\s+(\S+)',text)
assert definitions==['positiveIntegral','negativeIntegral','signedExpectation'] and len(proofs)==7
names=definitions+proofs;prefix=text[:text.index('theorem positiveIntegral_coe')]
write(contract/'context-definitions.lean.txt',prefix)
for p in [module,canary]:(run/('original-'+p.name+'.txt')).write_bytes(p.read_bytes())
intent='''Orabona v10 Theorem2.9, printed11/PDF23, is the parent source endpoint: measurable convex f:R^d->(-infinity,+infinity], measurable random vector with existing finite mean, a.e. effective-domain membership, and f(EX)<=E[fX]. It does not assume loss integrability. This package is explicitly an implementation representation dependency, not seven printed source results and not Jensen acceptance.

Actual arbitrary measurable sample type Omega and arbitrary measure mu; no probability, finite-mass, sigma-finiteness or function measurability premise on definitions or the two coercion identities. positiveIntegral is the ENNReal lintegral of (f omega).toENNReal; negativeIntegral is lintegral of (-f omega).toENNReal; signedExpectation is their EReal-embedded difference. These are total Lean operations; mathematical signed expectation use requires at least one finite part and appropriate measurability. Both parts infinite is excluded from that interpretation: pinned EReal subtraction gives top-top=bottom, not a legitimate undefined signed expectation. No claim of a probability mean for an arbitrary measure.

positiveIntegral_coe/negativeIntegral_coe are arbitrary-real-function coercion identities without integrability/measurability premises. The two coe_ne_top proofs require actual Bochner Integrable real f, which includes a.e. strong measurability and finite norm integral. signedExpectation_coe_integrable under the same premise proves exact equality with embedded real Bochner integral, not equality under arbitrary nonintegrability/fallback integral zero. signedExpectation_of_nonneg requires only a.e. f>=0, proves negative part zero and reduction to positive lintegral, with positive-infinite outcomes allowed. signedExpectation_eq_top requires positive part= infinity AND negative part!= infinity and yields positive infinity. No source loss-integrability assumption is introduced; the Jensen parent must separately prove negative-part finiteness from source convexity/integrable-X via affine minorant, rather than assume it or use the finite compatibility case to cover all losses.

Three retained definitions/seven retained proofs, zero new production definitions/proofs/code/registry nodes. Existing canary has twoAtoms=dirac(-1)+dirac(3), mass TWO (not probability): integrable nonconstant identity with signed integral2, not normalized expectation1. Growing n=n+1 under counting measure on naturals is nonnegative, finite at every point, nonconstant, positive integral infinity/negative integral zero, hence signed integral top. Counting measure is NOT a probability law; this canary proves the foundation infinite branch only, not the parent's probability infinite-loss example. Six named canary proofs/two definitions, all bytes fixed.

Single retained reuse route after distinct semantic stabilization. Allowed edits leading source/dependency qualification comment and only online-expectation reader subtree; all10public headers/full definition context/proof tokens/canary bytes fixed. Separate fresh public-module/canary/18named axiom/10native guard/compiled scopedgraph/combined root/Tests/fullharness/site/registry/browser/finalreview/contributor/PR gates required. Exact stacked base OPENdraftPR1597c3b241a13b1b43d1efcd08429f33c93b890a981; canonical main6847 unchanged. Legacy17 before package; Chapter2 mandatory total null/incomplete, Chapters1-16 GoalACTIVE/unbudgeted. No main/live/merge/chapter/book completion. Historical accepted snapshots immutable; no source/toolchain changes.'''
dag='definitions -> coercion identities -> integrability of positive/negative parts -> finite Bochner compatibility; a.e. nonnegative -> negative part0 -> nonnegative reduction; positive infinite + negative finite -> top branch. Parent: accepted extended-convex APIs + future reviewed affine minorant + Integrable X -> finite negative part, then either top branch or finite compatibility + nonclosed convex barycenter -> Theorem2.9.'
write(contract/'source-intent.md',intent)
write(contract/'source-card.json',dict(source_path=source.as_posix(),source_sha256=sha(source),url='https://arxiv.org/pdf/1912.13213v10',printed_pages=[11],pdf_pages=[23],number='Theorem2.9 necessary representation dependency, not printed foundation theorems',retained_proofs=7,retained_definitions=3,new_proofs=0,new_definitions=0,parent_accepted=False))
headers={};fragments={}
for n in names:
 header=lean_declaration_header(module,n);digest=hashlib.sha256(header.encode()).hexdigest();headers[n]=digest
 assumptions=['(hf : Integrable f μ)'] if n.endswith('_ne_top') or n=='signedExpectation_coe_integrable' else (['(hf : ∀ᵐ ω ∂μ, 0 ≤ f ω)'] if n=='signedExpectation_of_nonneg' else (['(hp : positiveIntegral μ f = ∞)','(hn : negativeIntegral μ f ≠ ∞)'] if n=='signedExpectation_eq_top' else []))
 fragments[n]=assumptions
 write(contract/(n+'-header.txt'),header)
 write(contract/(n+'.json'),dict(name='BanditRL.OnlineConvex.'+n,statement=header,statement_hash=digest,source_assumptions=assumptions,classification='retained-definition' if n in definitions else 'retained-library-representation-helper',context_hash=sha(contract/'context-definitions.lean.txt')))
 args=[sys.executable,'-X','utf8','tools/bandit.py','statement-fence','--declaration','BanditRL.OnlineConvex.'+n,'--file',module.as_posix(),'--output',str(run/('native-draft-fences/'+n+'.json'))]
 for a in assumptions:args+=['--source-assumption',a]
 gate('draft-fence-'+n+'-v1',*args)
 assert json.loads((run/('native-draft-fences/'+n+'.json')).read_text(encoding='utf-8'))['statement_hash']==digest
neutral=prefix.replace('import BanditRLProof.OnlineConvexExtended','import Mathlib.Data.EReal.Basic').replace('namespace BanditRL.OnlineConvex','namespace Neutral')
neutral+= '\n\n'.join(lean_declaration_header(module,n) for n in proofs)+'\nend Neutral\n'
neutral=neutral.replace('/-- Signed positive-minus-negative expectation. Mathematical use requires at least one\npart to be finite; Jensen\'s source assumptions will prove the negative part finite. -/','')
for i,n in enumerate(names,1):neutral=re.sub(r'\b'+re.escape(n)+r'\b','N'+str(i).zfill(2),neutral)
write(run/'blind-packet-v1.md','Fresh restricted-input reconstruction, GPT-6 Astra / medium. Read ONLY this packet this pass: no source identity, proof bodies, source verdicts or other files. Three actual definitions and seven unproved headers neutralized. Reconstruct seven slots, arbitrary-measure versus probability/normalization, total definitions versus legitimate signed-integral meaning, both-infinite boundary, actual Integrable assumption and a.e. nonnegativity/infinite-positive branch. Imported semantics may be interpreted, not claimed inspected. Write ONLY blind-reconstruction-v1.md and blind-receipt-v1.json here with sole-current-input packet/report SHA; prior history not erased; no source/compilation/human/external/runtime attestation.\n\n```lean\n'+neutral+'```')
write(run/'draft-freeze-v1.json',dict(stage='draft',headers=headers,definitions=definitions,proofs=proofs,module={module.as_posix():sha(module)},canary={canary.as_posix():sha(canary)},source_sha256=sha(source),context_sha256=sha(contract/'context-definitions.lean.txt'),retained_proofs=7,retained_definitions=3,new_proofs=0,new_definitions=0,source_accepted=False,DAG=dag))
write(run/'00_context.md','Whole Chapters1-16 ACTIVE unbudgeted Goal; exact OPENdraftPR1597c3b241a13b1b43d1efcd08429f33c93b890a981 delivered/remotely verified, clean checkout before new branch codex/research-online-expectation-migration. Same shared Lean graph, isolated checkout; mainorigin6847 unchanged. Signed integral foundations only: seven retained proofs/three retained definitions/zero new production code/nodes. Parent Jensen/Chapter2 not accepted by this package. Legacy17 before; Chapter2 total null/incomplete.')
write(run/'10_upper_director-v1.md','Select necessary signed-expectation representation dependency before Jensen. Retain positive-infinite branch; arbitrary measure foundation canary is not a probability Jensen example. Stabilize exact definition semantics/finite part legitimacy and all7helpers before retained body replay; single lower route, required distinct actors GPT6Astra/medium.')
write(run/'20_architect-v1.md',intent+'\n\nDAG: '+dag)
for folder,title in [('tasks','Signed expectation retained migration'),('conversion-windows','Signed expectation conversion window v1'),('proof-obligations','Signed expectation exact obligations')]:write(Path(folder)/(task+'.md'),'# '+title+'\n\n'+intent+'\n\nDAG: '+dag)
write(run/'proof-obligations-v1.json',dict(stage='draft',required=[dict(name=n,statement_hash=h,state='distinct-source-review-pending') for n,h in headers.items()],DAG=dag,retained_proofs=7,retained_definitions=3,new_proofs=0,parent_accepted=False,chapter_complete=False,goal_complete=False))
write(run/'leaves/actual-public-types-v1.lean','import BanditRLProof\n'+''.join('#check @BanditRL.OnlineConvex.'+n+'\n' for n in names)+'#check @MeasureTheory.integral_eq_lintegral_pos_part_sub_lintegral_neg_part\n#check @MeasureTheory.lintegral_ofReal_ne_top_iff_integrable\n#check @EReal.sub_top\n#check @EReal.top_sub\n')
export=(prior/'leaves/export-scoped-dependencies-v1.lean').read_text(encoding='utf-8')
start=export.index('def targets');end=export.index('\ndef moduleName')
export=export[:start]+'def targets : Array Name := #[\n  '+',\n  '.join('`BanditRL.OnlineConvex.'+n for n in names)+']\n'+export[end:]
export=export.replace('("kind", toJson "theorem")','("kind", toJson <| match info with | .thmInfo _ => "theorem" | .defnInfo _ => "definition" | _ => "other")').replace('four selected retained public theorems; direct type/value boundary only','ten selected retained public declarations (seven proofs, three definitions); direct type/value boundary only')
write(run/'leaves/export-scoped-dependencies-v1.lean',export)
write(run/'utility-audit-v1.md','Read-only preparation corrected a PowerShell rg tools/*.py glob (Windows123), a guessed non-existent bandit export-lean-graph subcommand and missing guessed prior helper filenames by actual rg--files/actual prior exit command. These are not Lean failures or passed gates. Actual export is lake env lean --run the scoped exporter; no failure output overwritten. Native fences are guards, not compilation.')
gate('existing-public-retrieval-v1',sys.executable,'-X','utf8','tools/bandit.py','list-lean-decls','--include-tests','--statement','signedExpectation')
gate('draft-lifecycle-v1',sys.executable,'-X','utf8','tools/bandit.py','lifecycle-event','--session',task,'--event','draft','--payload-json',json.dumps(dict(run_id=run.name,frozen_headers=headers,retained_proofs=7,retained_definitions=3,new_proofs=0,source_accepted=False,chapter_complete=False,goal_complete=False)))
print('Ten retained headers/three definition semantics/source dependency/DAG frozen; distinct review pending.')
