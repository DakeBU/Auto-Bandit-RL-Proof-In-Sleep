"""Freeze the exact nonclosed barycenter dependency and its two supporting helpers."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
from pypdf import PdfReader
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header
run=Path(__file__).parent;prior=Path('runs/online-expectation-migration-20261005')
contract=Path('docs/contracts/online-barycenter-migration-v1');task='ONLINE-BARYCENTER-MIGRATION-20261005'
assert not contract.exists();contract.mkdir()
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(p,x):
 p=Path(p);assert not p.exists(),p;p.parent.mkdir(parents=True,exist_ok=True)
 with p.open('w',encoding='utf-8',newline='\n') as handle:
  if isinstance(x,str):handle.write(x.rstrip('\n')+'\n')
  else:json.dump(x,handle,ensure_ascii=False,indent=2);handle.write('\n')
def gate(label,*args):subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),label,*args],check=True)
assert subprocess.check_output(['git','branch','--show-current'],encoding='utf-8').strip()=='codex/research-online-barycenter-migration'
assert subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf-8').strip()=='b2b70fa8cf10095ba681eb1ff3e635c98ca2bc56'
assert json.loads((run/'actual-public-types-v1-01-exit.json').read_text(encoding='utf-8'))['exit_code']==0
assert sha(run/'run-command.py')==sha(prior/'run-command.py')
write(run/'auxiliary-run-command-reuse-v1.json',dict(path=(run/'run-command.py').as_posix(),source=(prior/'run-command.py').as_posix(),sha256=sha(run/'run-command.py'),boundary='Byte-exact copy was already used for the actual type probe; hash recorded after that use, not claimed captured before execution.'))
source=Path('../research-online-ogd/tmp/pdfs/orabona-v10.pdf');assert sha(source)=='cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17'
write(run/'source-printed11-pdf23.txt',PdfReader(source).pages[22].extract_text())
module=Path('BanditRLProof/OnlineConvexBarycenter.lean');canary=Path('Tests/OnlineConvexBarycenterCanary.lean')
text=module.read_text(encoding='utf-8');names=re.findall(r'(?m)^theorem\s+(\S+)',text)
assert names==['supporting_functional_ae_eq_mean','supporting_functional_at_closure','integral_mem_convex_finiteDimensional']
for p in [module,canary]:(run/('original-'+p.name+'.txt')).write_bytes(p.read_bytes())
imports=text[:text.index('section SupportEquality')]
scaffolds={}
for section,name in zip(['SupportEquality','FiniteSupport','Barycenter'],names):
 start=text.index('section '+section);end=text.index('theorem '+name,start)
 scaffolds[name]=imports+text[start:end]+'end '+section+'\nend BanditRL.OnlineConvex\n'
write(contract/'scoped-contexts.json',scaffolds)
intent='''Source Orabona v10 Theorem2.9, printed11/PDF23, is the parent Jensen endpoint for measurable convex f:R^d->(-infinity,+infinity], probability random vector with existing finite mean and a.e.domain membership, allowing positive-infinite expected loss. This package is its necessary nonclosed-convex-set barycenter proof dependency, not three printed results or Jensen acceptance. Its precise terminal is mean membership in s ITSELF, not only closure s. No closedness, full-dimensional interior, finite support, boundedness or MeasurableSet s assumption can replace the frozen target.

Actual @types already checked: supporting_functional_ae_eq_mean works in a COMPLETE real normed space (not restricted finite dimension), arbitrary measurable Omega/probability mu, Integrable X and continuous real linear functional a, with AE a(X)<=a(meanX). It yields AE equality of functional values, NOT X=meanX or a nonzero-functional existence claim. a may be zero in this helper. Integrable includes genuine AEstrong measurability and finite norm integral, not a total-integral fallback. Probability mass1 is essential to integral of the constant.

supporting_functional_at_closure is geometric/deterministic: finite-dimensional real normed E, convex s, x in closure s and x NOT in AMBIENT interior s, yielding nonzero continuous linear a with a(y)<=a(x) for all y in s. No Omega/measure/differentiability/closedness/nonempty-interior/strict separation hypothesis or conclusion. It includes lower-dimensional empty-ambient-interior sets, using proper affine span rather than imposing full dimension. The source Euclidean setting is included; no relative-interior substitution or a(x)=0 normalization is claimed.

integral_mem_convex_finiteDimensional has measurable Omega, finite-dimensional real normed E with explicitly RETAINED MeasurableSpace E/BorelSpace E in actual @type, probability mu, convex s, Integrable X and AE X in s. No pointwise membership or separately supplied Measurable X/MeasurableSet s requirement. Probability/integrability govern empty-space/set cases; no dimension-positive premise added. Finite-dimensional real normed generality contains source Euclidean spaces. This does not claim the arbitrary nonclosed membership endpoint in infinite dimension.

Actual proof DAG: mathlib closed-convex integral theorem gives mean in closure s only; if mean assumed outside s then not interior; supporting nonzero functional (nonempty interior Hahn-Banach or empty-interior proper affine-span annihilator); support inequality + linear integral commutation/probability constant yields AE equality; center X-mean into proper kernel with dimension strictly smaller; actual AE representative/subtype isometry proves integrability and kernel mean0; affine preimage convexity preserves AE membership; strong induction on finrank gives mean in s, contradicting outside. Integrability of the lift, zero kernel mean and finite rank descent must be PRODUCED by bodies, not consumer assumptions. No closedness weakening or assumed barycenter conclusion.

Existing meaningful public canary is probability halfdirac1+halfdirac3, vector(x)=(x,0), ray={p|p.1>0 and p.2=0}, convex and nonclosed, lower-dimensional in R x R. Actual Integrable/vector AE membership/mean(2,0)/nonconstant support and nonclosed proof instantiate the full terminal. Three canary definitions/seven proofs/one named probability instance, all bytes fixed. Three retained production proofs/no definitions/zero new code/nodes; 14 named axioms planned including the probability instance. Separate contract/body/final reader phases and actual focused/root/Tests/fullharness/fences/scopedgraph/shared registry/site/canary/browser/contributor/PR gates remain required.

Allowed edits leading dependency qualification comment and only online-barycenter reader subtree; three headers/all proof tokens/canary bytes frozen. Default single lower retained reuse route after dependency readiness and distinct source stabilization. Exact stacked OPENdraftPR160b2b70fa8cf10095ba681eb1ff3e635c98ca2bc56, mainorigin6847 unchanged. Legacy16 before this package; Chapter2 mandatory total null/incomplete and Chapters1-16 realGoalACTIVE/unbudgeted. No Jensen/chapter/book/main/live/merge/newproof completion from this package. Historical preceding accepted receipts/snapshots and failures preserved.'''
dag='supporting_functional_ae_eq_mean <- actual integrable AE inequality/equal-integrals criterion + linear integral commutation + probability constant; supporting_functional_at_closure <- nonempty-interior HB OR proper affine-span annihilator/finite-dimensional closure; integral_mem_convex_finiteDimensional <- mean-in-closure + separator + AE supporting equality + actual centered proper-kernel integrability/zero mean + strict finrank descent/strong induction.'
write(contract/'source-intent.md',intent)
write(contract/'source-card.json',dict(source_path=source.as_posix(),source_sha256=sha(source),url='https://arxiv.org/pdf/1912.13213v10',printed_pages=[11],pdf_pages=[23],number='Theorem2.9 necessary nonclosed barycenter dependency, not printed auxiliary results',retained_proofs=3,new_proofs=0,new_definitions=0,parent_accepted=False))
headers={}
assumptions={names[0]:['(hX : Integrable X μ)','(hle : ∀ᵐ ω ∂μ, a (X ω) ≤ a (∫ ω, X ω ∂μ))'],names[1]:['(hs : Convex ℝ s)','(hx : x ∈ closure s)','(hxi : x ∉ interior s)'],names[2]:['(hs : Convex ℝ s)','(hX : Integrable X μ)','(hmem : ∀ᵐ ω ∂μ, X ω ∈ s)']}
neutral=imports.replace('namespace BanditRL.OnlineConvex','namespace Neutral')
for i,(section,name) in enumerate(zip(['SupportEquality','FiniteSupport','Barycenter'],names),1):
 header=lean_declaration_header(module,name);digest=hashlib.sha256(header.encode()).hexdigest();headers[name]=digest
 write(contract/(name+'-header.txt'),header)
 write(contract/(name+'.json'),dict(name='BanditRL.OnlineConvex.'+name,statement=header,statement_hash=digest,source_assumptions=assumptions[name],classification='retained-library-barycenter-terminal' if i==3 else 'retained-library-support-helper',context_hash=sha(contract/'scoped-contexts.json')))
 args=[sys.executable,'-X','utf8','tools/bandit.py','statement-fence','--declaration','BanditRL.OnlineConvex.'+name,'--file',module.as_posix(),'--output',str(run/('native-draft-fences/'+name+'.json'))]
 for assumption in assumptions[name]:args+=['--source-assumption',assumption]
 gate('draft-fence-'+name+'-v1',*args)
 assert json.loads((run/('native-draft-fences/'+name+'.json')).read_text(encoding='utf-8'))['statement_hash']==digest
 start=text.index('section '+section);end=text.index('theorem '+name,start)
 neutral+=text[start:end]+header.replace('theorem '+name,'theorem N'+str(i).zfill(2),1)+'\nend '+section+'\n\n'
neutral+='end Neutral\n'
write(run/'blind-packet-v1.md','Fresh restricted reconstruction GPT-6 Astra / medium. Read ONLY this packet this pass; no source identity/names/proof bodies/verdicts/other files. Three unproved headers with actual separate section/import/type contexts neutralized. Reconstruct seven slots per target; separate normed complete versus finite-dimensional scopes, explicit Borel context, probability/Integrable/AE membership, ambient interior/closure versus actual-set mean, nonzero separator versus supplied arbitrary functional, no X-constant/closedness inference. Imported semantics are interpretation, not inspected implementation. Write ONLY blind-reconstruction-v1.md/blind-receipt-v1.json here with sole current packet/report SHA; history not erased/no compilation/source/human/external/runtime attestation.\n\n```lean\n'+neutral+'```')
write(run/'draft-freeze-v1.json',dict(stage='draft',headers=headers,module={module.as_posix():sha(module)},canary={canary.as_posix():sha(canary)},source_sha256=sha(source),scoped_context_sha256=sha(contract/'scoped-contexts.json'),retained_proofs=3,definitions=0,new_proofs=0,new_definitions=0,source_accepted=False,parent_accepted=False,DAG=dag))
write(run/'10_upper_director-v1.md','Select actual nonclosed finite-dimensional mean-in-s dependency for Jensen after representation package accepted/delivered. Keep exact s-membership, no closedness/fullinterior/finite-support strengthening. Two supporthelpers distinct scopes, actual @types checked first. Three retained proofs/zero newcode/nodes, required distinct semantic actors GPT6Astra/medium, single lower route.')
write(run/'20_architect-v1.md',intent+'\n\nDAG: '+dag)
for folder,title in [('tasks','Nonclosed barycenter retained migration'),('conversion-windows','Nonclosed barycenter conversion window v1'),('proof-obligations','Nonclosed barycenter exact obligations')]:write(Path(folder)/(task+'.md'),'# '+title+'\n\n'+intent+'\n\nDAG: '+dag)
write(run/'proof-obligations-v1.json',dict(stage='draft',required=[dict(name=n,statement_hash=h,state='distinct-source-review-pending') for n,h in headers.items()],DAG=dag,retained_proofs=3,new_proofs=0,parent_accepted=False,chapter_complete=False,goal_complete=False))
export=(prior/'leaves/export-scoped-dependencies-v1.lean').read_text(encoding='utf-8')
start=export.index('def targets');end=export.index('\ndef moduleName')
export=export[:start]+'def targets : Array Name := #[\n  '+',\n  '.join('`BanditRL.OnlineConvex.'+n for n in names)+']\n'+export[end:]
export=export.replace('ten selected retained public declarations (seven proofs, three definitions); direct type/value boundary only','three selected retained barycenter/support theorems; direct type/value boundary only')
write(run/'leaves/export-scoped-dependencies-v1.lean',export)
gate('existing-public-retrieval-v1',sys.executable,'-X','utf8','tools/bandit.py','list-lean-decls','--include-tests','--statement','integral_mem_convex_finiteDimensional')
gate('draft-lifecycle-v1',sys.executable,'-X','utf8','tools/bandit.py','lifecycle-event','--session',task,'--event','draft','--payload-json',json.dumps(dict(run_id=run.name,frozen_headers=headers,retained_proofs=3,new_proofs=0,source_accepted=False,parent_accepted=False,chapter_complete=False,goal_complete=False)))
print('Three exact nonclosed barycenter/support headers/actual scopes/source parent/DAG frozen; distinct review pending.')
