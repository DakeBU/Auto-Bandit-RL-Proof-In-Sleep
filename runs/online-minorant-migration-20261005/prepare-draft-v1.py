"""Freeze exact finite-dimensional affine-support/minorant dependency contracts."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
from pypdf import PdfReader
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header
run=Path(__file__).parent;prior=Path('runs/online-barycenter-migration-20261005')
contract=Path('docs/contracts/online-minorant-migration-v1');task='ONLINE-MINORANT-MIGRATION-20261005'
assert not contract.exists();contract.mkdir()
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(p,x):
 p=Path(p);assert not p.exists(),p;p.parent.mkdir(parents=True,exist_ok=True)
 with p.open('w',encoding='utf-8',newline='\n') as f:
  if isinstance(x,str):f.write(x.rstrip('\n')+'\n')
  else:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
def gate(label,*args):subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),label,*args],check=True)
assert subprocess.check_output(['git','branch','--show-current'],encoding='utf-8').strip()=='codex/research-online-minorant-migration'
assert subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf-8').strip()=='f68646457a12de93ee6cb8d585a4162f9f0a112c'
for n in ['actual-public-types-v1-01','retained-module-types-v1-01']:assert json.loads((run/(n+'-exit.json')).read_text(encoding='utf-8'))['exit_code']==0
source=Path('../research-online-ogd/tmp/pdfs/orabona-v10.pdf');assert sha(source)=='cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17'
write(run/'source-printed11-pdf23.txt',PdfReader(source).pages[22].extract_text())
module=Path('BanditRLProof/OnlineConvexMinorant.lean');canary=Path('Tests/OnlineConvexMinorantCanary.lean')
text=module.read_text(encoding='utf-8');names=re.findall(r'(?m)^theorem\s+(\S+)',text)
assert names==['affine_support_of_finite_neighborhood','affine_support_of_domain_interior','affine_minorant_of_domain_interior','convex_affine_minorant']
for p in [module,canary]:(run/('original-'+p.name+'.txt')).write_bytes(p.read_bytes())
prefix=text[:text.index('/-- A convex extended-real function')]
contexts={n:prefix+'end BanditRL.OnlineConvex\n' for n in names};write(contract/'scoped-contexts.json',contexts)
intent='''Source Orabona v10 Theorem2.9 printed11/PDF23 is the measurable convex Jensen parent with integrable/existing finite vector mean and AE effective-domain membership under a probability law, allowing positive-infinite expected loss. This package revalidates FOUR RETAINED LIBRARY affine-support/minorant dependencies, not four printed source results or Jensen acceptance. The exact final terminal is a continuous REAL affine global lower bound for convex extended-real f with global nowhere-bottom and nonempty effective domain. No source loss-integrability premise, lsc/closedness/ambient-interior or differentiability of f is added.

Actual four public @types have finite-dimensional real normed E, WITHOUT supplied MeasurableSpace E/BorelSpace E/probability/CompleteSpace/inner-product classes. Finite-dimensional continuity is used for algebraic linear extension. Old v1 contract prose claiming retained Borel instances is historical/stale; actual current public types control this freeze, not that prose. Source Euclidean spaces are included by explicit finite-dimensional normed generality; no arbitrary infinite-dimensional result is claimed.

affine_support_of_finite_neighborhood: convex real epigraph, chosen x and GENUINE neighbourhood eventually-everywhere FINITE f values, gives real continuous affine global lower bound touching f(x). No supplied global hbot/nonempty-domain/closedness/measurability/differentiability/convex-open-U premise. Finite at x alone is NOT the neighbourhood condition. Body must PRODUCE global no-bottom; local finiteness implies properness, rather than bypassing it. The output slope a may zero. Nonzero separating L is in E x R; its vertical coefficient c is proved strictly negative before division, not an assumed oracle or a claim outputa!=0. Fermat applies only to auxiliary identity/continuous linear A, NOT f.

affine_support_of_domain_interior: global hbot, convex real epigraph and chosen x in AMBIENT interior effectiveDomain f yield global support TOUCHING f(x). The body produces finite-neighbourhood via hbot/domain and reuses the ready first helper. The ambient-interior premise belongs ONLY to this helper, not the general terminal; relative interior is not substituted in its statement.

affine_minorant_of_domain_interior: same hbot/convexity/ambient-interior x, gives global minorant by dropping contact equality. It does not independently remove the interior requirement or guarantee a nonzero slope/unique support.

convex_affine_minorant: global hbot, convex real epigraph and NONEMPTY effective domain only, gives continuous real affine lower bound at EVERY x, including extended-top values outside domain. No chosen interior point, contact at a specified boundary point, full-dimensionality, lsc/closedness/measurability/finite support/boundedness/quantitative norm bound/probability/differentiability assumption. All-top is excluded by domain nonempty; zero dimension allowed. Effective domain means f<top and includes bottom generally; global hbot makes its points genuinely finite. Source no-bottom codomain is explicitly preserved.

Actual DAG/producer: finite pointgraph belongs real epigraph but not ambient interior via vertical identity local-min derivative contradiction; accepted nonclosed separator on E x R produces nonzero L; split L(y,t)=A(y)+t*c; upward epigraph implies c<=0; finite neighbourhood and local Fermat on A force c!=0, hence c<0; actual support proves nowhere-bottom and legal division produces affine support. Domain interior produces finite neighbourhood; helper drops contact. General terminal generates intrinsic interior in affine span of domain, translates/restricts to its direction space, proves ambient interior there, applies interior helper, actually extends linear functional and adjusts intercept, then proves the global bound. No desired-minorant/intrinsic-interior/extension/negative-coefficient hypothesis is inserted as an oracle.

Existing meaningful canary: coordinate loss on the lower-dimensional NONCLOSED ray in R x R, top outside. Its total upperAdd implementation has an actual formula f(p)=p.1 on ray and top otherwise; base coordinate is finite everywhere, so no mixed-infinity arithmetic convention is being attributed to the source here. Six proof bodies/one definition establish noBottom/convexity/domain=ray, instantiate general minorant, and prove values1/3/top plus domain nonclosed. No probability/Jensen loss expectation is claimed. All canary bytes fixed;11named axioms planned =4public+6canaryproofs+1canarydefinition. Four retained production proofs/zero definitions/newcode/nodes.

Allowed edits ONLY leading dependency qualification comment and online-minorant reader subtree after distinct source stabilization/body gates; four exact headers/proof tokens/canary bytes fixed. Three distinct required automated actors requestedGPT6Astra/medium, no human/external/runtime attestation, single lower reuse route. Exact stacked OPENdraftPR161f68646457a12de93ee6cb8d585a4162f9f0a112c; mainorigin6847 unchanged. Legacy15 beforepackage; Chapter2mandatorytotalnull/incomplete and wholeChapters1-16GoalACTIVEunbudgeted. General minorant acceptance does NOT accept Jensen negative-part producer/parent/sourcechapter/book/main/live. Prior frozen contracts/receipts/snapshots/failures intact.'''
dag='finite_neighborhood support <- accepted finite-dimensional nonclosed separator + actual auxiliary local-Fermat/negative vertical coefficient/no-bottom proof; domain_interior support <- hbot/domain neighbourhood + first support; interior minorant <- support drops contact; global convex_affine_minorant <- actual convex domain/intrinsic interior/affine-span direction pullback + interior helper + algebraic extension/finite-dimensional continuity/intercept adjustment.'
write(contract/'source-intent.md',intent);write(contract/'source-card.json',dict(source_path=source.as_posix(),source_sha256=sha(source),url='https://arxiv.org/pdf/1912.13213v10',printed_pages=[11],pdf_pages=[23],number='Theorem2.9 necessary affine-minorant dependencies, not printed auxiliary results',retained_proofs=4,new_proofs=0,new_definitions=0,parent_accepted=False))
assumptions={names[0]:['(hf : IsConvexExtended f)','(hneigh : ∀ᶠ y in 𝓝 x, ∃ r : ℝ, f y = (r : EReal))'],names[1]:['(hbot : ∀ y, f y ≠ ⊥)','(hf : IsConvexExtended f)','(hx : x ∈ interior (effectiveDomain f))'],names[2]:['(hbot : ∀ y, f y ≠ ⊥)','(hf : IsConvexExtended f)','(hx : x ∈ interior (effectiveDomain f))'],names[3]:['(hbot : ∀ x, f x ≠ ⊥)','(hf : IsConvexExtended f)','(hne : (effectiveDomain f).Nonempty)']}
headers={};neutral=prefix.replace('namespace BanditRL.OnlineConvex','namespace Neutral')+'open BanditRL.OnlineConvex\n\n'
for i,name in enumerate(names,1):
 header=lean_declaration_header(module,name);digest=hashlib.sha256(header.encode()).hexdigest();headers[name]=digest
 write(contract/(name+'-header.txt'),header);write(contract/(name+'.json'),dict(name='BanditRL.OnlineConvex.'+name,statement=header,statement_hash=digest,source_assumptions=assumptions[name],classification='retained-library-general-minorant-terminal' if i==4 else 'retained-library-affine-support-helper',context_hash=sha(contract/'scoped-contexts.json')))
 args=[sys.executable,'-X','utf8','tools/bandit.py','statement-fence','--declaration','BanditRL.OnlineConvex.'+name,'--file',module.as_posix(),'--output',str(run/('native-draft-fences/'+name+'.json'))]
 for a in assumptions[name]:args+=['--source-assumption',a]
 gate('draft-fence-'+name+'-v1',*args)
 assert json.loads((run/('native-draft-fences/'+name+'.json')).read_text(encoding='utf-8'))['statement_hash']==digest
 neutral+=header.replace('theorem '+name,'theorem N'+str(i).zfill(2),1)+'\n\n'
neutral+='end Neutral\n'
write(run/'blind-packet-v1.md','Fresh restricted reconstruction GPT6Astra/medium. Read ONLY this packet this pass; no source identity/target names/proof bodies/verdicts/other files. Four unproved neutral headers with actual common imports/normed-finiteDim context and projectpredicate name lookup. Reconstruct seven slots per target; named imported predicates cannot be body-inspected this pass, so explicitly separate their interpretation from inspected definitions. Distinguish genuine eventually-neighbourhood finiteness versus finite at one point, global no-bottom supplied versus absent, ambient domain-interior versus final mere nonemptydomain, touching support versus pure global lower bound and outputfunctional possiblyzero. No measurable/probability/Borel/closedness/lsc/loss differentiability/infiniteDim hypothesis/conclusion inferred. Write ONLY blind-reconstruction-v1.md/blind-receipt-v1.json here with solepacket/reportSHA; historynoterased/no compilation/source/human/external/runtime attestation.\n\n```lean\n'+neutral+'```')
write(run/'draft-freeze-v1.json',dict(stage='draft',headers=headers,module={module.as_posix():sha(module)},canary={canary.as_posix():sha(canary)},source_sha256=sha(source),scoped_context_sha256=sha(contract/'scoped-contexts.json'),retained_proofs=4,definitions=0,new_proofs=0,new_definitions=0,source_accepted=False,parent_accepted=False,DAG=dag))
write(run/'10_upper_director-v1.md','Select necessary general affine-minorant dependency after barycenter package accepted/delivered. No loss-integrability/interior/closedness assumption may enter parent/general terminal. Four existing proofs/currentactualtypes rechecked beforefreeze; distinctautomatedAstra/mediumactors, singlelower route, zero newcode/nodes.')
write(run/'20_architect-v1.md',intent+'\n\nDAG: '+dag)
for folder,title in [('tasks','Affine support/minorant retained migration'),('conversion-windows','Affine minorant conversion window v1'),('proof-obligations','Affine minorant exact obligations')]:write(Path(folder)/(task+'.md'),'# '+title+'\n\n'+intent+'\n\nDAG: '+dag)
write(run/'proof-obligations-v1.json',dict(stage='draft',required=[dict(name=n,statement_hash=h,state='distinct-source-review-pending') for n,h in headers.items()],DAG=dag,retained_proofs=4,new_proofs=0,parent_accepted=False,chapter_complete=False,goal_complete=False))
export=(prior/'leaves/export-scoped-dependencies-v1.lean').read_text(encoding='utf-8');start=export.index('def targets');end=export.index('\ndef moduleName')
export=export[:start]+'def targets : Array Name := #[\n  '+',\n  '.join('`BanditRL.OnlineConvex.'+n for n in names)+']\n'+export[end:]
export=export.replace('three selected retained barycenter/support theorems; direct type/value boundary only','four selected retained affine-support/minorant theorems; direct type/value boundary only')
write(run/'leaves/export-scoped-dependencies-v1.lean',export)
gate('existing-public-retrieval-v1',sys.executable,'-X','utf8','tools/bandit.py','list-lean-decls','--include-tests','--statement','convex_affine_minorant')
gate('draft-lifecycle-v1',sys.executable,'-X','utf8','tools/bandit.py','lifecycle-event','--session',task,'--event','draft','--payload-json',json.dumps(dict(run_id=run.name,frozen_headers=headers,retained_proofs=4,new_proofs=0,source_accepted=False,parent_accepted=False,chapter_complete=False,goal_complete=False)))
print('Four exact affine-support/minorant headers/currentscopes/sourceparent/DAG frozen; distinctreview pending.')
