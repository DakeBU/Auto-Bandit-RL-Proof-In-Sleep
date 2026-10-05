"""Freeze the exact source Jensen and its genuine negative-part producer before proving."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
from pypdf import PdfReader
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header
run=Path(__file__).parent;task='ONLINE-JENSEN-MIGRATION-20261005'
contract=Path('docs/contracts/online-jensen-migration-v1')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))

def write(p,x):
 p=Path(p);assert not p.exists(),p;p.parent.mkdir(parents=True,exist_ok=True)
 with p.open('w',encoding='utf-8',newline='\n') as f:
  if isinstance(x,str):f.write(x.rstrip('\n')+'\n')
  else:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')

def gate(label,*args):subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),label,*args],check=True)
assert subprocess.check_output(['git','branch','--show-current'],encoding='utf-8').strip()=='codex/research-online-jensen-migration'
assert subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf-8').strip()=='2b4586db952b0e4ed0b7630f2d471c75a9af0f74'
assert load(run/'actual-public-types-v2-01-exit.json')['exit_code']==0
assert load(run/'retained-module-types-v1-01-exit.json')['exit_code']==0
assert not contract.exists();contract.mkdir()
source=Path('../research-online-ogd/tmp/pdfs/orabona-v10.pdf')
assert sha(source)=='cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17'
write(run/'source-printed11-pdf23.txt',PdfReader(source).pages[22].extract_text())
public=Path('BanditRLProof/OnlineJensen.lean');canary=Path('Tests/OnlineJensenCanary.lean')
text=public.read_text(encoding='utf-8');names=re.findall(r'(?m)^theorem\s+(\S+)',text)
assert names==['jensen_negativeIntegral_ne_top','theorem_2_9']
canarytext=canary.read_text(encoding='utf-8');assert len(re.findall(r'(?m)^(?:lemma|theorem)\s+',canarytext))==13
assert len(re.findall(r'(?m)^def\s+',canarytext))==3 and len(re.findall(r'(?m)^instance\s*:',canarytext))==2
for p in [public,canary]:(run/('original-'+p.name+'.txt')).write_bytes(p.read_bytes())
prefix=text[:text.index('theorem jensen_negativeIntegral_ne_top')]
contexts={n:prefix+'end BanditRL.OnlineConvex\n' for n in names};write(contract/'scoped-contexts.json',contexts)
intent='''Orabona v10 Theorem2.9 printedp11/PDF23: measurable convex f:R^d→(-infinity,+infinity], an R^d-valued random element on a probability space with E[X] exists and AE membership in dom f, implies f(E[X])≤E[f(X)]. This package revalidates that source terminal plus ONE required library negative-part producer, not two printed source results. The source expected loss may be +infinity. NO loss-integrability, closed/lsc/full-dimensional domain, finite-support law, boundedness or differentiability assumption is added.

Interpret E[X] exists as ordinary FINITE Lebesgue coordinate expectations. For finitely many real coordinates, existence of each finite Lebesgue integral requires integrability (both scalar positive/negative parts finite); finite-dimensional norm equivalence gives genuine Bochner integrability. Pinned actual integrable_pi_iff and integrable_piLp_iff verify coordinate-integrability equivalence, including Euclidean PiLp. This is a source-implicit mathematical interpretation to review explicitly, not an unrecorded source word replacement, total-Bochner nonintegrable-zero convention or principal-value mean. Required X measurability is the random-element condition; loss measurability is explicit in source.

Actual common class scope: measurable Ω, finite-dimensional real normed E with supplied MeasurableSpace E/BorelSpace E; probability measure μ. No supplied CompleteSpace or inner-product parameter (finite-dimensional completeness available internally). Source Euclidean/Borel spaces are included by an explicit generalization, no arbitrary infinite-dimensional nonclosed Jensen claim. All x globally f(x)≠bottom preserves source codomain, convexity is actual real-height epigraph convexity, dom={x|f(x)<top}; no-bottom makes sampled domain values finite. AE domain membership is not replaced by everywhere membership or supplied MeasurableSet(domain).

Both exact retained headers quantify probability μ, f/hbot/hf/hfm, X/hXm/hX and hdom. jensen_negativeIntegral_ne_top returns actual negativeIntegral μ (f∘X)≠infinity; it must PRODUCE this from assumptions, not assume it. Body obtains a domain witness from probability AE membership, invokes accepted global affine minorant, proves a(X)+b integrable via genuine Integrable X and finite measure, and pointwise bounds negative part by that of the real affine loss; accepted real-integrable compatibility gives finite negative integral. Its hfm/hXm may be unused in the body but remain in the exact frozen public signature; no silent removal or new hypothesis.

theorem_2_9 first invokes that producer. Infinite positive part with finite negative part yields legitimate signedExpectation=top, hence the inequality, without assuming finite loss mean. Finite positive part: Y=(f∘X).toReal is measurable; hbot/AEdom prove AE real embedding equality. Both part integrals finite produce actual Integrable max(Y,0)/max(-Y,0), their difference gives Integrable Y. The actual joint vector (X,Y) lies AE in real epigraph and is genuinely integrable; accepted barycenter theorem puts its mean in that ORIGINAL possibly nonclosed epigraph. integral_pair and signedExpectation_coe_integrable plus actual AE equality produce the exact terminal. No assumed Integrable Y, epigraph mean, finite negative part or Jensen bound oracle; no closure substitution.

SignedExpectation is the retained total EReal positiveIntegral-minus-negativeIntegral definition. Mathematical use here is legitimate because negative finiteness is produced; its both-infinite total-bottom convention is outside this theorem's reachable regime. Source expected loss is never negative-infinite under these hypotheses, may positive-infinite; theorem's conclusion alone does not promise finite mean-loss or finite regret. In the infinite-positive branch it does not prove mean in effective domain. No minimum/support contact, strict inequality or quantitative gradient claim.

Meaningful unchanged whole canary: normalized halfdirac1+halfdirac3, mean2 and expected square5 with nonconstant finite values; normalized geometric P(N=n)=(3/4)(1/4)^n, X=2^n genuinely integrable but square positive integral infinite; nonclosed lower-dimensional coordinate/top-outside loss under genuine probability law, AE domain and actual source terminal. Thirteen canary proofs/three definitions/two anonymous probability instances; verify actual generated instance names before final named audit. Planned20 named axiom entries =2public+13proofs+3defs+2instances. Canary is not unnormalized counting-measure evidence. Preserve bytes and all canary hypotheses.

Allowed production delta ONLY leading source/scope comment and selected online-jensen reader subtree after distinct source/body review. Two exact headers, proof tokens and full canary bytes frozen; no new proof code/definitions/registry nodes or toolchain changes. Default single lower route: ready negative producer before final terminal. Three required distinct automated actors requested GPT-6 Astra/medium; no human/external/runtime attestation, prior history not erased. Native CLI gates are separate from prompt/file-role conventions. Stacked OPENdraft PR162 exact2b4586db952b0e4ed0b7630f2d471c75a9af0f74, not main. Legacy14 before package, Chapter2 mandatory total null/incomplete, persistent Chapters1-16 Goal ACTIVE/unbudgeted; no whole chapter/book acceptance or merge/deploy/retirement.'''
dag='accepted convex_affine_minorant + actual Integrable affine(X) + negativeIntegral_coe_ne_top -> jensen_negativeIntegral_ne_top; producer + signedExpectation_eq_top -> infinite branch; producer + finite positive part + measurable toReal/AE embedding + actual integrable positive/negative parts -> Integrable Y; accepted original-set integral_mem_convex_finiteDimensional on real epigraph + actual pair-integrability/integral_pair + signedExpectation_coe_integrable/AE equality -> theorem_2_9.'
write(contract/'source-intent.md',intent)
write(contract/'source-card.json',dict(source_path=source.as_posix(),source_sha256=sha(source),url='https://arxiv.org/pdf/1912.13213v10',printed_pages=[11],pdf_pages=[23],number='Theorem2.9 plus necessary negative-part producer',retained_proofs=2,new_proofs=0,new_definitions=0,source_mean_interpretation='Finite Lebesgue coordinate expectations, actual integrable_piLp_iff verification; explicit reviewer gate pending',source_accepted=False))
assumptions=['(μ : Measure Ω) [IsProbabilityMeasure μ]','(f : E → EReal)','(hbot : ∀ x, f x ≠ ⊥)','(hf : IsConvexExtended f)','(hfm : Measurable f)','(X : Ω → E)','(hXm : Measurable X)','(hX : Integrable X μ)','(hdom : ∀ᵐ ω ∂μ, X ω ∈ effectiveDomain f)']
headers={};neutral=prefix.replace('namespace BanditRL.OnlineConvex','namespace Neutral')+'open BanditRL.OnlineConvex\n\n'
for i,name in enumerate(names,1):
 header=lean_declaration_header(public,name);digest=hashlib.sha256(header.encode()).hexdigest();headers[name]=digest
 write(contract/(name+'-header.txt'),header)
 write(contract/(name+'.json'),dict(name='BanditRL.OnlineConvex.'+name,statement=header,statement_hash=digest,source_assumptions=assumptions,classification='source-Theorem2.9-terminal' if i==2 else 'required-negative-part-producer',context_hash=sha(contract/'scoped-contexts.json')))
 args=[sys.executable,'-X','utf8','tools/bandit.py','statement-fence','--declaration','BanditRL.OnlineConvex.'+name,'--file',public.as_posix(),'--output',str(run/('native-draft-fences/'+name+'.json'))]
 for a in assumptions:args+=['--source-assumption',a]
 gate('draft-fence-'+name+'-v1',*args)
 assert load(run/('native-draft-fences/'+name+'.json'))['statement_hash']==digest
 neutral+=header.replace('theorem '+name,'theorem N'+str(i).zfill(2),1)+'\n\n'
neutral+='end Neutral\n'
write(run/'blind-packet-v1.md','Required restricted reconstruction GPT-6 Astra/medium. Read ONLY this packet in this pass; no source identity/numbered original names/prior verdicts/other files/proof bodies. Two neutral unproved headers, exact imports/scoped context. Interpret named imported predicates only from their names and supplied neutral notation, explicitly flag that their actual definitions were NOT independently inspected. Reconstruct seven slots including probability normalization, AE domain membership, global no-bottom, genuine Integrable vector versus total Bochner fallback, finite negative part versus assumption, possibly +infinite signed loss. FiniteD real normed/Borel scope, no loss-integrability/closedness/lsc/full-dimensional-domain hypothesis. Write ONLY blind-reconstruction-v1.md/blind-receipt-v1.json in this run with sole packet/report SHA and reading boundary/history not erased; no compilation/source/human/external/runtime attestation.\n\nNeutral notation: effectiveDomain is the below-top domain; IsConvexExtended names convexity via a real-height epigraph. positiveIntegral/negativeIntegral name total nonnegative part integrals; signedExpectation names their EReal difference. These are notation supplied by the formalizer, not decoder-inspected bodies.\n\n```lean\n'+neutral+'```')
write(run/'draft-freeze-v1.json',dict(stage='draft',headers=headers,module={public.as_posix():sha(public)},canary={canary.as_posix():sha(canary)},source_sha256=sha(source),scoped_context_sha256=sha(contract/'scoped-contexts.json'),retained_proofs=2,definitions=0,new_proofs=0,new_definitions=0,source_accepted=False,DAG=dag))
write(run/'10_upper_director-v1.md','Close the source Theorem2.9 endpoint only after genuine finite-negative-part production and distinct source review. Reuse exact existing two bodies with accepted minorant/barycenter/representation dependencies; no loss-integrability assumption. Review finite Lebesgue mean wording explicitly. Single lower route, distinct automated Astra/medium actors, zero new code/nodes; whole Chapter2/Book Goal remain incomplete.')
write(run/'20_architect-v1.md',intent+'\n\nDAG: '+dag)
for folder,title in [('tasks','Source Jensen retained revalidation'),('conversion-windows','Source Jensen conversion window v1'),('proof-obligations','Source Jensen exact obligations')]:write(Path(folder)/(task+'.md'),'# '+title+'\n\n'+intent+'\n\nDAG: '+dag)
write(run/'proof-obligations-v1.json',dict(stage='draft',required=[dict(name=n,statement_hash=h,state='distinct-source-review-pending') for n,h in headers.items()],DAG=dag,retained_proofs=2,new_proofs=0,source_accepted=False,chapter_complete=False,goal_complete=False))
export=Path('runs/online-minorant-migration-20261005/leaves/export-scoped-dependencies-v1.lean').read_text(encoding='utf-8');start=export.index('def targets');end=export.index('\ndef moduleName')
export=export[:start]+'def targets : Array Name := #[\n  '+',\n  '.join('`BanditRL.OnlineConvex.'+n for n in names)+']\n'+export[end:]
export=export.replace('four selected retained affine-support/minorant theorems; direct type/value boundary only','two selected retained source-Jensen/negative-part theorems; direct type/value boundary only')
write(run/'leaves/export-scoped-dependencies-v1.lean',export)
gate('existing-public-retrieval-v1',sys.executable,'-X','utf8','tools/bandit.py','list-lean-decls','--include-tests','--statement','theorem_2_9')
gate('draft-lifecycle-v1',sys.executable,'-X','utf8','tools/bandit.py','lifecycle-event','--session',task,'--event','draft','--payload-json',json.dumps(dict(run_id=run.name,frozen_headers=headers,retained_proofs=2,new_proofs=0,source_accepted=False,chapter_complete=False,goal_complete=False)))
print('Source Jensen and genuine negative-part producer exact headers/source/mean interpretation/DAG frozen; distinct review pending.')
