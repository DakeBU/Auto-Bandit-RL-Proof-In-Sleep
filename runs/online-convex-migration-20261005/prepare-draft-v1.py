"""Freeze four retained convex modules without changing their public code."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
from pypdf import PdfReader
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header,_strip_lean_comments
run=Path(__file__).parent
contract=Path('docs/contracts/online-convex-migration-v1')
task='ONLINE-CONVEX-MIGRATION-20261005'
assert not (run/'draft-freeze-v1.json').exists()
contract.mkdir(exist_ok=False)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(p,x):
    p=Path(p);p.parent.mkdir(parents=True,exist_ok=True)
    with p.open('w',encoding='utf-8',newline='\n') as f:
        if isinstance(x,str):f.write(x+'\n')
        else:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
def gate(label,*args):subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),label,*args],check=True)
source=Path('../research-online-ogd/tmp/pdfs/orabona-v10.pdf')
secondary=Path('tmp/rockafellar-conjugate-duality.pdf')
assert sha(source)=='cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17'
assert sha(secondary)=='29d57ab07857b8270c175343746c77b4138f2db6161ae20174a0bba076991b0e'
pdf=PdfReader(source)
write(run/'source-printed9-10-pdf21-22.txt','\n'.join(pdf.pages[i].extract_text() for i in [20,21]))
write(run/'convention-printed6-pdf17.txt',PdfReader(secondary).pages[16].extract_text())
groups={
'OnlineConvexExtended':['definition_2_2','convex_effectiveDomain','effectiveDomain_indicator','convex_indicator_iff','realEpigraph_toReal','convexExtended_iff_toReal','theorem_2_4','convex_add_indicator'],
'OnlineConvexExamples':['convexExtended_coe_iff','example_2_5','example_2_6'],
'OnlineConvexClosures':['convex_comp_affine','convex_iSup','convex_comp_monotone'],
'OnlineConvexSums':['upperAdd_coe','upperAdd_top','top_upperAdd','upperAdd_le_coe_iff','convex_upperAdd','positive_mul_le_coe_iff','convex_nonneg_mul','convex_nonneg_linear_combination']}
defs={'OnlineConvexExtended':['effectiveDomain','realEpigraph','IsConvexExtended','extendedIndicator'],'OnlineConvexSums':['upperAdd']}
deps={
'definition_2_2':[],'convex_effectiveDomain':[],'effectiveDomain_indicator':[],
'convex_indicator_iff':['convex_effectiveDomain','effectiveDomain_indicator'],
'realEpigraph_toReal':[],'convexExtended_iff_toReal':['realEpigraph_toReal'],
'theorem_2_4':['convexExtended_iff_toReal'],'convex_add_indicator':[],
'convexExtended_coe_iff':['convexExtended_iff_toReal'],
'example_2_5':['convexExtended_coe_iff'],'example_2_6':['convexExtended_coe_iff'],
'convex_comp_affine':[],'convex_iSup':[],'convex_comp_monotone':['convexExtended_coe_iff'],
'upperAdd_coe':[],'upperAdd_top':[],'top_upperAdd':[],'upperAdd_le_coe_iff':[],
'convex_upperAdd':['upperAdd_le_coe_iff'],'positive_mul_le_coe_iff':[],
'convex_nonneg_mul':['positive_mul_le_coe_iff','convexExtended_coe_iff'],
'convex_nonneg_linear_combination':['convex_upperAdd','convex_nonneg_mul']}
assumptions={
'definition_2_2':[],'convex_effectiveDomain':['(hf : IsConvexExtended f)'],
'effectiveDomain_indicator':[],'convex_indicator_iff':[],
'realEpigraph_toReal':['(hbot : ∀ x, f x ≠ ⊥)'],
'convexExtended_iff_toReal':['(hbot : ∀ x, f x ≠ ⊥)'],
'theorem_2_4':['(hbot : ∀ x, f x ≠ ⊥)','(hdom : Convex ℝ (effectiveDomain f))'],
'convex_add_indicator':['(hbot : ∀ x, f x ≠ ⊥)','(hf : IsConvexExtended f)','(hV : Convex ℝ V)'],
'convexExtended_coe_iff':[],'example_2_5':[],'example_2_6':[],
'convex_comp_affine':['(hf : IsConvexExtended f)'],
'convex_iSup':['(hf : ∀ i, IsConvexExtended (f i))'],
'convex_comp_monotone':['(hf : IsConvexExtended (fun x => (f x : EReal)))','(hg : IsConvexExtended (fun x => (g x : EReal)))','(hmono : Monotone g)'],
'upperAdd_coe':[],'upperAdd_top':[],'top_upperAdd':[],'upperAdd_le_coe_iff':[],
'convex_upperAdd':['(hf : IsConvexExtended f)','(hg : IsConvexExtended g)'],
'positive_mul_le_coe_iff':['(ha : 0 < a)'],
'convex_nonneg_mul':['(hf : IsConvexExtended f)','(ha : 0 ≤ a)'],
'convex_nonneg_linear_combination':['(hf : IsConvexExtended f)','(hg : IsConvexExtended g)','(ha : 0 ≤ a)','(hb : 0 ≤ b)']}
intent='''Frozen primary source: Orabona arXiv1912.13213v10, 21 June2026; printed9-10/PDF21-22. Def2.2 convex sets uses every x,y in V and strictly interior real weight. Def2.3 extended-real convexity uses a REAL-height epigraph; f permits both infinities. Domain is f(x)<top and includes bottom. Indicator is zero inside V/top outside. Required unnumbered consequences: convex domain, indicator convex iff V convex, and addition of indicator to noBottom convex f on convex V. Empty sets/domains allowed. Theorem2.4 explicitly assumes noBottom and convex effective domain and quantifies only domain points,0<theta<1. Those hypotheses are retained, not moved into a new definition of convexity. Epigraph/toReal and real-valued coercion iff are proved bridges; toReal is only used on finite values in the characterization.

Example2.5 covers all affine inner-product functions including zero slope and arbitrary intercept; Example2.6 covers all norms, even though its proof is left as an exercise. Abstract real module/normed/inner-product space generality includes source finite-dimensional Euclidean instances. No compactness, closedness, strict positivity of norm values, probability or algorithm premise.

Four required p10 closure bullets: nonnegative linear combinations, affine precomposition, real convex/nondecreasing outer composition, and arbitrary indexed supremum. Affine maps need not be injective/continuous. Supremum has no nonempty index or bounded-family assumption and may take both infinities. Monotone composition keeps the source explicitly REAL-valued f and g and global Monotone g. It does not extend g to EReal.

Convention delta: Orabona does not print a mixed-infinity addition convention. The nonnegative-combination interface explicitly adopts the convex-analysis upper addition upperAdd(a,b)=-(-a+-b), supported by Rockafellar Conjugate Duality and Optimization printed6/PDF17. This is an attributed interpretation, not a literal assertion in Orabona. Ordinary mathlib EReal addition is bottom-dominant and fails the unrestricted closure: the existing public spike counterexample must be freshly compiled. upperAdd agrees with finite addition/top dominance and includes improper functions, disjoint domains, zero weights and zero-times-infinity=0. No noBottom/properness/nonempty-domain restriction is added to the general closure. Indicator addition uses ordinary + with explicit noBottom so there is no mixed-infinity ambiguity.

Migration scope is four existing production modules,22 retained actual proof bodies/five definitions, not22 new source theorems/proofs or Chapter2 completion. Every frozen header stays exact; retained bodies must be inspected/freshly compiled after separate distinct-actor source-contract review. Existing canaries are replayed, not counted new mathematical progress. Legacy same-model reviews remain historical. Native command gates and file/prompt semantic review are separate; no single-runtime enforcement, external human review or independent runtime model attestation claim. Whole Chapters1-16 Goal remains active; other required main text and appendix dependencies are not excluded.'''
write(contract/'source-intent.md',intent)
write(contract/'source-card.json',dict(primary=dict(path=str(source),sha256=sha(source),url='https://arxiv.org/pdf/1912.13213v10',printed_pages=[9,10],pdf_pages=[21,22]),
    convention=dict(path=str(secondary),sha256=sha(secondary),url='https://sites.math.washington.edu/~rtr/papers/rtr054-ConjugateDuality.pdf',printed_page=6,pdf_page=17,permission='explicit attributed interpretation; not printed by Orabona'),
    numbered_anchors=['Definition2.2','Definition2.3','Theorem2.4','Example2.5','Example2.6'],unnumbered='effective domain, indicator consequences, four closure bullets',standalone_exercises='optional; Example2.6 mandatory main text'))
headers={};frozen={};modules={};canaries={}
for group,names in groups.items():
    module=Path('BanditRLProof')/(group+'.lean');canary=Path('Tests')/(group+'Canary.lean')
    modules[module.as_posix()]=sha(module);canaries[canary.as_posix()]=sha(canary)
    (run/('original-'+group+'.lean.txt')).write_bytes(module.read_bytes())
    (run/('original-'+group+'Canary.lean.txt')).write_bytes(canary.read_bytes())
    context=module.read_text(encoding='utf-8').split('theorem '+names[0],1)[0]
    write(contract/(group+'-context.lean.txt'),context+'end BanditRL.OnlineConvex')
    for n in names:
        h=lean_declaration_header(module,n);headers[n]=h
        digest=hashlib.sha256(h.encode('utf-8')).hexdigest();frozen[n]=digest
        write(contract/(n+'-header.txt'),h)
        write(contract/(n+'.json'),dict(version=1,name='BanditRL.OnlineConvex.'+n,statement=h,statement_hash=digest,
            source_assumptions=assumptions[n],dependencies=deps[n],file=module.as_posix(),classification='reuse-existing-public-proof',
            evidence_permission='historical same-model acceptance is not distinct source certification; fresh review/build gates required'))
        args=[sys.executable,'-X','utf8','tools/bandit.py','statement-fence','--declaration','BanditRL.OnlineConvex.'+n,'--file',module.as_posix(),'--output',str(run/('native-fences/'+n+'.json'))]
        for a in assumptions[n]:args+=['--source-assumption',a]
        gate('fence-'+n,*args)
        assert json.loads((run/('native-fences/'+n+'.json')).read_text(encoding='utf-8'))['statement_hash']==digest
assert len(frozen)==22 and sum(map(len,defs.values()))==5
extended=_strip_lean_comments(Path('BanditRLProof/OnlineConvexExtended.lean').read_text(encoding='utf-8'))
neutral_context=extended.split('namespace BanditRL.OnlineConvex',1)[1].split('theorem definition_2_2',1)[0]
neutral_context+='\ndef upperAdd (a b : EReal) : EReal := -(-a + -b)\n'
mapping={n:'Q'+str(i) for i,n in enumerate(sum(defs.values(),[]))}
def rename(s):
    for a,b in mapping.items():s=re.sub(r'\b'+a+r'\b',b,s)
    return s
neutral='import Mathlib.Analysis.Convex.Function\nimport Mathlib.Data.EReal.Basic\nimport Mathlib.Analysis.Normed.Module.Convex\nimport Mathlib.Analysis.InnerProductSpace.Basic\n\nnoncomputable section\nopen Set\nnamespace Neutral\n'+rename(neutral_context)+'\n'
name_map={}
for i,(n,h) in enumerate(headers.items(),1):
    m='M'+str(i).zfill(2);name_map[m]=n
    neutral+=rename(h.replace('theorem '+n,'theorem '+m,1))+'\n\n'
neutral+='end Neutral\n'
write(contract/'neutral-name-map.json',name_map)
write(run/'blind-packet-v1.md','Fresh restricted-input reconstruction, requested GPT-6 Astra / medium. Read ONLY this packet in this pass. No source identity, theorem-name map, prior verdict, proof body or other file. Five definitions are mathematical context. Reconstruct Q0-Q4 and M01-M22 in seven slots:objects,quantifiers,assumptions,conclusions,constants/normalization,information/probability,boundary. Missing proof bodies are intentional; no compilation/source acceptance claim. Write ONLY blind-reconstruction-v1.md and blind-receipt-v1.json beside this packet, with exact raw input/report SHA, actor/requested medium, prior history not erased, sole input this pass and no human/external review.\n\n```lean\n'+neutral+'```')
write(run/'draft-freeze-v1.json',dict(stage='draft',headers=frozen,groups=groups,definitions=defs,modules=modules,canaries=canaries,
    primary_sha256=sha(source),convention_sha256=sha(secondary),source_intent_sha256=sha(contract/'source-intent.md'),
    retained_proofs=22,new_proofs=0,new_registry_nodes=0,public_edits=False,source_accepted=False))
table='| Target | Dependencies | State |\n|---|---|---|\n'+'\n'.join('|'+n+'|'+','.join(deps[n])+'|retained; fresh distinct source/body review pending|' for n in headers)
scope='Allowed edits after source-reviewed stabilization: source-qualified comments in these four modules, task-local evidence/contracts and scoped shared Book/contributor mapping. No public header/definition/body change; new target requires new version/review. Preserve accepted OGD/FTL inputs and raw-reader bindings via explicit preedit snapshots if shared readers change. Global SGB untouched; no chapter/Goal/main/live completion.'
write('tasks/'+task+'.md','# Four-module convex analysis migration\n\n'+intent+'\n\n'+table+'\n\n'+scope)
write('conversion-windows/'+task+'.md','# Convex conversion window v1\n\n'+intent+'\n\nMap Rd into finite-dimensional Euclidean real instances of the same abstract spaces; domain f<top includes bottom, real heights, noBottom only where printed. Source weighted sum maps to named upperAdd with explicit convention delta. Strict weights in Def2.2/Thm2.4; arbitrary nonnegative weights including zero in closure.\n\n'+table+'\n\n'+scope)
write('proof-obligations/'+task+'.md','# Required retained convex endpoints\n\n'+table+'\n\n'+scope+'\n\nAll22 native fences/source review/body review/public canaries/axioms/root/Tests/full harness/shared graph/shadow/registry/site/contributor/PR gates separately required. Actual22 proofs are not22 original numbered results. Other Chapter2 obligations remain mandatory.')
write(run/'proof-obligations-v1.json',dict(stage='draft',required=[dict(name=n,statement_hash=frozen[n],dependencies=deps[n],state='fresh-source-review-pending') for n in headers],
    terminals=['theorem_2_4','example_2_5','example_2_6','convex_comp_affine','convex_iSup','convex_comp_monotone','convex_nonneg_linear_combination'],
    edit_scope=scope,package_accepted=False,chapter_accepted=False,goal_complete=False))
write(run/'00_context.md','Real whole Chapters1-16 Goal active/no budget. Same active checkout research-online-book; branch codex/research-online-convex-migration exact stacked OPENdraft PR155 head a2728b1da2109844ffec64f594827197cd9b541b. Canonical main/originmain6847b678a73db68dee5101d6f05c2453c1405afc clean after fresh fetch. Scope four retained convex modules22proofs/five definitions, zero new proof/registry count; not chapter acceptance. Preserve sharedGit/.lake/other tasks/accepted historical artifacts. No merge/deploy/retirement.')
write(run/'10_upper_director-v1.md','Select only retained dependency-ready convex definitions/examples/closure foundations. Single lower reuse route; distinguish general extended epigraphs, noBottom characterization, real composition and explicitly interpreted upper addition. Distinct blind/source roles required by local skill; no mathematical progress by declaration count, no wholeChapter acceptance/model escalation.')
write(run/'20_architect-v1.md',intent+'\n\n'+table+'\n\n'+scope)
gate('actual-declaration-retrieval',sys.executable,'-X','utf8','tools/bandit.py','list-lean-decls','--include-tests','--statement','OnlineConvex.')
gate('draft-lifecycle',sys.executable,'-X','utf8','tools/bandit.py','lifecycle-event','--session',task,'--event','draft','--payload-json',json.dumps(dict(run_id=run.name,retained_proofs=22,definitions=5,new_proofs=0,source_accepted=False,chapter_complete=False,goal_complete=False)))
print('Draft frozen:22 actual native headers/five definitions/four modules, source/convention/DAG/window and neutral packet; distinct source review pending.')
