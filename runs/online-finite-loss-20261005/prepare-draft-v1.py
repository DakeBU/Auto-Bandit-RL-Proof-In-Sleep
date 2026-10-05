"""Freeze source finite-loss criterion and its distinct noBottom domain helper."""
from pathlib import Path
import hashlib,json,subprocess,sys
from pypdf import PdfReader
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header
run=Path(__file__).parent;contract=Path('docs/contracts/online-finite-loss-v1');task='ONLINE-FINITE-LOSS-20261005'
assert not (run/'draft-freeze-v1.json').exists();contract.mkdir(exist_ok=False)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(p,x):
    p=Path(p);p.parent.mkdir(parents=True,exist_ok=True)
    with p.open('w',encoding='utf-8',newline='\n') as f:
        if isinstance(x,str):f.write(x.rstrip('\n')+'\n')
        else:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
def gate(label,*args):subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),label,*args],check=True)
source=Path('../research-online-ogd/tmp/pdfs/orabona-v10.pdf');assert sha(source)=='cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17'
pdf=PdfReader(source);write(run/'source-printed9-10-pdf21-22.txt','\n'.join(pdf.pages[i].extract_text() for i in [20,21]))
headers={
'finite_add_indicator_iff':'theorem finite_add_indicator_iff {E : Type*} (f : E → EReal) (V : Set E) (x : E) :\n    (∃ r : ℝ, f x + extendedIndicator V x = (r : EReal)) ↔\n      x ∈ V ∧ ∃ r : ℝ, f x = (r : EReal)',
'effectiveDomain_add_indicator':'theorem effectiveDomain_add_indicator {E : Type*} (f : E → EReal)\n    (hbot : ∀ x, f x ≠ ⊥) (V : Set E) :\n    effectiveDomain (fun x => f x + extendedIndicator V x) = effectiveDomain f ∩ V'}
probe='import BanditRLProof.OnlineConvexExtended\n\nnoncomputable section\nopen Set\nnamespace BanditRL.OnlineConvex\n\n'+''.join(h+' := by\n\n' for h in headers.values())+'end BanditRL.OnlineConvex\n'
p=run/'leaves/draft-statement-v1.lean';write(p,probe)
intent='''Source Orabona arXiv1912.13213v10 (21 June2026), printed9-10/PDF21-22. After defining the zero-on-V/top-outside constraint indicator, the main text says that finite loss after adding it requires prediction in V. This previously omitted mandatory consequence was identified by the distinct convex package reviewer; it is not accepted by the prior22 endpoints.

Primary exact criterion: a constrained value equals some FINITE REAL r iff x is in V AND the original value equals some finite real r. Membership alone does not suffice: f can be top at feasible x. This iff is an explicitly proved algebraic refinement of the source's stated necessary direction and indicator definition, not a new printed numbered theorem. General extended-real f may attain either infinity; no noBottom hypothesis is needed for this finite-existence predicate. With ordinary bottom-dominant EReal +, bottom+top is bottom, which is STILL NOT finite. Do not confuse f<top with finite when bottom is allowed. Empty V, top/bottom functions, nonconstant finite functions and arbitrary carriers included. Source Euclidean setting is a specialization; no vector, topology, convexity, nonempty or probability assumption needed for this pointwise algebra.

Separate supporting domain identity: effectiveDomain(f+indicator V)=effectiveDomain(f) intersect V under GLOBAL noBottom f. Effective domain is the shared f<top definition and generally includes bottom. Here noBottom is necessary for the ordinary-addition domain identity: bottom outside V leaks into the f<top domain because bottom+top=bottom. Preserve that exact hypothesis rather than silently changing domain definition or addition convention. Source's later noBottom convex indicator-addition regime supports this helper; convexity of f/V is not needed for the algebra. This is not the general convex upperAdd closure, and no operation convention is switched. Two finite witnesses on the primary iff need not be assumed equal in the statement; actual zero-on-V identity makes the values equal.

Reuse existing effectiveDomain/extendedIndicator in the same shared Lean project/registry. Primary terminal is finite_add_indicator_iff; effectiveDomain_add_indicator is separately hypothesized foundation growth. No desired-domain/finite-loss premise is assumed. Source and actual typed headers/scoped context/native fingerprints/DAG/window must be reviewed before actual proof. Private draft probe intentionally has two unproved bodies, never public root/compiled proof acceptance. Two new proofs are planned, not yet present. Whole Goal active, finite-loss group/Chapter2 not accepted; earlier accepted OGD/FTL/convex contracts immutable. Future standalone problems optional/main formal results mandatory; Chapter2 totalnull and Chapters3-16 unenumerated mandatory.'''
write(contract/'source-intent.md',intent)
write(contract/'source-card.json',dict(kind='unnumbered-main-text-consequence',primary=dict(path=str(source),sha256=sha(source),url='https://arxiv.org/pdf/1912.13213v10',printed_pages=[9,10],pdf_pages=[21,22]),
    source_conclusion='Finite constrained loss requires x in V.',Lean_refinement='Exact iff additionally requires finite original f(x); separate noBottom effective-domain identity.',
    gap_detection='runs/online-convex-migration-20261005/finite-loss-constraint-gap-v1.json',printed_number=None,required_main_text=True))
context='import Mathlib.Data.EReal.Basic\nnoncomputable section\nopen Set\nnamespace Neutral\n\ndef Q0 {E : Type*} (f : E → EReal) : Set E := {x | f x < ⊤}\n\ndef Q1 {E : Type*} (V : Set E) (x : E) : EReal := by\n  classical\n  exact if x ∈ V then 0 else ⊤\n'
write(contract/'context.lean.txt','import BanditRLProof.OnlineConvexExtended\nnoncomputable section\nopen Set\nnamespace BanditRL.OnlineConvex\n-- Existing shared effectiveDomain/extendedIndicator; exact actual signatures in actual-prerequisite-types-v1-01.log.\nend BanditRL.OnlineConvex')
hashes={}
for n,h in headers.items():
    actual=lean_declaration_header(p,n);digest=hashlib.sha256(actual.encode('utf-8')).hexdigest();hashes[n]=digest
    assumptions=['(hbot : ∀ x, f x ≠ ⊥)'] if n=='effectiveDomain_add_indicator' else []
    write(contract/(n+'-header.txt'),actual)
    write(contract/(n+'.json'),dict(version=1,name='BanditRL.OnlineConvex.'+n,statement=actual,statement_hash=digest,source_assumptions=assumptions,
        dependencies=['BanditRL.OnlineConvex.effectiveDomain','BanditRL.OnlineConvex.extendedIndicator'] if assumptions else ['BanditRL.OnlineConvex.extendedIndicator'],
        public_file='BanditRLProof/OnlineConstraintFiniteLoss.lean',draft_file=p.as_posix(),classification='new-shared-explicit-source-refinement',
        evidence_permission='draft unproved-body typing is not compiled; distinct contract/proof/body/reader/integrated gates required'))
    args=[sys.executable,'-X','utf8','tools/bandit.py','statement-fence','--declaration','BanditRL.OnlineConvex.'+n,'--file',p.as_posix(),'--output',str(run/('native-draft-fences/'+n+'.json'))]
    for a in assumptions:args+=['--source-assumption',a]
    gate('draft-fence-'+n,*args)
    assert json.loads((run/('native-draft-fences/'+n+'.json')).read_text(encoding='utf-8'))['statement_hash']==digest
neutral=context+'\n'
for i,(n,h) in enumerate(headers.items(),1):neutral+=h.replace('theorem '+n,'theorem M'+str(i).zfill(2),1).replace('effectiveDomain','Q0').replace('extendedIndicator','Q1')+'\n\n'
neutral+='end Neutral\n'
write(run/'blind-packet-v1.md','Fresh restricted-input reconstruction, requested GPT-6 Astra / medium. Read ONLY this packet this pass, no source identity/public-name map/prior verdict/proof body/other files. Two context definitions and two unproved headers. Reconstruct Q0/Q1/M01/M02 in seven slots:objects,quantifiers,assumptions,conclusion,normalization,information/probability,boundary. Compare finite-real witness existence with below-top predicate; both infinities and empty-set cases matter. Do not assume unspecified noBottom premise. Imported EReal conventions should be marked interpretations, not verified code. Write ONLY blind-reconstruction-v1.md/blind-receipt-v1.json here with raw packet/report SHA, actor/requested medium, sole input currentpass, prior history not erased, no compilation/source acceptance/human/external/runtime-attestation claim.\n\n```lean\n'+neutral+'```')
write(run/'draft-freeze-v1.json',dict(stage='draft',headers=hashes,source_pdf_sha256=sha(source),source_intent_sha256=sha(contract/'source-intent.md'),
    shared_context_module_sha256=sha('BanditRLProof/OnlineConvexExtended.lean'),private_draft_probe_sha256=sha(p),public_module_present=False,
    proposed_new_proofs=2,primary_source_terminal='finite_add_indicator_iff',supporting_terminal='effectiveDomain_add_indicator',source_accepted=False))
scope='Allowed after reviewed stabilization: new OnlineConstraintFiniteLoss module/two frozen public proofs, focused meaningful canary, public root/Tests imports, scoped task/contracts/evidence/contribution/Book mapping in shared registry. Never rewrite accepted convex/OGD/FTL inputs; any source/public header change needs new version/review. Keep global SGB untouched, whole Goal active, Chapter2 totalnull. A new source endpoint closes only this explicit finite-loss obligation, not all18 draftgroups or the chapter.'
table='| Leaf | Required context/API | Route |\n|---|---|---|\n| finite_add_indicator_iff | shared extendedIndicator; EReal finite/top/bottom arithmetic | membership cases; outside all three EReal constructors; inside exact zero identity |\n| effectiveDomain_add_indicator | shared effectiveDomain/indicator; add_top_of_ne_bot | pointwise set equality; membership cases; explicit global noBottom |'
write('tasks/'+task+'.md','# Finite constrained loss\n\n'+intent+'\n\n'+table+'\n\n'+scope)
write('conversion-windows/'+task+'.md','# Finite-loss conversion window v1\n\n'+intent+'\n\nFinite means exists finite-real equality, not f<top without noBottom. Arbitrary carrier generalizes Rd. Both endpoints use ordinary EReal+; upperAdd is not substituted.\n\n'+table+'\n\n'+scope)
write('proof-obligations/'+task+'.md','# Mandatory finite-loss endpoint and separate domain helper\n\n'+table+'\n\n'+scope+'\n\nSource/actual typing/fence/fingerprint/blind/reviewer before proof; then exact body/canary/axioms/actual graph/root/Tests/full harness/shadow/contributor/Book/clean site/reader/raw/PR gates. Both infinities/empty/finite-inside/top-inside/finite-outside and counterexample to dropping domain hbot must remain visible.')
write(run/'proof-obligations-v1.json',dict(stage='draft',required=[dict(name=n,statement_hash=hashes[n],state='source-review-pending') for n in headers],
    primary_terminal='finite_add_indicator_iff',supporting_terminal='effectiveDomain_add_indicator',new_proofs_present=0,proposed_new_proofs=2,edit_scope=scope,package_accepted=False,chapter_accepted=False,goal_complete=False))
write(run/'00_context.md','Whole Chapters1-16 real Goal active/no budget. Same isolated research-online-book checkout, branchcodex/research-online-finite-loss stacked on OPENdraft PR156 exactverified finalheadf6daaa68927398df9fd8b756f3ac2dd28247c1e7. Fresh originmain=canonicalmain6847b678a73db68dee5101d6f05c2453c1405afc clean; other worktrees/sharedGit/.lake preserved. Previous convex22 package delivered, not chapter completion. New mandatory finite-loss sentence requires exact finite witness criterion, separate noBottom domain helper. Nothing public/proved yet; two private intentional unproved-body headers only. No model upgrade/merge/deploy/retirement.')
write(run/'10_upper_director-v1.md','Select next genuinely missing main-text finite-loss endpoint detected by prior distinct reviewer. Source necessity refined to exact finite-witness iff, plus separate hypothesized domain intersection. One lower route; direct membership/EReal cases. No noBottom on finite criterion; do not silently count bottom as finite. Default dependency-ready lower leaf is finite_add_indicator_iff; supporting identity separate. Distinct semantic actors/GPT-6 Astra medium; no human/external/attested model claim.')
write(run/'20_architect-v1.md',intent+'\n\n'+table+'\n\n'+scope)
gate('actual-existing-declaration-retrieval-v1',sys.executable,'-X','utf8','tools/bandit.py','list-lean-decls','--include-tests','--statement','finite_add_indicator_iff')
gate('draft-lifecycle-v1',sys.executable,'-X','utf8','tools/bandit.py','lifecycle-event','--session',task,'--event','draft','--payload-json',json.dumps(dict(run_id=run.name,scope='mandatory finite-loss sentence and separate noBottom domain helper',proposed_new_proofs=2,new_proofs_present=0,source_accepted=False,chapter_complete=False,goal_complete=False)))
print('Two exact private typed targets/source/DAG/window/neutral packet frozen; source review and actual proofs pending.')
