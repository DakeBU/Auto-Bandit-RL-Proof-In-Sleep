"""Freeze the retained causal FTL producer for a fresh distinct semantic migration."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
from pypdf import PdfReader
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header
run=Path(__file__).parent;task='ONLINE-FTL-MIGRATION-20261005'
contract=Path('docs/contracts/online-ftl-migration-v1')
assert not (run/'draft-freeze-v1.json').exists()
assert not any(p.is_file() for p in contract.rglob('*'))
contract.mkdir(exist_ok=True)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(p,x):
    p=Path(p);p.parent.mkdir(parents=True,exist_ok=True)
    with p.open('w',encoding='utf-8',newline='\n') as f:
        if isinstance(x,str):f.write(x+'\n')
        else:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
def gate(label,*args):subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),label,*args],check=True)
source=Path('../research-online-ogd/tmp/pdfs/orabona-v10.pdf')
assert sha(source)=='cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17'
pdf=PdfReader(source);text=pdf.pages[23].extract_text()
write(run/'source-printed12-pdf24.txt',text)
module=Path('BanditRLProof/OnlineFTLFailure.lean');raw=module.read_bytes();body=raw.decode('utf-8')
(run/'original-public-module.lean.txt').write_bytes(raw)
assert sha(run/'original-public-module.lean.txt')==sha(module)
canary=Path('Tests/OnlineFTLFailureCanary.lean')
(run/'original-public-canary.lean.txt').write_bytes(canary.read_bytes())
names=['prefixCoefficient_eq_sum','linearFTLPredict_prefix','linearFTLPredict_mem','linearFTLPredict_minimizes',
    'failure_prefixCoefficient','failure_prediction','example_2_10']
headers={n:lean_declaration_header(module,n) for n in names}
deps={names[0]:[],names[1]:[names[0]],names[2]:[],names[3]:[names[0]],
    names[4]:[],names[5]:[names[4]],names[6]:[names[5]]}
context=body.split('theorem prefixCoefficient_eq_sum',1)[0]
write(contract/'context.lean.txt',context+'end BanditRL.OnlineLearning')
intent='''Source Orabona arXiv1912.13213v10, frozen21June2026 SHAcef4edfa...a1b17. Example2.10 printed12/PDF24:V=[-1,1], losses ell_t(x)=z_t*x. z1=-1/2; later even source rounds+1, odd source rounds-1. First prediction arbitrary feasible x1; later FTL predictions+1 on even source rounds and-1 on odd source rounds. Regret against comparator0 exactly T-1-x1/2 >= T-3/2 for T>=1.

Audit retained actual prefix statistic recursively, not an assumed stability/regret bound. Lean0 is source round1. linearFTLPredict uses exactly t past coefficients, takes feasible x0 at0 and minimizes the past linear-loss sum by the sign of prefixCoefficient; tie rule at zero chooses-1 for positive indices. The failure stream has no later zero prefix, so later source predictions do not depend on that tie rule. AtT0 all losses/prefix sums are zero; the source endpoint still deliberately requiresT>=1. Historical minimization helper has no feasible-x0 premise because at0 both sums are0; algorithm feasibility and source endpoint separately require x0 in[-1,1]. Coefficients are arbitrary real in generic helpers; only the failure witness uses specified values. Comparator0 is the cited fixed feasible comparator, not an asserted best hindsight comparator. This is a deterministic failure of this FTL family, not an all-algorithms lower bound or stochastic theorem. Full future coefficient functions are mathematical input representations; actual recursion and strict-prefix identity establish causality.

Mathematical objects:scalar real actions/coefficient losses, finite horizon, closed interval. Quantifier order:fix arbitrary coefficient sequence/initial action, prove outputs for everyt; fix specified witness and every feasibleinitial, everyT>=1. Assumptions:membership only where needed; no probability/integrability/gradient/compactness oracle premise. Conclusion:exact loss/regret identity AND uniform linear lower bound. Constants/index:T-1-x0/2, worst feasiblex0<=1 givesT-3/2; Leanodd positiveindex is sourceeven. Information:output before current coefficient, past prefix only. Boundary:no convergence/no universal adversarial lower bound; original three definitions/seven theorem bodies retained, existing two nondegenerate public canaries reused. This is independent migration of one historical production path, not seven new proofs or wholeChapter2 acceptance. Existing prior same-model semantic judgment stays historical, never relabelled independent.'''
write(contract/'source-intent.md',intent)
assumptions={names[0]:[],names[1]:['(h : ∀ i < t, z i = w i)'],
    names[2]:['(hx0 : x0 ∈ Icc (-1 : ℝ) 1)'],names[3]:['(hu : u ∈ Icc (-1 : ℝ) 1)'],
    names[4]:['(ht : 0 < t)'],names[5]:['(ht : 0 < t)'],
    names[6]:['(hx0 : x0 ∈ Icc (-1 : ℝ) 1)','(hT : 0 < T)']}
freeze={}
for n,h in headers.items():
    digest=hashlib.sha256(h.encode('utf-8')).hexdigest();freeze[n]=digest
    write(contract/(n+'-header.txt'),h)
    write(contract/(n+'.json'),dict(version=1,name='BanditRL.OnlineLearning.'+n,statement=h,statement_hash=digest,
        source_assumptions=assumptions[n],dependencies=deps[n],file=module.as_posix(),classification='reuse-existing-public-proof',
        evidence_permission='Existing compilation is not independent source acceptance; fresh blind/source/body/current integrated gates required.'))
    args=[sys.executable,'-X','utf8','tools/bandit.py','statement-fence','--declaration','BanditRL.OnlineLearning.'+n,
        '--file',module.as_posix(),'--output',str(run/('native-fences/'+n+'.json'))]
    for a in assumptions[n]:args+=['--source-assumption',a]
    gate('fence-'+n,*args)
    assert json.loads((run/('native-fences/'+n+'.json')).read_text(encoding='utf-8'))['statement_hash']==digest
neutral='import Mathlib.Data.Real.Basic\nimport Mathlib.Algebra.Order.BigOperators.Group.Finset\n\nnoncomputable section\nopen Set Finset\nnamespace Neutral\n\n'
defs=context.split('namespace BanditRL.OnlineLearning',1)[1]
mapping={'prefixCoefficient':'Q0','linearFTLPredict':'Q1','failureCoefficient':'Q2'}
def rename(s):
    for a,b in mapping.items():s=re.sub(r'\b'+a+r'\b',b,s)
    return s
neutral+=rename(defs)+'\n'
for i,n in enumerate(names,1):neutral+=rename(headers[n].replace('theorem '+n,'theorem M'+str(i).zfill(2),1))+'\n\n'
neutral+='end Neutral\n'
write(run/'blind-packet-v1.md','Fresh restricted-input reconstruction, requested GPT-6 Astra / medium. Read ONLY this mathematical packet in this pass. No source identity, public theorem-name map, prior verdict, proof bodies, compile logs or other files. Definitions are algorithm context, not proof bodies. Reconstruct Q0-Q2 and M01-M07 in seven semantic slots:objects,quantifiers,assumptions,conclusions,constants/index,information/probability,boundary. This is retained typed statement text with proof bodies omitted; do not claim source acceptance or new compilation. Write only blind-reconstruction-v1.md and blind-receipt-v1.json beside this packet, including exact raw input/report hashes, actor/requested medium, prior unrelated actor history not erased, sole input this pass, no human/external review.\n\n```lean\n'+neutral+'```')
write(run/'draft-freeze-v1.json',dict(stage='draft',headers=freeze,source_pdf_sha256=sha(source),
    source_intent_sha256=sha(contract/'source-intent.md'),context_sha256=sha(contract/'context.lean.txt'),
    original_public_module_sha256=sha(module),original_public_canary_sha256=sha(canary),
    native_fences=7,source_target='Example2.10',old_theorems_audited=7,new_proofs=0,body_edited=False,source_accepted=False))
table='| Target | Dependencies | State |\n|---|---|---|\n'+'\n'.join('|'+n+'|'+','.join(deps[n])+'|retained compiled body; fresh independent review pending|' for n in names)
scope='Allowed edits after reviewed stabilization:source-qualified comments in OnlineFTLFailure only, task-local contracts/evidence and scoped shared Book/manifest integration. No old header/definition/body rewrite; any semantic target change needs a new version/review. Same Lean/Lake project/registry; no per-book project/globalSGB overwrite. Whole Goal remains active; Chapter2 and other20main migration paths remain mandatory after this single-file scope is accepted.'
write('tasks/'+task+'.md','# Actual causal FTL source migration\n\n'+intent+'\n\n'+table+'\n\n'+scope)
write('conversion-windows/'+task+'.md','# FTL conversion window v1\n\n'+intent+'\n\nSource1-based t+1 = Lean t; x1=x0, zt=failureCoefficient(t-1); sourceT matches LeanT. Comparator0, exact initial term and T>=1 unchanged.\n\n'+table+'\n\n'+scope)
write('proof-obligations/'+task+'.md','# FTL retained producer obligations\n\n'+table+'\n\n'+scope+'\n\nFresh neutral decoder/source-contract/body review; native public guards/lookup/canary/axioms, root/Tests/fullharness, actualgraph/sharedregistry/source reader/site and exact stacked contributor/PR gates required. Failure classes follow actual harness; no old same-model review becomes independent retroactively.')
write(run/'proof-obligations-v1.json',dict(stage='draft',required=[dict(name=n,statement_hash=freeze[n],dependencies=deps[n],state='fresh-source-review-pending') for n in names],
    terminal='BanditRL.OnlineLearning.example_2_10',edit_scope=scope,package_accepted=False,chapter_accepted=False,goal_complete=False))
write(run/'00_context.md','Persistent real Orabona Chapters1-16 Goal ACTIVE, no budget. Newbranch codex/research-online-ftl-migration stacked on OPENdraft PR154 exact4b55f5ebebb370ebe9e173b9bf5155b97a2e3998. Same active research-online-book worktree/sharedGit/.lake/registry. Current leaf:independent production migration of actual causal Example2.10, seven existing bodies/three definitions, not seven new proofs. Sourceprinted12/PDF24 exactv10. Preserve historical same-model reviews and wholebook/Chapter2 boundaries; no merge/deploy/main/live/retirement/Goalcompletion.')
write(run/'10_upper_director-v1.md','Select only the dependency-ready retained scalar FTL producer package. Audit actual recursive prefix, genuine minimization and exact specified-stream regret; one lower reuse route. No algorithm existence with future-informed output, no assumed desired regret/stability, no chapter progression or model escalation. Fresh three distinct automated roles required; actor runtime model not independently attested.')
write(run/'20_architect-v1.md',intent+'\n\n'+table+'\n\n'+scope)
gate('actual-declaration-retrieval',sys.executable,'-X','utf8','tools/bandit.py','list-lean-decls','--include-tests','--statement','OnlineLearning.example_2_10')
gate('draft-lifecycle',sys.executable,'-X','utf8','tools/bandit.py','lifecycle-event','--session',task,'--event','draft',
    '--payload-json',json.dumps(dict(run_id=run.name,scope='retained causal FTL Example2.10 only',old_theorems=7,new_proofs=0,source_accepted=False,chapter_complete=False,goal_complete=False)))
print('Retained actual FTL seven targets frozen with native hashes,source intent,DAG,conversion and neutral packet; independent review pending.')
