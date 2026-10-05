"""Freeze existing OGD proof targets for a fresh semantic migration, without rewriting history."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header
from pypdf import PdfReader
run=Path(__file__).parent
contract=Path('docs/contracts/online-ogd-migration-v1')
contract.mkdir(parents=True,exist_ok=True)
(run/'leaves').mkdir(exist_ok=True)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(p,v):
    with Path(p).open('w',encoding='utf-8',newline='\n') as f:
        if isinstance(v,str):f.write(v+'\n')
        else:json.dump(v,f,indent=2);f.write('\n')
def clean(t):
    t=re.sub(r'/-.*?-/', '',t,flags=re.S);return re.sub(r'--[^\n]*','',t)
pdf=Path('../research-online-ogd/tmp/pdfs/orabona-v10.pdf')
assert sha(pdf)=='cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17'
extract=Path('tmp/online-ogd-migration-source-pages23-27.txt')
reader=PdfReader(str(pdf))
write(extract,'\n'.join('PDF page '+str(i+1)+'\n'+reader.pages[i].extract_text() for i in range(22,27)))
modules=[Path('BanditRLProof/OnlineGradientDescent.lean'),Path('BanditRLProof/OnlineGradientDescentVariable.lean')]
fixed,variable=[p.read_text(encoding='utf-8') for p in modules]
native={}
for p,t in zip(modules,[fixed,variable]):
    for name in re.findall(r'^theorem\s+(\w+)',t,re.M):
        header=lean_declaration_header(p,name)
        native[name]=dict(file=p.as_posix(),statement=header,statement_hash=hashlib.sha256(header.encode()).hexdigest())
assert len(native)==16
names={name:'N'+str(i+1).zfill(2) for i,name in enumerate(native)}
defs={'Domain':'Q0','project':'Q1','RegularLoss':'Q2','step':'Q3','iterate':'Q4','regret':'Q5',
      'iterateVariable':'Q6','regretVariable':'Q7'}
replacements=dict(defs,**names)
def neutral(t):
    for old,new in sorted(replacements.items(),key=lambda kv:-len(kv[0])):
        t=re.sub(r'\b'+re.escape(old)+r'\b',new,t)
    return t
context='import Mathlib.Topology.MetricSpace.Bounded\n'+clean(fixed.split('theorem project_spec',1)[0])
context=context.replace('namespace BanditRL.OnlineGradientDescent','namespace NeutralMigration')
variabledefs=clean(variable.split('theorem iterateVariable_mem',1)[0]).split('def iterateVariable',1)[1]
context+='\ndef iterateVariable'+variabledefs
context=neutral(context)
write(run/'neutral-context.lean.txt',context+'\nend NeutralMigration')
headers={names[name]:neutral(row['statement']) for name,row in native.items()}
def split_statement(header):
    rest=re.sub(r'^theorem\s+\w+\s*','',header)
    depth=0
    for i,c in enumerate(rest):
        if c in '([{':depth+=1
        elif c in ')]}':depth-=1
        elif c==':' and depth==0:return rest[:i].strip(),rest[i+1:].strip()
    raise AssertionError(header)
probe=context+'\n'
for name,header in headers.items():
    binders,result=split_statement(header)
    probe+='def '+name+'Type : Prop := '+('∀ '+binders+', ' if binders else '')+result+'\n'
    probe+='#check @'+name+'Type\n'
probe+='end NeutralMigration\n'
write(run/'leaves/neutral-types-v1.lean',probe)
packet=('Reconstruct each of the sixteen unproved statement headers N01-N16 in seven slots, '
        'including mathematical objects, quantifiers, assumptions, conclusion/metric, constants/indexing, '
        'information order and excluded regimes. This pass may read only this packet. Do not read source '
        'identity, name maps, proof bodies, compile logs or prior judgments. Do not infer acceptance. '
        'Give natural-language and mathematical reconstruction per target.\n\nScoped context:\n```lean\n'+
        context+'\n```\n\nUnproved headers (no theorem bodies):\n```lean\n'+
        '\n\n'.join(headers.values())+'\nend NeutralMigration\n```')
write(run/'blind-packet-v1.md',packet)
write(run/'private-neutral-name-map.json',dict(definitions=defs,targets=names))
write(contract/'native-headers-v1.json',native)
write(contract/'context-v1.json',dict(modules=[dict(path=p.as_posix(),sha256=sha(p)) for p in modules],
    source_pdf=dict(path=pdf.as_posix(),sha256=sha(pdf)),
    ignored_source_extract=dict(path=extract.as_posix(),sha256=sha(extract),physical_pages=list(range(23,28))),
    actual_definitions=[dict(name=n,neutral=q) for n,q in defs.items()],
    proof_bodies_exist_before_this_audit=True,new_proofs_claimed=0))
write(run/'source-card.md',
    'Orabona arXiv:1912.13213v10, 21 June2026, fixed SHA cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17. '
    'Algorithm2.1 and Prop2.11 printed12/PDF24; Lemma2.12/Theorem2.13 printed13/PDF25, accumulation printed14/PDF26; '
    'Eq2.1 printed15/PDF27; Theorem2.7 supporting-gradient prerequisite printed11/PDF23. '
    'Projection exists in nonempty closed convex V and decreases distance to a feasible point. Lemma preserves '
    'both eta-scaled loss-to-inner-product and quadratic-potential inequalities for actual projected update. '
    'Fixed positive eta terminal retains initial-distance term and negative terminal residual, allowing unbounded V. '
    'Positive adjacent nonincreasing schedule uses finite diameter and final eta_T; exact source diameter differs '
    'from a supplied upper bound. T>=1 precedes predecessor indexing. Eq2.1 horizon-tuned constant eta uses '
    'a priori diameter/gradient bounds and the same actual tuned trajectory; source symbol L corresponds to Lean G. '
    'Do not certify the later scalar eta-dependent-gradient minimizer as an implementable learner. '
    'Source losses are convex and differentiable on an open neighborhood containing V. Existing RegularLoss '
    'explicitly stores IsOpen U, V subset U, ConvexOn U f and DifferentiableOn U f; ConvexOn also entails convex U. '
    'Fresh review must check that regularity implication rather than assume theorem numbers match. '
    'Real-valued functions on E and a complete real Hilbert space are the current abstraction; review any '
    'source-to-abstraction scope issue explicitly. Existing proof bodies/old contracts remain untouched. '
    'This migration is not new mathematics or chapter/book acceptance; any missing source-premise adapter stays required.')
write(run/'00_context.md',
    'Persistent real whole-book Goal ACTIVE, no budget. Branch codex/research-online-ogd-migration stacked on '
    'OPENdraft PR153 exact64e25407a4a2b952fa4597d6c2cffc8df16810e8, canonical main6847b678 clean after fetch. '
    'Same active research-online-book worktree, shared Git/.lake and underlying Lean registry. Audit two of '
    'the historical26 production paths: existing fixed/variable OGD modules, sixteen theorem bodies/eight '
    'definitions or structure, not a new proof count. Reconcile Prop2.11/Lemma2.12 source inventory only '
    'after distinct semantic review. Historical same-model reviews cannot become independent retroactively. '
    'Default one lower reuse route; root formalizer, existing required distinct normal_blind/source_reviewer '
    'Astra/medium, no model escalation/externalhumanclaim. No old contract/proof/header/generated_site/'
    'anonymous/privatepaper changes. FullChapter2 enumeration/remaining24 historical paths and any source '
    'regularity repair remain mandatory. No merge/deploy/main/live/retirement/Goalcompletion.')
write(run/'10_upper_director.md',
    'Current chapter dependency frontier requires exact old OGD semantic/contribution migration. Freeze '
    'actual16 existing headers/context and original v10 before blind review. Projection producer is the '
    'first dependency-ready audit leaf; actual bodies already exist, so no new theorem productivity claim. '
    'Do not change old statements to hide a mismatch. If source premises do not entail RegularLoss, '
    'record repair and freeze a separately versioned adapter that reuses the same recurrence. '
    'Source inventory/chapter2 accepted state remains pending.')
write(run/'20_middle_architect.md',
    'DAG: shared mathlib projection existence/variational characterization -> projection decrease; '
    'convex gradient supporting bound -> actual one-step -> actual fixed recursion/sum/negative endpoint '
    '-> positive D/G/T tuning. Variable actual recursion feasibility and strict-prefix causality -> '
    'existing one-step -> weighted potential -> upper-bound diameter -> exact bounded Metric.diam. '
    'Source eta_T=Lean eta(T-1), x_(T+1)=iterateVariable T. Fixed T0 allowed, variable T>=1. '
    'Audit actual public producer bodies; accepting one-step consumers would not suffice. '
    'Allowed edit boundary currently new migration contract/run/task only; old Lean bodies/header hashes '
    'and historical contracts are fixed. Any correction needs a new reviewed version and separate scope. '
    'Known reusable API OnlineConvex.convex_gradient_lower_bound accepts ConvexOn V plus DifferentiableAt '
    'at current point, without an open convex-neighborhood premise; inspect actual type before using.')
write(run/'proof-obligations.json',dict(stage='draft',scope='current old OGD semantic migration',
    required=[dict(name=n,state='existing-compiled-unreviewed-this-pass',**row) for n,row in native.items()],
    chapter_complete=False,book_complete=False,goal_complete=False,new_proofs=0,
    mandatory_remaining=['neutral typed reconstruction','source contract/body review',
        'any source-premise repair','current focused/publiccanary/axioms/combined/graph/Book gates',
        'contribution migration','remaining historical24 paths and full chapter enumeration']))
write(run/'predecessor-delivery.json',dict(pr=153,url='https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/pull/153',
    exact_head='64e25407a4a2b952fa4597d6c2cffc8df16810e8',state='OPEN',draft=True,merged=False,
    accepted_payload='9ecc0841761fa62d7cf25271777df4de502a327e',reader_source_commit='70c63cac7efa59d2a892b563d8affee4266be610',
    proof_count=22,canary_count=30,unit_package_accepted=True,chapter2_accepted=False,book_accepted=False,
    worktree_retained=True,ignored_pdf_graph_site_browser_artifacts_preserved=True))
print(json.dumps(dict(status='migration-draft-frozen',targets=len(native),old_bodies_unchanged=True,new_proofs=0)))
