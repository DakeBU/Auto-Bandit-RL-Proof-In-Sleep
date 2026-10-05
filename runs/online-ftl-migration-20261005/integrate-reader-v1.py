"""Integrate reviewed retained FTL semantics without changing any Lean code token."""
from pathlib import Path
import hashlib,json,re,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header,_strip_lean_comments
run=Path(__file__).parent
def load(p):return json.loads(Path(p).read_text(encoding='utf-8'))
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(p,x):
    with Path(p).open('w',encoding='utf-8',newline='\n') as f:
        if isinstance(x,str):f.write(x+'\n')
        else:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
receipt=load(run/'public-body-receipt-v1.json')
assert receipt['actor']['task']=='/root/source_reviewer'
assert receipt['verdict']=='accepted-with-explicit-delta' and not receipt['mathematical_repairs']
assert sha(receipt['report'])==receipt['report_sha256']
rows={r['path']:r['sha256'] for r in receipt['reviewed_files']}
assert len(rows)==159
for p,h in rows.items():
    if p=='BanditRLProof/OnlineFTLFailure.lean':
        assert sha(run/'original-public-module.lean.txt')==h
    else:assert sha(p)==h,p
assert all(v=='accepted-with-explicit-delta' for v in receipt['target_verdicts'].values())
write(run/'body-binding-audit-v1.json',dict(status='passed',raw_rows=159,report_sha256=receipt['report_sha256'],
    actual_bodies=7,actual_canaries=2,new_proofs=0,required_reader_repairs=receipt['required_repairs']))
paths=['BanditRLProof/OnlineFTLFailure.lean','website/content/readings.json','website/content/highlights.json','website/content/chapters.json']
snapshots=[]
for p in paths:
    snapshot=run/'leaves'/('pre-integration-'+p.replace('/','--')+'.txt')
    if snapshot.exists():
        assert sha(snapshot)==rows[p],p
    else:snapshot.write_bytes(Path(p).read_bytes())
    snapshots.append(dict(path=p,snapshot=snapshot.as_posix(),raw_sha256=sha(snapshot),
        authorized_delta='source-qualification comments only' if p.endswith('.lean') else 'only online-ftl-failure reader metadata'))
write(run/'historical-raw-supersession-v1.json',dict(status='exact originals preserved before source-qualified integration',rows=snapshots,
    prior_OGD_receipts_not_rewritten=True,original_FTL_contract_and_body_receipts_not_rewritten=True))
module=Path(paths[0]);before=(run/'original-public-module.lean.txt').read_bytes()
token=lambda x:re.sub(r'\s+',' ',_strip_lean_comments(x)).strip()
assert token(before.decode('utf-8'))==token(module.read_text(encoding='utf-8'))
comment='''/-
Source: Orabona, Online Learning, arXiv:1912.13213v10, Example 2.10,
printed p.12 / PDF p.24. This retained implementation uses zero-based time:
Lean 0 is source round 1. The exceptional first coefficient is -1/2; later
Lean odd/even coefficients are +1 and -1. Every feasible initial x0 is allowed.

prefixCoefficient and linearFTLPredict are actual recursive-past definitions.
The prefix theorem proves causality for a fixed x0. Generic positive-time
zero-prefix ties select -1, a permitted concrete FTL selection; the source
failure stream has no such ties. The historical objective inequality alone
does not require feasible x0 at time 0 because both objectives are empty.
Combine linearFTLPredict_mem with linearFTLPredict_minimizes for feasible FTL.

example_2_10 proves the actual played-loss regret against comparator 0, exactly
T - 1 - x0/2 and at least T - 3/2, for T >= 1. It is a counterexample for this
FTL family, not a lower bound for every online algorithm. The six helpers and
three definitions are library refinements of one printed example. This
migration preserves all existing definition, statement and proof code.
-/
'''
module.write_bytes(comment.replace('\n','\r\n').encode('utf-8')+before)
assert token(before.decode('utf-8'))==token(module.read_text(encoding='utf-8'))
freeze=load(run/'draft-freeze-v1.json')
for n,h in freeze['headers'].items():assert hashlib.sha256(lean_declaration_header(module,n).encode()).hexdigest()==h,n
p=Path(paths[1]);data=load(p);r=next(x for x in data['readings'] if x['slug']=='online-ftl-failure')
r['notation'][0]['meaning']='S_t is the sum of precisely Lean indices i<t; current and future coefficients are not read.'
r['notation'][1]['meaning']='A fixed input x0 in [-1,1], corresponding to source x1. Prefix causality compares streams with this same input.'
r['algorithm']['steps'][1]['detail']='At Lean time0 output feasible x0. At positive times choose1 if S_t<0 and -1 otherwise; zero-prefix ties choose -1. The source witness has S_t=+/-1/2 at every positive time.'
s=r['source_theorems'][0]
s['relationship']='The actual recursion is proved causal for fixed x0. Combine the membership and prefix-objective inequality for a feasible FTL selection, including time0. The later source witness has no ties; the exact played-loss regret and its lower bound are derived, not assumed. Six helpers and three definitions refine this one printed example.'
s['contract']['assumptions']='Fixed x1 in [-1,1], T>=1. Source z1=-1/2, z_t=+1 on even t and -1 on odd t>1. Lean time0 corresponds to source round1; positive-time generic zero-prefix ties choose -1.'
s['contract']['regret']='Deterministic actual played-loss regret against the fixed feasible comparator0; no expectation or optimal-hindsight-comparator equality.'
s['local_status']['boundary']='Example2.10 and its retained structural helpers only. Concrete generic tie selection and fixed-initial-input causality; no all-algorithm lower bound. Fresh integrated/package gates are recorded separately; Chapter2 and the whole book remain incomplete.'
r['worked_example']['boundary']='The canary evaluates a nonzero initial value1/3 and uses the actual producer theorem for29/6. This FTL counterexample is not a lower bound against every online algorithm; T0 is excluded from the source identity.'
write(p,data)
p=Path(paths[2]);data=load(p)
for n in data['nodes'] if 'nodes' in data else data['highlights']:
    if n.get('chapter')!='online-ftl-failure':continue
    name=n['full_name'].rsplit('.',1)[-1]
    if name=='linearFTLPredict_prefix':
        n['math']=r'\((\forall i<t,\ z_i=w_i)\Longrightarrow x_t(z,x_0)=x_t(w,x_0)\)'
        n['lean_notes']='Generic coefficient streams and any fixed real initial x0; strict-prefix equality excludes the current coefficient. This causality theorem alone does not assert feasibility or restrict an external initialization procedure.'
    elif name=='linearFTLPredict_minimizes':
        n['math']=r'\(\sum_{i<t}z_i x_t\le\sum_{i<t}z_i u,\qquad u\in[-1,1]\)'
        n['plain']='The selected action has no larger historical objective than any feasible comparator.'
        n['lean_notes']='The inequality permits any real x0: at time0 both sums vanish. Combine linearFTLPredict_mem with feasible x0 in[-1,1] to obtain an actual feasible argmin. Later zero-prefix ties use -1; the source failure witness has none.'
    elif name=='example_2_10':
        n['lean_notes']='Every feasible x0 and T>=1; comparator0 is fixed and feasible. Equality and lower bound use actual played losses, with initial loss -x0/2. Lean0 is source1. No T0 formula or lower bound against all algorithms.'
write(p,data)
p=Path(paths[3]);data=load(p);c=next(x for x in data['chapters'] if x['slug']=='online-ftl-failure')
c['completion_definition']='One source Example2.10: retained actual prefix recursion, fixed-initial-input causality, feasibility plus historical minimization, exact comparator0 regret for T>=1. Seven existing proofs are reused; no new theorem bodies, full Chapter2 completion or main/live update.'
write(p,data)
names=['BanditRL.OnlineLearning.'+n for n in ['prefixCoefficient','linearFTLPredict','failureCoefficient']+list(freeze['headers'])]
contract=load('research-wiki/contribution-contracts/ONLINE-OGD-MIGRATION-20261005.json')
contract.update(id='ONLINE-FTL-MIGRATION-20261005',frontier_cell='online-ftl-failure',
    source=dict(kind='book',title='Online Learning: A Modern Introduction Using Convex Optimization',
        version='arXiv:1912.13213v10,21 June2026; SHA256 '+freeze['source_pdf_sha256'],
        anchor='Section2.1.2 Example2.10; printed12/PDF24',url='https://arxiv.org/pdf/1912.13213v10'),
    target='Independently revalidate retained causal FTL implementation and exact source counterexample; qualify source/initialization/tie/minimization boundaries without changing proof code.',
    affected_files=paths,declarations=names,
    reuse_plan=dict(classification='reuse',decision='reuse_existing',searched_existing=['Native actual public declarations and actual compiled shared graph10 scope nodes/six required value pairs.'],
        reused_declarations=names,new_shared_declarations=[],known_consumers=['Tests.OnlineFTLFailure.six_rounds','Tests.OnlineFTLFailure.actual_predictions'],
        planned_consumers=['Complete Chapter2 source and historical production audits.'],no_duplicate_wrapper=True,
        decision_reason='Reuse the same seven proof bodies/three definitions, zero new nodes and no duplicate per-book library.'),
    semantic_roundtrip=dict(required=True,status='accepted',formalizer='/root',blind_decoder='/root/normal_blind',source_reviewer='/root/source_reviewer',
        verdict='accepted-with-explicit-delta',remaining_semantic_delta='Distinct source-contract and actual-body reviews accepted. Fixed x0, zero-based indices and concrete generic tie selection explicit; initial feasibility separate from minimization. Final reader/package review pending; no human/external review.'),
    graph_contribution=dict(lean_graph='reuse-only',overview_graph='updated',functor_hypergraph='none-found-with-reason',functor_reason='Retained FTL source counterexample, no functor claim.',
        focus_targets=names,visual_review='Reused actual compiled graph with10 unchanged FTL nodes and six required value pairs; shared registry/site final checks pending.',edge_semantics='formal-solid; overlays-dashed'),
    progress_updates=dict(teaching_route='updated: same three old FTL reader nodes and URLs, with causality and feasible-minimization formulas corrected.',
        banditrlwiki='no-change-with-reason: no new Bandit setting.',results_ledger='no-change-with-reason: additive task acceptance overlay follows gates; historical source inventory untouched.',
        roadmap='no-change-with-reason: whole-book Goal remains active, Chapter2 incomplete and global SGB untouched.',website_surfaces=paths[1:]),
    truth_boundary='One retained source FTL example, seven existing proofs/three definitions and no new proof code. Zero-based indexing; feasible fixed initial input; concrete generic -1 tie choice; source witness later prefixes neverzero. Historical minimization inequality alone has no initial feasibility premise, supplied separately for algorithm interpretation. Exact deterministic comparator0 regret T-1-x0/2 >=T-3/2 for T>=1, not optimal-comparator equality/all-algorithm lower bound/randomized-law theorem. Remaining historical production audits/full Chapter2 source contract and Chapters3-16 mandatory. Local compilation/stacked draftPR do not update main/live.',
    verification=dict(focused_checks=['Fresh actual retained-body elaboration, two public nondegenerate canaries,12 exact named #check/#print axioms standard3-or-none, seven actual native safe guards.'],
        bandit_check='Fresh combined root/Tests/full harness pending.',site_build='lean-verified only after applicable fresh combined gate; generated_site untouched.',
        site_check='Clean registry/site/reader acceptance pending.',independent_review='Three distinct required automated actors, requested GPT-6 Astra/medium; no human/external review or independently attested runtime model.'))
write('research-wiki/contribution-contracts/ONLINE-FTL-MIGRATION-20261005.json',contract)
write(run/'public-integration-v1.json',dict(stage='reader-repair-integrated-for-final-review',unchanged_headers=7,all_lean_code_tokens_unchanged=True,
    existing_definitions=3,existing_proofs=7,new_proofs=0,new_registry_nodes=0,old_three_highlights_retained=True,
    reader_repairs=receipt['required_repairs'],source_body_receipts_unchanged=True,
    raw_supersession=str(run/'historical-raw-supersession-v1.json'),public_module_sha256=sha(module),
    actual_failed_integration='First comment contained nested-comment opener in sign shorthand; unchanged-code assertion rejected before public build. Exact failed module/script retained, corrected prose preserves every old code token.',
    combined_gates='pending',final_reader_review='pending',package_accepted=False,chapter_complete=False,goal_complete=False))
print('Seven retained headers and all code tokens unchanged; two reader expressions repaired with exact historical snapshots. Integrated/package gates pending.')
