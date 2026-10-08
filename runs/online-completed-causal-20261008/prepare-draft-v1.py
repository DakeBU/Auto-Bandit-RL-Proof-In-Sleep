from common_v1 import *
sys.path.insert(0,str(ROOT))
from tools.abrl_lifecycle import statement_hash

assert not PUBLIC.exists() and not CANARY.exists()
assert subprocess.check_output(['git','rev-parse','HEAD'],encoding='utf8').strip()==BASE
assert sha(PDF)==PDF_SHA
paths=['BanditRLProof.lean','Tests.lean','lean-toolchain','lakefile.lean','lake-manifest.json',
    'runs/active_frontier.json','runs/trials.jsonl','runs/lifecycle_sessions.jsonl','runs/lifecycle_memory.jsonl','MANIFEST.md',
    'website/content/readings.json','website/content/chapters.json','website/content/highlights.json',
    'website/content/functor_hypergraph.json','website/content/graph_memory_index.json',
    'BanditRLProof/OnlineGuessingAECausal.lean','BanditRLProof/OnlineGuessingRandomizedIID.lean',
    'BanditRLProof/OnlineGuessingIIDBenchmark.lean','BanditRLProof/OnlineLearningStochastic.lean',
    'Tests/OnlineGuessingAECausalCanary.lean']
rows=[]
for i,rel in enumerate(paths):
    p=ROOT/rel;q=RUN/'baseline'/('input-'+str(i)+'.raw');write(q,p.read_bytes())
    rows.append(dict(path=rel,snapshot=q.relative_to(ROOT).as_posix(),sha256=sha(q)))
write(RUN/'draft-baseline-v1.json',dict(rows=rows,branch=BRANCH,base=BASE))
baseline_fixed()
prior=ROOT/'runs/online-ae-causal-20261008'
for name in ['source-pdf13-text-v1.txt','source-pdf15-text-v1.txt','source-pdf13-v1.png','source-pdf15-v1.png']:
    write(RUN/name,(prior/name).read_bytes())
write(RUN/'prior-PR198-final-ready-v4.json',(ROOT/'tmp/online-ae-causal-final-ready-v4.json').read_bytes())
for label,command in [('stacked-base-current-v1',['gh','pr','view','198','--json','number,state,isDraft,headRefOid,baseRefName,headRefName,mergedAt,statusCheckRollup']),
    ('actual-dependency-api-v1',['lake','env','lean',prior/'future-completion-api-v1.lean'])]:gate(label,*command)
remote=load(RUN/'stacked-base-current-v1.log')
assert remote['headRefOid']==BASE and remote['state']=='OPEN' and remote['isDraft'] and remote['mergedAt'] is None
write(RUN/'00_context.md','Whole Orabona v10 Chapters1-16 Goal ACTIVE/unbudgeted. Requested GPT-6 Astra / medium, not runtime-attested. Worktree '+ROOT.as_posix()+', canonical E:/ABRL/research main6847, branch '+BRANCH+' stacked on OPEN draft unmerged PR198 exact'+BASE+'. Previous AE3 derived obligations accepted and delivered; no whole source object/chapter/Goal completion. Current package4 derived ambient-null-augmentation/real-version and same original causal terminal obligations; general kernel REQUIRED. Original16/null/remainingC1/C2/unenumeratedC3-16/appendices preserved. Single lower route. Distinct reused osd_blind/source_reviewer mandatory semantic actors, no optional agents/absolute blind/human/external review. Root personally reread original source text and viewed original PNG13/15; copied cached images, no fresh rendering claimed. Shared Git/lake junctions retained. No production bodies yet.')
text=(CONTRACT/'targets-v1.lean.txt').read_text(encoding='utf8')
parts=text.split('\ntheorem ')[1:];targets=[]
for i,part in enumerate(parts):
    if i==len(parts)-1:part=part.split('\n\nend BanditRL.OnlineLearning')[0]
    header='theorem '+part.strip();name=header.split()[1]
    targets.append(dict(id='L'+str(i+1),name='BanditRL.OnlineLearning.'+name,
        owning_file=PUBLIC.relative_to(ROOT).as_posix(),header=header,statement_hash=statement_hash(header),
        raw_header_sha256=hashlib.sha256(header.encode('utf8')).hexdigest(),phase='draft',compiled=False))
assert len(targets)==4
write(CONTRACT/'targets-v1.json',dict(version=1,targets=targets,mathematical_terminals_compiled=0))
write(CONTRACT/'dependency-DAG-v1.json',dict(nodes=[
    dict(id='L1',ready=True,parents=['eventuallyMeasurableSpace','mapNatBool','measurable_mapNatBool','injective_mapNatBool','Measurable.measurableEmbedding','measurable_to_bool','ae_all_iff','MeasurableEmbedding.measurable_invFun','MeasurableEmbedding.leftInverse_invFun']),
    dict(id='L2',ready=False,parents=['L1','Measurable.aestronglyMeasurable','AEStronglyMeasurable.congr','ae_predictable_exists_bounded_history_policy']),
    dict(id='L3',ready=False,parents=['L1','Measurable.aestronglyMeasurable','AEStronglyMeasurable.congr','ae_predictable_private_seed_independent']),
    dict(id='L4',ready=False,parents=['L1','Measurable.aestronglyMeasurable','AEStronglyMeasurable.congr','ae_predictable_private_seed_expectedFixed_excess'])],
    lower_route='one actual completed real-version producer reused by three real consumers',
    scope='only exactly defined ambient-null augmentation, not arbitrary other completions or kernels',chapter_complete=False,goal_complete=False))
write(CONTRACT/'semantic-signature-v1.json',dict(source_sha256=PDF_SHA,source_pages=[dict(printed=1,pdf=13),dict(printed=3,pdf=15)],
    objects='real outputs; arbitrary measurable Omega/Seed; same original infinite P/Y/S',
    completed_information='exact eventuallyMeasurableSpace F (ae ambient_mu); each set AE an F-measurable set',
    no_trim_completion_equivalence=True,core_needs_F_below_ambient=False,core_probability_or_finiteness=False,
    causal_information='F_t below seed plus strict-past comap; same time0 empty history',
    all_time='one common AE event for one policy family before all horizons',
    original_unit_feasibility='AE for every natural time, explicit L2/L4 premise',
    seed_independence='independent of entire infinite target stream, joint independent targets',
    benchmark='minimum expected fixed comparator loss outside expectation; original P on both sides',
    population_mean='analysis only',zero_horizon='empty cumulative identity and nonnegative0',
    no_rate_or_convergence=True,no_off_null_equality=True,no_executable_unknown_law_constructor=True,
    general_causal_kernel_required=True,derived_targets=[r['name'] for r in targets],chapter_complete=False,goal_complete=False))
write(CONTRACT/'reader-requirements-v1.json',dict(
    R1='Pinned Orabona v10 printed1/PDF13 and printed3/PDF15; four derived targets, not four printed results. Original16/null source ledger and active whole Goal remain.',
    R2='Exact ambient-mu null augmentation sets AE to F-measurable sets, not an asserted mu.trim F completion equivalence. Real output enables countable coding and measurable inverse; core no probability/F<=ambient/countability on Omega.',
    R3='Actual core version producer, not supplied AE version. One infinite same-process globally bounded policy and one common all-time AE event; original AE [0,1] premise, no off-null equality/executable unknown-law claim.',
    R4='Original current independence from joint targets and whole-stream seed independence; independence terminal no support/same-law/boundedness/integrability premise. L2 policy needs no probability/ambient S/Y measurability.',
    R5='Original-P finite exact expectedFixedRegret against min expected fixed unit losses outside expectation, every natural T including0; mean analysis-only, no convergence/rate/pathwise/highprob upgrade.',
    R6='Actual augmented-measurable yet not ordinary pointwise-predictable AE-only canary with nonempty null branch, random seed/positive variance and nonzero two-round1/2; instantiate all four public bodies, full types/axioms/fences/root/Tests/fullharness/ownshadow/site/pixels separately.',
    R7='Source completion gap only for precise ambient augmentation; general causal kernels and other completion notions not proved by premise substitution. All remaining C1/C2/C3-16/appendices required, main/live unchanged, distinct reused staged actors/no absolute blind/human/external/runtime attestation.'))
write(CONTRACT/'canary-plan-v1.md','Reuse actual previous seeded IID nonempty-null badPrediction. Prove augmented-field measurability from causal_version_measurable.eventuallyMeasurable_of_eventuallyEq, without assuming AEStrong as the new input. Invoke core version and all three completed terminals. Retain notordinarypredictable/noteverywhereunit, positivevariance1/4, original two-round excess1/2 and zero horizon. No new proof/compiled status before bodies and focused gate.')
ledger=load(ROOT/'docs/contracts/online-ae-causal-v1/chapter-one-source-ledger-accepted-v2.json')
assert len(ledger['original16_source_objects'])==16 and ledger['required_proof_leaf_total'] is None
ledger['current_completed_leaf_overlay']=dict(task=TASK,phase='draft',derived_obligations=4,accepted=0,
    precise_completed_space='eventuallyMeasurableSpace F (ae ambient_mu)',general_kernel_required=True,
    chapter_complete=False,goal_complete=False)
write(CONTRACT/'chapter-one-source-ledger-draft-v1.json',ledger)
proto=text.split('\ntheorem ')[0]+'\n'
for t in targets:
    rest=t['header'].split(t['name'].split('.')[-1],1)[1].strip().replace(' :\n',',\n',1)
    proto+='#check (∀ '+rest+')\n\n'
proto+='end BanditRL.OnlineLearning\n';write(RUN/'draft-typecheck-v1.lean',proto)
gate('draft-typecheck-v1','lake','env','lean',RUN/'draft-typecheck-v1.lean')
native('draft-new-task-v1','new-task',TASK,'--kind','completed-causal-producer',
    '--title','Ambient completed-information real versions and original IID excess','--target-lean',PUBLIC.relative_to(ROOT).as_posix())
for d in ['tasks','proof-obligations','conversion-windows']:
    p=ROOT/d/(TASK+'.md');write(RUN/('native-'+d+'-template-v1.raw'),p.read_bytes())
    p.write_bytes(p.read_bytes()+('\n\n## Draft4 derived completion targets\n\n'+(CONTRACT/'source-intent-v1.md').read_text(encoding='utf8')+'\nExact targets/DAG in '+CONTRACT.relative_to(ROOT).as_posix()+'. L1 dependency-ready; L2/L3/L4 await L1. Type syntax checked; no theorem body or terminal compiled. Contract source/semantic review REQUIRED.\n').encode('utf8'))
native('draft-blueprint-v1','blueprint-refresh',TASK)
native('draft-lifecycle-v1','lifecycle-event','--session',TASK,'--event','draft','--payload-json',
    json.dumps(dict(run_id=RUN.name,contract_version=1,source_sha256=PDF_SHA,
        target_statement_hashes=[r['statement_hash'] for r in targets],obligations=4,compiled=0,chapter_complete=False,goal_complete=False)))
for name in ['bandit_paper_cards','bandit_scenario_cards','bandit_textbook_cards','proof_weapon_cards','local_leaf_cards','local_lean_declarations']:
    p=ROOT/'research-wiki/retrieval-index'/(name+'.json');write(RUN/'baseline'/('retrieval-'+name+'.raw'),p.read_bytes())
native('draft-reference-index-v1','reference-index')
for query in ['completed_measurable','EventuallyMeasurable','ae_predictable_private_seed']:
    native('draft-retrieval-'+query+'-v1','list-lean-decls',query,'--statement')
write(RUN/'10_director-v1.md','Four exact derived targets, no future-loss algorithm existence. Pin ambient augmentation interpretation; corerealversion L1 dependency-ready, terminal L2-L4 blocked only on L1. Single lower route; same model staged director/architect/worker with mandatory distinct decoder/source reviewer, no independent external review claim. Original source16/null/fullGoal preserved.')
write(RUN/'20_architect-v1.md','Frozen after source contract review: exact four headers; allow only new public module and owned canary until favorable BODY. Actual mathlib countable coding/inverse API verified. Core witness must be obtained from augmented measurability, not supplied. AE original unit assumption belongs only to policy/excess terminals; L3 independence no boundedness. No proof body yet.')
print('Actual draft/type/API/native records created; four bodies unproved, semantic source-contract review pending.',flush=True)
