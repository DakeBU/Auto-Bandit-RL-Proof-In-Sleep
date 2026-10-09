from common_reader_v6 import *

fixed()
receipt=load(RUN/'FINAL-receipt-v1.json')
assert sha(RUN/'FINAL-receipt-v1.json')=='7f0ade24d0d121dcd4d9d7d91a5c73478b5b5d011c6433ec5242e418b02abf50'
assert sha(receipt['report'])==receipt['report_sha256']=='b10f8558fc3560a27d6c0f781f41613239cad886309ca5e638a78efb319ed593'
assert receipt['verdict']=='accepted-with-explicit-delta' and not receipt['required_blocking_repairs']
assert len(receipt['source_object_verdicts'])==17 and all(r['verdict']=='accepted-with-explicit-delta' for r in receipt['source_object_verdicts'])
for r in load(receipt['input_index'])['rows']:assert sha(r['path'])==r['sha256'],r['path']
pr=json.loads(subprocess.check_output(['gh','pr','view','203','--json','number,url,state,isDraft,headRefOid,headRefName,baseRefName,mergedAt'],encoding='utf8'))
assert pr['state']=='OPEN' and pr['isDraft'] and pr['mergedAt'] is None and pr['baseRefName']=='codex/research-online-ftl-obstruction'
write(RUN/'delivery-PR203-candidate-v2.json',dict(PR=pr,
    remote_exact_head=subprocess.check_output(['git','ls-remote','origin','refs/heads/'+BRANCH],encoding='utf8').split()[0],
    official_app_attachment_succeeded=True,attachment_url=pr['url'],
    actual_attachment_tool='mcp__codex_app__attach_artifact, successful current logical turn immediately after creation',
    chapter_complete=False,goal_complete=False))
mutables=[ROOT/d/(TASK+'.md') for d in ['tasks','proof-obligations','conversion-windows']]
mutables += [CONTRIBUTION]+[Path(r['path']) for r in load(RUN/'reader-integration-bindings-v3.json')['rows']]
mutables += [RUN/p for p in ['trials.jsonl','lifecycle-sessions.jsonl','lifecycle-state.json','own-artifact-journal.md','retrieval-index-v1.jsonl']]
before=[]
for i,p in enumerate(mutables):
    snapshot=RUN/'snapshots'/('before-post-FINAL-v1-'+str(i).zfill(2)+'.raw')
    write(snapshot,p.read_bytes());before.append(dict(path=p.as_posix(),before_sha256=sha(p),snapshot=snapshot.as_posix()))
write(RUN/'post-FINAL-metadata-before-v1.json',dict(rows=before,permission=receipt['permitted_future_metadata'],FINAL_sha256=sha(RUN/'FINAL-receipt-v1.json')))
# Actual native records are owned by this task. The formalizer records the distinct review artifact.
for label,evidence,note in [
 ('SITE-SCHEMA',RUN/'site-build-v1-exit.json','Actual site schema failure1; exact original4 teaching-route repair subsequently passed site2/site3.'),
 ('CONTRIBUTOR-SCHEMA',RUN/'candidate-contributor-stack-v2-exit.json','Actual affected_files schema failure1; docs coverage moved to results_ledger; current both nonempty bases pass.'),
 ('CAPTURE-WRAPPER',RUN/'capture-output-recovery-v2.json','Actual browser child0 but wrapper1 after filename collision; exact historical bytes restored and new outputs retained/versioned; failure not recast passed.'),
 ('CUMULATIVE-DIFF',RUN/'FINAL-cumulative-diff-audit-v2.json','Actual unexcluded2; exactly13 SHA-bound RAW evidence exceptions independently accepted; scoped0, no production/Test/reader/contract exception.'),
 ('PUSH-CREDENTIAL',RUN/'delivery-candidate-push-v1-exit.json','Actual push128/403 wrong GCM account; command-scoped active gh credential with verified push permission succeeded0, no global credential mutation.')]:
    native('post-FINAL-failure-'+label.lower()+'-v1','trial-log','--task',TASK,'--role','lower','--kind','attempt','--status','failed','--attempt-id',label+'-V1','--run-id',RUN.name,'--progress-class','diagnostic','--notes',note,'--verifier-evidence',str(evidence))
native('post-FINAL-review-trial-v1','trial-log','--task',TASK,'--role','reviewer','--kind','review','--status','accepted',
    '--attempt-id','C1-INTEGRATION-FINAL-V1','--reviewer-validated','--run-id',RUN.name,'--progress-class','closed-frontier',
    '--notes','Formalizer records distinct source reviewer FINAL artifact:17 source objects accepted-with-explicit-delta, R1-R10/current10pixels/raw13exceptions adjudicated. Source integration only; postnative/current status-site/delivery still required; wholeGoalACTIVE. Obligations17->0 refers only reviewed source objects, not unknown proof-leaf total.',
    '--obligations-before','17','--obligations-after','0','--verifier-evidence',str(RUN/'FINAL-receipt-v1.json'),'--verifier-evidence',str(RUN/'FINAL-review-v1.md'))
payload=dict(scope='17-source-object reconciliation accepted-with-explicit-delta; not chapter completion',FINAL_sha256=sha(RUN/'FINAL-receipt-v1.json'),
    source_objects=17,proof_total=None,public_body_sha256=sha(PUBLIC),canary_body_sha256=sha(CANARY),postnative_site_delivery_required=True,chapter_complete=False,goal_complete=False)
native('post-FINAL-lifecycle-v1','lifecycle-event','--session',TASK,'--event','accepted','--payload-json',json.dumps(payload))
names=[t['name'] for t in load(CONTRACT/'general-initialization-targets-stabilized-v3.json')['new_targets']]
args=['retrieval-record','--task',TASK,'--query','Actual general-initial FTL terminals closed; reuse exact public same-run correction/refined/upper/best-average proofs after distinct FINAL.',
    '--compiled-scratch',str(RUN/'general-init-public-value-witnesses-v1.lean'),'--provenance',str(RUN/'FINAL-receipt-v1.json'),'--output',str(RUN/'retrieval-index-v1.jsonl')]
# Locate the already compiled whole-value witness from its actual recorded readiness receipt.
if not Path(args[args.index('--compiled-scratch')+1]).is_file():
    candidates=list(RUN.glob('*general*value*.lean'))+list(RUN.glob('*general*public*.lean'))
    candidates=[p for p in candidates if 'ftlPredict_bestRegret_initial_correction' in p.read_text('utf8') and '#print axioms' in p.read_text('utf8')]
    assert candidates, 'Actual compiled public witness must be located, never invented'
    args[args.index('--compiled-scratch')+1]=str(candidates[0])
for n in names:args.extend(['--candidate',n])
native('post-FINAL-retrieval-v1',*args)
native('post-FINAL-memory-v1','memory-record','--type','checkpoint','--task',TASK,'--provenance-kind','distinct_source_FINAL',
    '--provenance',str(RUN/'FINAL-receipt-v1.json'),'--status','source-reconciled-native-postreview-pending',
    '--verifier',str(RUN/'FINAL-receipt-v1.json'),'--role','reviewer','--details-json',json.dumps(payload),'--output',str(RUN/'memory-index-post-FINAL-v1.jsonl'))
boundary=('Current Chapter1 source reconciliation covers17 required source audit objects, preserving the original16 and the required any-initial FTL guarantee. '
    'There are54 generic public proof contracts and27 complementary canaries; the required proof-leaf total remains unknown(null), with no coverage percentage inferred. '
    'Four new public proofs serve one source family. Separate Lean/harness, semantic FINAL, native, reader/site, post-native and delivery evidence is retained; '
    'the current chapter-gate decision is recorded in the versioned contract ledger and docs/contracts/online-book-v1/coverage.json. '
    'The ordinary-limit source correction is explicit, not a proof of the false-as-written universal inference or author endorsement. '
    'Whole Chapters1-16 Goal ACTIVE; Chapter2 partial, Chapters3-16 unenumerated and necessary appendices required. '
    'Draft PR203 is stacked on OPEN draft unmerged PR202 exact '+BASE+'. Main/live unchanged; no merge or deployment. Earlier cards retain historical package boundaries.')
oldboundary=load(RUN/'reader-proposal-v1.json')['boundary']
bindings=load(RUN/'reader-integration-bindings-v3.json')
for i,row in enumerate(bindings['rows']):
    p=Path(row['path']);data=load(p)
    if p.name=='chapters.json':
        c=next(x for x in data['chapters'] if x['slug']=='online-foundations')
        c['summary']='Current Chapter1 source reconciliation: causal guessing, exact general-initial FTL, separate ordinary/upper regret semantics and explicit IID benchmarks; source correction explicit.'
        c['completion_blockers']=[boundary]
        c['known_gaps']=['Chapter2 remaining obligations, unenumerated Chapters3-16 and necessary appendix dependencies remain required. Chapter1 gate is recorded separately in the current contract ledger.']
    elif p.name=='readings.json':
        c=next(x for x in data['readings'] if x['slug']=='online-foundations')
        cards=c['source_statements'] if 'source_statements' in c else c['source_theorems']
        card=cards[-1];assert card['local_status']['boundary']==oldboundary
        card['local_status']['boundary']=boundary;card['local_status']['label']='Compiled locally; source correction explicit'
    elif p.name=='highlights.json':
        for note in data['highlights']:
            if note['full_name'] in names:
                assert oldboundary in note['lean_notes'];note['lean_notes']=note['lean_notes'].replace(oldboundary,boundary)
    elif p.name=='coverage.json':
        c=next(x for x in data['chapters'] if x['chapter']==1)
        c['status']='source-reconciled-native; post-native/chapter-delivery gate pending'
        c['accepted']=False;c['boundary']=boundary
        c['FINAL_receipt']=str((RUN/'FINAL-receipt-v1.json').relative_to(ROOT))
    else:raise AssertionError(p)
    p.write_bytes((json.dumps(data,ensure_ascii=False,indent=2)+'\n').encode('utf8'))
    result=RUN/'snapshots'/('reader-result-post-FINAL-v4-'+str(i)+'.raw');write(result,p.read_bytes())
    row['result_sha256']=sha(p);row['planned_result_snapshot']=result.as_posix()
bindings['post_FINAL_status_only']=True;bindings['FINAL_sha256']=sha(RUN/'FINAL-receipt-v1.json')
write(RUN/'reader-integration-bindings-v4.json',bindings)
guard=(RUN/'common_reader_v6.py').read_text('utf8').replace('reader-integration-bindings-v3.json','reader-integration-bindings-v4.json').replace('online-c1-chapter-audit-site-v3','online-c1-chapter-audit-site-v4')
write(RUN/'common_reader_v7.py',guard)
mapping=load(CONTRACT/'chapter-one-current-candidate-v4.json')
verdicts={r['source_id']:r for r in receipt['source_object_verdicts']}
for row in mapping['rows']:
    row['historical_candidate_status']=row.get('status')
    row['status']='source-reconciled-native; chapter gate pending post-native/site/delivery'
    row['current_gate_status']=row['status'];row['FINAL_verdict']=verdicts[row['source_id']]['verdict']
    row['FINAL_receipt_sha256']=sha(RUN/'FINAL-receipt-v1.json')
mapping['source_objects_semantically_reconciled']=17;mapping['accepted_source_objects_this_current_chapter_gate']=0
mapping['native_transition_executed']=True;mapping['chapter_complete']=False;mapping['goal_complete']=False
write(CONTRACT/'chapter-one-post-native-v5.json',mapping)
doc=('Source: Orabona arXiv1912.13213v10,21June2026; SHA '+PDF_SHA+'; printed1-6/PDF13-18. '
    'Current17 source objects are separately reviewed; original16 and source-as-written ordinary-limit definition remain frozen. '
    'Actual same-FTL counterexample and separately reviewed source correction are explicit. Four new general-initial performance proofs close one missing source family. '
    '54generic contracts/27canaries/null required proof-leaf total are not coverage percentages. '
    'Actual root9105/Tests9270/fullharness472tests7skips/axioms/fences/wholevalues/directVALUE passed on unchanged code/pins. '
    'Distinct automated FINAL accepted-with-explicit-delta, report/receipt in current RUN; native transition now executed. '
    'Updated status reader/site, own shadow, separate post-native and PR203 delivery review remain prerequisites to chapter acceptance. '
    'Whole1-16GoalACTIVE; C2partial/C3-16unenumerated/null/necessaryappendicesrequired; no main/live/merge/deploy. '
    'This current document supersedes the retained historical bootstrap template and proving-stage statuses; their exact RAW bytes are preserved before-post-FINAL snapshots.')
for d in ['tasks','proof-obligations','conversion-windows']:
    p=ROOT/d/(TASK+'.md')
    text='# '+{'tasks':'Chapter1 source reconciliation','proof-obligations':'Chapter1 current obligations','conversion-windows':'Chapter1 conversion window'}[d]+'\n\nTask id: `'+TASK+'`\nStatus: `source-reconciled-native; chapter gate pending`\n\n'+doc+'\n\n'
    text+='| Source object | Current source verdict | Public declarations |\n| --- | --- | --- |\n'
    for row in mapping['rows']:text+='| '+row['source_id']+' | accepted-with-explicit-delta | '+', '.join('`'+n+'`' for n in row.get('exact_public_names',[]))+' |\n'
    text+='\nAlgorithm uses fixed legal initializer, actual count/mean recurrence and strict past. Source round1 is Lean0. Positive-horizon correction only; first legal loss bound1, half-onlyquarter, reciprocal denominators2..T. G001 -> G002 and G003; G001+actualhalfbestaverage0 -> G004. Existing projection/convex foundations are reused in the same shared registry; no extra library. IID joint independence/private tape/AE feasibility, outside-expectation fixed min and exogenous kernel model are explicit. No false universal ordinary-comparator-limit claim.\n'
    text+='\nOpen current gate obligations: applicable updated site/registry/current status DOM/pixels; own native shadow; distinct post-native and actual PR203 remote/attachment/delivery review. These are not new mathematical assumptions. No unproved mandatory source object is dropped. Independent History/Problems1.1/1.2 remain optional.\n'
    p.write_bytes(text.encode('utf8'))
v=load(CONTRIBUTION);v['truth_boundary']=boundary
v['semantic_roundtrip']['remaining_semantic_delta']='Whole source17 FINAL accepted-with-explicit-delta; native transition executed. Explicit ordinary-limit correction/IID models/derived lower constant remain. Current updated-status site/postnative/delivery adjudication pending; no wholeGoal/main/live claim.'
v['verification']['independent_review']='Distinct staged automated source17 FINAL b10f8558, receipt7f0ade24, all1128RAW/current10pixels/R1-R10; post-native/delivery pending. No human/external/absolute-blind/runtime model claim.'
v['verification']['site_check']='SITE3 clean78482 registry10977+4/site/DOM/pixels actually passed; post-FINAL status-only reader changes require new SITE4/DOM/pixels. No new Lean/pin/body change.'
v['graph_contribution']['visual_review']='Actual106selectednodes/10206TYPE_VALUEedges,9production/35canarydirectVALUEpairs; shared registry10977+4 preserved and current10pixels independently reviewed. Status-only site4 revalidation pending.'
CONTRIBUTION.write_bytes((json.dumps(v,ensure_ascii=False,indent=2)+'\n').encode('utf8'))
write(RUN/'post-FINAL-metadata-after-v1.json',dict(rows=[dict(**r,after_sha256=sha(r['path'])) for r in before],
    source_objects=17,proof_total=None,chapter_complete=False,goal_complete=False,
    before_index_sha256=sha(RUN/'post-FINAL-metadata-before-v1.json'),new_reader_bindings_sha256=sha(RUN/'reader-integration-bindings-v4.json'),
    required_next='Current reader preservation audit; native shadow; updated clean SITE4/registry/DOM/currentpixels; distinct post-native and delivered PR review.'))
print('Native source reconciliation and owned status metadata updated; chapter remains unaccepted pending post-native/site/delivery.')
