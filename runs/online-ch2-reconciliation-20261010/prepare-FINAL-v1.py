from integration_guard_v4 import *
fixed()
b=load(RUN/'formula-render-v1-browser.json');assert len(b['images'])==28
px=load(RUN/'root-original-pixel-review-v1.json')
assert px['actor']=='/root' and px['personally_viewed_original_count']==28 and px['images']==rows(RUN/f for f in b['images'])
assert load(RUN/'full-harness-inspected-v2.json')['actual_check_passed']
assert load(RUN/'registry-inspected-v1.json')['total_nodes']==11054
indices={sha(p):dict(path=p.as_posix(),encoding='raw-file') for d in [RUN,CONTRACT] for p in d.rglob('*') if p.is_file() and '__pycache__' not in p.parts}
def walk(obj,p,at=''):
    if isinstance(obj,dict):
        for k,v in obj.items():
            if k.endswith('raw_base64') and isinstance(v,str):
                raw=base64.b64decode(v);indices[hashlib.sha256(raw).hexdigest()]=dict(path=p.as_posix(),encoding='embedded-exact-raw-base64',field=at+'/'+k)
            else:walk(v,p,at+'/'+k)
    elif isinstance(obj,list):
        for i,v in enumerate(obj):walk(v,p,at+'/'+str(i))
for d in [RUN,CONTRACT]:
    for p in d.rglob('*.json'):walk(load(p),p)
resolved=[]
reviews=['source-model-review-v1.json','generic-ftl-contract-review-v1.json','production-BODY-canary-CONTRACT-repair-review-v1.json','ftl-canary-BODY-review-v1.json','integration-plan-review-v1.json','integration-plan-review-v2.json','evidence-attributes-review-v1.json','candidate-git-site-plan-review-v1.json','candidate-execution-repair-review-v2.json','contributor-schema-repair-review-v3.json']
for name in reviews:
    review=load(RUN/name);changes=[]
    for row in load(review['input_manifest'])['rows']:
        p=Path(row['path']);old=row['sha256']
        if sha(p)!=old:
            assert old in indices,(name,p,old)
            changes.append(dict(path=p.as_posix(),historical_sha256=old,current_sha256=sha(p),exact_historical_snapshot=indices[old]))
    resolved.append(dict(review=name,review_sha256=sha(RUN/name),changed_live_rows=changes,all_other_current_inputs_unchanged=True))
write(RUN/'FINAL-historical-bindings-v1.json',dict(reviews=resolved,scope='Exact old bytes retrievable; six source transitions, OWN attrs and manifest s->[s] not described as unchanged.'))
capture('FINAL-fresh-fetch-v1','git','fetch','origin')
_,out=capture('FINAL-parent-PR214-v1','gh','pr','view','214','--json','number,url,state,isDraft,headRefName,headRefOid,baseRefName,mergedAt')
pr=json.loads(out);assert pr['state']=='OPEN' and pr['isDraft'] and pr['mergedAt'] is None and pr['headRefOid']==BASE
capture('FINAL-canonical-research-status-v1','git','-C','E:/ABRL/research','status','--porcelain=v1','-z')
capture('FINAL-fresh-main-v1','git','rev-parse','origin/main')
site=load(RUN/'registry-inspected-v1.json')
write(RUN/'PR-body-v1.md','Adds Orabona v10 generic strict-past FTL as an explicit partial mathematical selector: feasible initialization, conditional minimum, exact nonattainment, restricted-domain invariance and actual prefix-causal Option equality. Four definitions and nine proofs represent one source algorithm-definition foundation, with eight complete concrete canaries. Reconciles Chapter2 source provenance and the existing prescient dependency chain without counting overlapping containers as independent results.\n\nValidation: root9115/Tests9290; fullharness472tests7skips;21public production/Test values and standard axioms;17frozenheaders/safe-verifies;24selectedcompiledvalues/11selectedconjuncts. Both nonempty contributor bases passed after a retained schema repair. Clean local site '+site['source_commit']+' preserves every11041oldregistryobject+13canonicalproduction=11054;14cards/17sourceguideformulas/28desktop originals receive root and distinct staged automated review. Evidence: docs/contracts/online-ch2-reconciliation-v1 and runs/online-ch2-reconciliation-20261010/FINAL-review-v1.md with bound receipts.\n\nStacked on OPEN draft unmerged PR #214 exact '+BASE+' ('+pr['headRefName']+'). No universal attainment, executable/measurable optimizer, new FTL regret bound or complete run after failure: P1=none has no playable action; P2=some0 is an independent longer-prefix query. All8forwardcontainers required/open, including6future mathematicalclaims unenumerated. Chapter2partial/null, Ch3-16unenumerated/null, persistent GoalACTIVE. Local site binds its candidate commit, not later evidence commits. No merge/deployment/main/live/CI/retirement claim.\n')
write(RUN/'PR-plan-v1.json',dict(title='[Online Learning Ch2] Add generic causal FTL selector and source reconciliation',body_path=(RUN/'PR-body-v1.md').as_posix(),body_sha256=sha(RUN/'PR-body-v1.md'),base=pr['headRefName'],head=BRANCH,parent_exact_head=BASE,draft=True,merge=False,deploy=False))
write(RUN/'FINAL-packet-v1.md',(RUN/'FINAL-packet-proposal-v1.md').read_bytes())
capture('FINAL-stage-v1','git','add',*load(RUN/'candidate-stage-plan-v1.json')['stage'])
capture('FINAL-full-package-diff-v1','git','diff','--cached',BASE,'--check')
paths={p for d in [RUN,CONTRACT] for p in d.rglob('*') if p.is_file() and '__pycache__' not in p.parts}
paths.update([MODULE,TEST,CONTRIBUTION,PDF,ROOT/'BanditRLProof.lean',ROOT/'Tests.lean'])
paths.update(ROOT/d/(TASK+'.md') for d in ['tasks','conversion-windows','proof-obligations','research-wiki/retrieval-index'])
paths.update(ROOT/p for p in ['lean-toolchain','lakefile.lean','lake-manifest.json','website/content/chapters.json','website/content/readings.json','website/content/highlights.json','docs/contracts/online-book-v1/coverage.json'])
paths.update(Path(r['path']) for r in load(RUN/'browser-generated-inputs-before-v1.json')['rows'])
source=ROOT/'runs/online-ch2-chapter-audit-20261009'
paths.update(source.glob('source-pdf*-v1.png'));paths.update(source.glob('source-pdf*-text-v1.txt'))
fixed()
write(RUN/'FINAL-inputs-v1.json',dict(rows=rows(paths),source_commit=site['source_commit'],production_proof_terminals=9,public_canaries=8,new_definitions=4,additional_selected_Test_auxiliaries=3,source_family_count=1,source_container_closed=False,chapter_proof_total=None,chapter_complete=False,whole_Goal='active'))
print('FINAL exact packet prepared; distinct semantics/pixels/narrow-native review pending.',flush=True)
