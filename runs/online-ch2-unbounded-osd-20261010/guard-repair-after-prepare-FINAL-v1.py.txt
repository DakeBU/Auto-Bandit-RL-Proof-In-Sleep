from publication_guard_v2 import *
fixed()
b=load(RUN/'formula-render-v1-browser.json');assert len(b['images'])==32
px=load(RUN/'root-original-pixel-review-v1.json')
assert px['actor']=='/root' and px['personally_viewed_original_count']==32
assert px['images']==rows(RUN/f for f in b['images'])
write(RUN/'pre-FINAL-contribution-v1.json',dict(path=CONTRIBUTION.as_posix(),sha256=sha(CONTRIBUTION),before_raw_base64=base64.b64encode(CONTRIBUTION.read_bytes()).decode('ascii')))
c=load(CONTRIBUTION)
c['verification']['site_build']='Applicable actual combined Lean gate passed before clean local SITEv1 build at '+load(RUN/'clean-candidate-site-binding-v1.json')['actual_head']+'. Exact source/root/toolchain hashes bound. No generated website/_site edits, deployment or freshsite-at-later-evidence-head claim.'
c['verification']['site_check']='Actual site check; all11026completeoldregistryobjects unchanged+15canonicalproduction=11041;13sourcecards. Actualfile desktop16sourceguideMathJaxformulas/zeroerrors/foldedLean/built-inwrap/32originals personally viewed byroot. Distinct FINAL/pixels pending.'
CONTRIBUTION.write_bytes((json.dumps(c,ensure_ascii=False,indent=2)+'\n').encode('utf8'))
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
for name in ['contract-source-review-v1.json','seven-leaf-body-review-v1.json','full-body-canary-review-v1.json','canary-BODY-review-v1.json','publication-plan-review-v1.json']:
    review=load(RUN/name);changes=[]
    for row in review['raw_input_checks']+review.get('supplemental_raw_input_checks',[]):
        p=Path(row['path']);old=row.get('before_sha256') or row.get('expected_sha256') or row.get('sha256')
        if sha(p)!=old:
            assert old in indices,(name,p,old)
            changes.append(dict(path=p.as_posix(),historical_sha256=old,current_sha256=sha(p),exact_historical_snapshot=indices[old]))
    resolved.append(dict(review=name,review_sha256=sha(RUN/name),changed_live_rows=changes,all_other_current_inputs_unchanged=True))
write(RUN/'FINAL-historical-bindings-v1.json',dict(reviews=resolved,scope='Historical stage bytes remain retrievable exactly. Approved OWN native and obligation/index changes are NOT claimed live-unchanged. Exact five old-path transitions were separately approved; allotherbaseline unchanged.'))
capture('FINAL-fresh-fetch-v1','git','fetch','origin')
_,out=capture('FINAL-parent-PR213-v1','gh','pr','view','213','--json','number,url,state,isDraft,headRefName,headRefOid,baseRefName,mergedAt')
pr=json.loads(out);assert pr['state']=='OPEN' and pr['isDraft'] and pr['mergedAt'] is None and pr['headRefOid']==BASE
capture('FINAL-canonical-research-status-v1','git','-C','E:/ABRL/research','status','--porcelain=v1','-z')
capture('FINAL-fresh-main-v1','git','rev-parse','origin/main')
g=load(RUN/'full-harness-inspected-v1.json')
write(RUN/'PR-body-v1.md','Proves Orabona v10 Theorem5.4 as a required Chapter2 dependency: polynomially decreasing-step unprojected OSD can incur regret at least half-phi(alpha)*T^(2-alpha) at comparator0. The proof uses the same canonical causal selector/step/iterate/regret, constructs the switching losses, derives the exact scalar identity and integral bounds, and embeds the actual run in positive dimension. The exact horizon threshold, phi range and mandatory left-limit/numerical supplement are retained.\n\nTwo complete public canaries prove actual nonzero updates, different positive steps and pre-update scoring: T2 regret1; T64 E2D source threshold,256/15<=R,17<R and fully applied source existential. The horizon-specific streams differ. Four individually selected compiled result branches retain the new production parents. Validation:17public definitions/proofs/standard-only axiom lists,13frozen statements/safe-verifies,24requiredVALUEpairs; combinedroot/Tests/fullharness '+json.dumps(g['unittest_runs'])+'; ownlookup/index/shadow; nonempty contributor gates against both bases; clean local site with all11026oldregistryobjects preserved+15canonicalproduction=11041 and32actual desktop originals root+distinct automated review. Failed attempts and RAW stage history retained.\n\nStacked on OPEN draft unmerged PR #213 exact '+BASE+', branch '+pr['headRefName']+'. Four definitions and eleven proof terminals close one source theorem dependency, not fifteen source results. Positive dimension is source-implicit and necessary; totalphi(1)=1 differs from the left limit. This is a failure of this OSD algorithm, not a minimax statement against all learners. All eight Chapter2 source forward containers remain required/open pending dedicated reconciliation; Chapter2 and the persistent Chapters1-16Goal remain incomplete. No Chapter5 chapter acceptance,merge/deployment/main/live/CI/retirement claim. Local site is bound to its candidate commit, not later evidence commits.\n\nEvidence: docs/contracts/online-ch2-unbounded-osd-v1; runs/online-ch2-unbounded-osd-20261010/FINAL-review-v1.md and bound actual receipts; research-wiki/contribution-contracts/'+TASK+'.json. Functor audit:none-found-with-reason.\n')
write(RUN/'PR-plan-v1.json',dict(title='[Online Learning Ch2] Prove unbounded decreasing-step OSD failure',body_path=(RUN/'PR-body-v1.md').as_posix(),body_sha256=sha(RUN/'PR-body-v1.md'),base=pr['headRefName'],head=BRANCH,parent_exact_head=BASE,draft=True,merge=False,deploy=False))
write(RUN/'FINAL-packet-v1.md','''# Required Chapter2 Theorem5.4 dependency FINAL

Review pinned v10 printed52-53/PDF64-65 original pages, Chapter2 pointer, all11actual frozen production BODYs/fourexactdefinitions and FULL7/9conjunct public canaries. Distinct staged neutral/CONTRACT/sevenleaf/fullBODY/canaryBODY/plan/helper reviews and exact RAW history bindings are included. Seven slots: positive-dimensional finite real Euclidean source (Nontrivial necessary);alpha(0,1),exactT>=2/((1-alpha)phi);canonical current-loss singleton-subgradient selector/step/project_fullSpace/iterate/regret;sourceone-basedeta vsLeanzero;initial/comparator0;PREupdate scoring;horizon-specific switching witness firstceilhalf negative/remainderpositive. Learner is fixed causal polynomial schedule, never future-aware existential algorithm. No desired regret/trajectory premise. Scalaridentity worksallalpha,Tincluding0/1; generic step/prefix arbitraryeta. phi source range, exact denominators, leftlimit1-log2>=.3 preserved; totalphi1=1 is not continuity. Unit-direction actual scalar/vector regret equality and exists_norm_eq give complete source existential. Not a minimax-all-learners/oracle/PAC/adaptive/parameterfree result or Chapter5 chapter acceptance. Initial sourcefile documentation is a preserved historical first-leaf/stabilization comment, not a current progress ledger.

Both complete canaries, not partial theorem applications: scalarT2 alpha.5 steps1 and2^(-.5),states0->1->1-2^(-.5),R2=1. T2 belowthresholdtests exactidentity. E2D T64 alpha.5 unitcoordinate/nonzerofirstupdate,globalconvex/Lip1,phi>=1/15,actualthreshold,printedlowerbound,256/15<=R,17<R and fullyappliedsourceexistential. T2/T64 different switching streams/notcommonprefix. Four separately selected compiled conjunction proof VALUES retain scalaridentity,vectorboundtwice,theorem5.4existential. Not mere wholeproof membership, unusedcalls, proofirrelevance or unfolding claim. All actual compile/repair/wrapper failures retained. Frozenheaders/prefix unchanged.

Inspect17public#checks/axioms,13nativefences/safeverify,selected17nodes/3240coalesceddirectTYPE_VALUEpresences/24requiredVALUEpairs/4selectedbranches. Counts are not occurrences/fulltransitive/source-result/chapterdenominator. Actual combinedroot/Tests/fullharness compiler/unittest/exporter/checkmarkers and exact source/root/pin hashes in inspected receipts; exit0 alone nevercompiled. Own actuallookup/referenceindex8outputs/shadow mismatch[]; globalSGB/oldindices/journals untouched. Exactly5reviewed oldpath changes among33852baseline rows, all other baseline RAW preserved; wholeChapter2partial/null,Ch3-16unenumerated/null,all8requiredforwardcontainersOPENpendingdedicatedreconciliation,GoalACTIVE.

CleanlocalSITEv1 atboundcandidatecommit,actualsitecheck; EVERY11026completeoldregistryobjectunchanged+15productionIDs=11041,13sourcecards,noTest/perBookduplicates. Personally view ALL32CURRENT ORIGINAL PNGs listedformula-render-v1-browser.json withview_image detailoriginal and bindhashes; rootview does not discharge yours. ActuallocalfileURI desktop1440/16sourceguideMathJaxformulas/zeroerrors/foldedLean/built-inwrap,all4generatedinputbytesunchanged. NotHTTP/live/mobile/allviewports; no rejectedHTTPservice retry or freshsite-at-later-evidencehead claim.

Separately review prospective record-native-acceptance-v1.py for exact narrow metadata operation AFTER favorable FINAL: verifyFINALreport/manifest/allRAW; only11frozenproofterminalcounter11->0,oneOWNtrial/accepted-event/exactstate; ownjournalunchanged; exactly4namedcontributiontextfields and exactOWNobligation/indexsuffixes. Fourdefinitions tracked separately/notcounter. ExactbeforeRAW/rootaudit retained; distinctpostnative stillrequired. No source/Test/root/reader/contracts mutation; no silent failedretry/assertionweakening. User authorizes scopedcommit/nonforcepush/draftPR; exactplanstacksOPENdraftunmergedPR213. Officialattachment/concrete delivery required, no merge/deploy/retirement/Goalcomplete.

Create-onlyFINAL-review-v1.md/json,report/inputmanifestabsolute+SHA/RAWbeforeafter/32personalpixelhashes,separatesemantic/proof/canary/reader/registry/visual/scope/packageverdictsandrequired_repairs. If acceptable bindnativehelperSHA/approval. RequestedAstra/medium,distinctreusedstagedautomatedactor/relatedhistorydisclosed; nothuman/external/absolute-blind/runtimeattestation. Bounded package only; native/postnative/concretedelivery pending.
''')
capture('FINAL-stage-v1','git','add',*load(RUN/'candidate-stage-plan-v1.json')['stage'])
capture('FINAL-full-package-diff-v1','git','diff','--cached',BASE,'--check')
paths={p for d in [RUN,CONTRACT] for p in d.rglob('*') if p.is_file() and '__pycache__' not in p.parts}
paths.update([PUBLIC,TEST,CONTRIBUTION,PDF,ROOT/'BanditRLProof.lean',ROOT/'Tests.lean',ROOT/'conversion-windows'/(TASK+'.md')])
paths.update(ROOT/d/(TASK+'.md') for d in ['proof-obligations','research-wiki/retrieval-index'])
paths.update(ROOT/p for p in ['lean-toolchain','lakefile.lean','lake-manifest.json','website/content/chapters.json','website/content/readings.json','website/content/highlights.json'])
paths.update(Path(r['path']) for r in load(RUN/'browser-generated-inputs-before-v1.json')['rows'])
fixed()
write(RUN/'FINAL-inputs-v1.json',dict(rows=rows(paths),source_commit=load(RUN/'registry-inspected-v1.json')['source_commit'],production_proof_terminals=11,public_canaries=2,new_definitions=4,additional_selected_Test_auxiliaries=0,source_container_closed=False,chapter_proof_total=None,chapter_complete=False,whole_Goal='ACTIVE'))
print('Exact FINAL packet prepared; distinct semantic/pixel/narrow-native review pending.',flush=True)
