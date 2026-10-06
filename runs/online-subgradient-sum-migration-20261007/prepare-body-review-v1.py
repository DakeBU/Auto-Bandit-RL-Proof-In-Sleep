"""Bind fresh actual bodies, the whole existing canary, kernel checks and selected graph."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header
run=Path(__file__).parent;task='ONLINE-SUBGRADIENT-SUM-MIGRATION-20261007'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
def write(n,x):
 p=run/n;assert not p.exists(),p;p.parent.mkdir(parents=True,exist_ok=True)
 p.write_bytes((x.rstrip('\n')+'\n' if isinstance(x,str) else json.dumps(x,ensure_ascii=False,indent=2)+'\n').encode('utf-8'))
def gate(label,*args):subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),label,*args],check=True)
labels=['retained-focused-v1-01','public-body-v1-01','public-canary-focused-v1-01','public-all-axioms-v1-01','compiled-public-graph-v1-01','verify-public-fences-v1-01']
for n in labels:assert load(run/(n+'-exit.json'))['exit_code']==0,n
jobs={}
for n in ['retained-focused-v1-01','public-canary-focused-v1-01']:
 m=re.search(r'Build completed successfully \((\d+) jobs\)',(run/(n+'.log')).read_text(encoding='utf-8'));assert m,n;jobs[n]=int(m.group(1))
assert jobs=={'retained-focused-v1-01':3319,'public-canary-focused-v1-01':9091}
freeze=load(run/'draft-freeze-v1.json');public=Path('BanditRLProof/OnlineSubgradientSum.lean')
for group in ['module','whole_old_canary','fixed_shared_files']:
 for p,h in freeze[group].items():assert sha(p)==h,p
for n,h in freeze['headers'].items():assert hashlib.sha256(lean_declaration_header(public,n).encode()).hexdigest()==h,n
r=load(run/'source-contract-receipt-v1.json');assert sha(r['report'])==r['report_sha256']
prior=[]
for row in r['reviewed_files']:
 assert sha(row['path'])==row['sha256'],row['path'];prior.append(row)
write('prior-contract-binding-v1.json',dict(status='passed',rows=prior,original_receipt_immutable=True))
raw=(run/'public-all-axioms-v1-01.log').read_text(encoding='utf-8');assert 'sorryAx' not in raw
matches=re.findall(r"(?:^|\n)'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",raw)
named=load(run/'public-named-declarations-v1.json');names=named['axiom_probe']
assert len(matches)==len(set(names))==29 and {n for n,a in matches}==set(names)
axes={n:[a for a in re.sub(r'\s+','',s).split(',') if a] for n,s in matches}
assert all(set(a)<={'propext','Classical.choice','Quot.sound'} for a in axes.values())
g=load(run/'compiled-public-graph-v1.json');targets=names+named['public_definitions']+named['whole_canary_definitions']
assert g['extraction']['source']=='compiled-environment' and len(g['nodes'])==33 and len(g['edges'])==2844
assert sum(n['kind']=='theorem' for n in g['nodes'])==29 and sum(n['kind']=='definition' for n in g['nodes'])==4
assert all(n['has_value'] for n in g['nodes']) and {n['name'] for n in g['nodes']}==set(targets)
newmap={n['name']:n for n in g['nodes']};oldg=load(run/'compiled-ready-graph-v1.json')
assert all(n==newmap[n['name']] for n in oldg['nodes'])
pairs={(e['source'],e['target']) for e in g['edges'] if e['kind']=='value' or e['also_in_value']};pre='BanditRL.OnlineConvex.'
required=[(pre+a,pre+b) for a,b in load(run/'ready-dependencies-v2.json')['required_value_pairs']]
required.extend([('SumEqualityProbe.'+a,pre+'theorem_2_23_equality') for a in ['actual_three_component_decomposition','outside_domain_both_empty','singleton_family_empty_interior']])
required.extend([('SumRuleProbe.'+a,pre+'theorem_2_23_inclusion') for a in ['quadratic_plus_constraint_support','empty_family_zero_support']])
assert len(required)==22
for pair in required:assert pair in pairs,pair
write('compiled-dependencies-v1.json',dict(status='passed',nodes=33,proof_nodes=29,definition_nodes=4,direct_references=2844,graph_sha256=sha(run/'compiled-public-graph-v1.json'),required_value_pairs=required,ready_10nodes_1146refs_exactly_preserved=True,full_graph_export=False,whole_twenty_canary_proofs_three_definitions_exported=True))
write('public-actual-bindings-v1.json',dict(status='compiled-public-exact-targets-and-whole-genuine-canary',fixed_headers=freeze['headers'],module_sha256=sha(public),complete_definition_fixed=True,retained_proofs=9,retained_definitions=1,new_production_proofs=0,new_test_proofs=0,whole_canary_proofs=20,whole_canary_definitions=3,named_kernel_axes=axes,named_kernel_checks=29,native_guards=9,focused_jobs=jobs,selected_graph_nodes=33,selected_graph_direct_references=2844,public_body_seconds=load(run/'public-body-v1-01-exit.json')['elapsed_seconds'],source_package_accepted=False,chapter_complete=False,goal_complete=False))
write('30_lower_worker-public-evidence-v1.md','Nine unchanged production proofs/one full actual M definition freshly elaborated. Focused 3319 jobs, whole old canary 9091 jobs; 20 old canary proofs/3 definitions byte-exact, no new mathematics or TESTs.29 unique named kernel checks standard foundations or none/no sorryAx; nine native guards separate from builds.33 selected compiled nodes/2844 direct type-value references/22 required actual producer-canary pairs; old10-node1146-reference readiness exact. Three-component nonzero decomposition, last boundary, outside-domain empty, REAL singleton empty interior, quadratic+constraint inclusion and empty-index inclusion genuinely instantiated. Concave fixture proves support absence, not a named nonconvexity theorem or inclusion invocation. Existing nonblocking linter warnings retained. BODY/package gates pending; whole Goal active.')
gate('retained-body-trial-v1',sys.executable,'-X','utf8','tools/bandit.py','trial-log','--task',task,'--role','lower','--kind','build','--status','compiled','--run-id',run.name,'--attempt-id','SUBGRADIENT-SUM-RETAINED-BODIES-V1','--lean',public.as_posix(),'--statement-hash',freeze['headers']['theorem_2_23_equality'],'--reused-declaration',pre+'theorem_2_23_inclusion','--reused-declaration',pre+'theorem_2_23_equality','--verifier-evidence',str(run/'public-body-v1-01.log'),'--progress-class','retrieval-reuse','--notes','Actual9 retained proofs/complete M/whole20canary proofs3definitions/29kernel checks/9guards/33selected nodes2844refs PASS.0newproductionmath or TESTs; BODY/package gates pending, Chapter2/book incomplete.')
packet='''Distinct BODY source review. Requested GPT-6 Astra/medium; actively search for mismatches. Independently hash EVERY public-body-inputs-v1.json row and prior-contract-binding-v1.json row. Write ONLY public-body-review-v1.md/public-body-receipt-v1.json in this run, actor.task=/root/source_reviewer, report raw SHA plus ALL reviewed_files hashes; seven slots ALL nine production targets and complete M. Separate mathematical_repairs from eleven required_reader_corrections. Acceptance BODY only, not package/chapter/Goal.

Read source-intent.md/scoped-contexts.json/actual @types/full unchanged module and whole unchanged 20canary proofs3defs, printed17-18/PDF29-30 exact v10. ONE T2.23 numbered anchor has TWO mandatory branches. Nine retained proofs+one definition are source refinements, ZERO new mathematics/TESTs/registry nodes. Inclusion arbitrary Fintype and only component properness; all queried x, no convexity/closedness/commonfinite/queryfinite. M has actual simultaneous Gi supports and exact sum. Empty-index is an explicit inclusion-only library extension, not source positive-family equality. Generic S is wider than printed proper-function Def2.20: disjoint proper domains give identicallytop aggregate, all vectors formally support while M empty. Never infer aggregate properness from component properness or say this improper S is empty. Ordinary sum agrees with upperAdd when bottom is excluded by actual component properness; mixed infinities differ.

Equality Fin(n+1), every component proper/convex/CLOSED, independently qualifying z in LAST DOMAIN only and all OTHER AMBIENT interiors. Last may be boundary; singleton others condition vacuous but proper/convex/closed retained. All queried x, outside-top allowed; queryfinite and aggregate properness DERIVED. Six vector proofs retain actual finiteD REAL inner-product classes; three scalar proofs have no E; full M definition has no FD; completeness derived/zeroD and zero vectors allowed. Convex real-height epigraph; closed REAL sublevels, not closed domain or smooth finite-part conversion. No causal algorithm/probability/regret/selection oracle.

Review actual inclusion sums individual support inequalities/inner finite sum. Binary stronger helper assumes proper convex/queryfinite/common z, no closedness: construct linear image of epigraph product (spatialdifference, summedheight minus inner(g,secondpoint)); actual aggregate support yields contact/noninterior; accepted shared normal produces NONZERO continuous L. Split spatial part A and height coefficient c; upward height gives c<=0; c=0 would force A=0 via qualifying interior localmax and hence L=0, contradiction. Strict c<0 permits normalization and Riesz, yielding actual p and g-p global component supports, top branches handled before toReal. No assumed decomposition/dual attainment. Main finite-family induction derives prefix convex/proper/interior, aggregate proper and queryfinite from actual aggregate support, then each componentfinite. Binary producer + recursive equality + actual Fin.snoc constructs all Gi and exact sumg. Public CLOSED hypotheses retained and recursively passed, although producer stronger without them.

Actual fresh body elaboration PASS20.094s; focused3319 jobs, whole-canary9091 jobs.29 unique named kernel checks standard3-or-none/no sorryAx; nine native statement guards and full M tokens/all old rawbody/wholecanary/shareddeps/root/Tests/pins fixed. Existing unsuppressed nonblocking linters are not failures. Actual selected33 nodes2844 direct type/value references:9producer proofs1definition plus20canary proofs3defs;22 required producer/canary valuepairs, actualold10nodes1146refs exact. Not full registry export; importing T2.22 module is not an actual direct T2.22 value dependency.

Canaries: two quadratics+interval at0 actual nonzero aggregate -1 and full threecomponent decomposition, last domain boundary0 with other interiors; outside3 both sets empty; REAL singleton indicator{0} empty interior/support7 via full equality; quadratic+constraint support2 via inclusion; concave quadratic proves support absence (does NOT itself invoke inclusion or prove named nonconvexity), vacuous family absence, empty-index zero via inclusion. REAL singleton empty interior not zeroD universal. No new tests/proofs/definitions planned.

CONTRACT accepted with eleven reader obligations; inspect contract-binding-audit-v1.json exact list. Later allowed ONLY leading ordinary ignored source/scope comment retaining ORIGINAL RAW suffix, selected Sum subtrees in three readerJSON/manifest/current evidence. Preserve original FOUR curated links/all TEN canonical links/shared registry10811oldIDsURLs/0newnodes, all other Book subtrees. Current combinedrootTests/fullharness/exact contributor/history/site/browser/FINAL/PR still pending. Existing old20261003 source/gates not inherited current acceptance. Preparation count/path/nonexistentCLI and unexecuted helper versions retained, no mathematical repair concealed; command exit0 not automaticcompiled. Three distinct automated actors requested Astra/medium/honest restricted priorhistory/no humanexternal/runtime attestation. Native command gates separate from file/prompt conventions, global SGB immutable/task-onlyshadow. Exact OPENdraftPR16952c24base/main6847unchanged/no merge/deploy/live/retirement. Legacy6->5ONLYSum after real acceptance/PR; nineOTHERChapter1 legacy contracts/remainingChapter1/2/appendix REQUIRED, Chapter2 totalnull/incomplete/3-16unenumerated/whole Goal ACTIVE. Adjacent Ex2.24 and later remain mandatory, no Chapter3 competitive writing.
'''
write('public-body-review-packet-v1.md',packet)
paths={row['path'] for row in load(run/'contract-source-inputs-v2.json')['rows']}
paths.update(p.as_posix() for p in run.rglob('*') if p.is_file())
paths.update(p.as_posix() for p in Path('docs/contracts/online-subgradient-sum-migration-v1').rglob('*') if p.is_file())
write('public-body-inputs-v1.json',dict(scope='9retainedproofs1fullM/20oldcanaryproofs3defs/29kernelchecks/9guards/33nodes2844refs',source_package_accepted=False,chapter_complete=False,goal_complete=False,rows=[dict(path=p,sha256=sha(p)) for p in sorted(paths)]))
print('Actual nine retained bodies/whole canary/29kernel checks/9guards/33nodes2844refs bound; distinct BODY pending.')
