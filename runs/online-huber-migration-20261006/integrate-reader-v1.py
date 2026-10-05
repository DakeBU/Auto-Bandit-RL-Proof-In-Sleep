"""Apply eight separately reviewed Huber qualifications; mathematical code stays fixed."""
from pathlib import Path
import hashlib,json,re,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header,_strip_lean_comments
run=Path(__file__).parent;task='ONLINE-HUBER-MIGRATION-20261006'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
def write(p,x,existing=False):
 p=Path(p);assert p.exists() if existing else not p.exists(),p
 with p.open('w',encoding='utf-8',newline='\n') as f:
  if isinstance(x,str):f.write(x.rstrip('\n')+'\n')
  else:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
r=load(run/'public-body-receipt-v1.json');freeze=load(run/'draft-freeze-v1.json')
assert r['actor']['task']=='/root/source_reviewer' and r['verdict'] in ['accepted','accepted-with-explicit-delta']
assert not r.get('mathematical_repairs',r.get('required_mathematical_repairs',[])) and sha(r['report'])==r['report_sha256']
reviewed={row['path']:row['sha256'] for row in r['reviewed_files']}
for row in load(run/'public-body-inputs-v1.json')['rows']:assert reviewed[row['path']]==row['sha256'],row['path']
for p,h in reviewed.items():assert sha(p)==h,p
write(run/'body-binding-audit-v1.json',dict(status='passed',raw_rows=len(reviewed),report_sha256=r['report_sha256'],retained_proofs=19,retained_definitions=3,new_proofs=0,required_reader_corrections=r.get('required_reader_corrections',[])))
snap={row['path']:row for row in load(run/'historical-raw-supersession-v1.json')['rows']}
for p in ['website/content/readings.json','website/content/highlights.json','website/content/chapters.json']:assert sha(p)==snap[p]['raw_sha256']==sha(snap[p]['snapshot']),p
public=Path('BanditRLProof/OnlineHuber.lean');original=(run/'original-OnlineHuber.lean.txt').read_bytes();assert public.read_bytes()==original
comment='''/-
Orabona v10 Example 2.15, printed pp.15-16/PDF pp.27-28. One printed
example; nineteen retained supporting proofs and three complete definitions.
The source's ordinary Huber threshold convention is made explicit as delta>=0,
including delta0; negative thresholds are not convex/differentiable in general.
Actual Complete real Hilbert-space generality includes source finite Euclidean
spaces. Features are available before prediction and labels afterwards; arbitrary
deterministic streams generalize the stock-history illustration without a stock law.
Scalar seam calculus, vector gradient/global convexity, full-space projection
identity and global RegularLoss are produced, not desired consumer hypotheses.
No bounded predictor domain, label/residual bound or diameter condition is added.
The positive fixed-step endpoint retains the negative terminal distance for T>=0.
For T>0, coefficient1 eta_T=1/sqrt(T) is one printed proportional-step instance:
a family of known-horizon constant-step runs, not one anytime eta_t trajectory.
The numerical average upper envelope tends0. The actual signed average regret
is only eventually below every positive epsilon for each fixed comparator;
it can stay negative and need not tend0. No uniform cutoff for unbounded
comparators, moving comparator or Chapter4 strongly-convex guarantee is claimed.
All original headers/proof/definition bytes and whole canary remain fixed.
Chapter2 and the persistent Chapters1-16 Goal remain incomplete.
-/
'''
public.write_bytes(comment.encode('utf-8')+original)
write(run/'public-comment-qualification-v1.json',dict(path=public.as_posix(),original_sha256=hashlib.sha256(original).hexdigest(),qualified_sha256=sha(public),delta='leading ordinary ignored source/scope comment only',exact_original_bytes_retained_as_suffix=True))
p=Path('website/content/readings.json');d=load(p);x=next(row for row in d['readings'] if row['slug']=='online-huber')
x['primary']['sections']='Section2.1.2, ONE printed Example2.15;19 retained supporting proofs and3 complete definitions'
x['notation'][0]['meaning']='H_delta(r)=r²/2 for |r|<=delta and delta*(|r|-delta/2) otherwise. Delta>=0 is an explicit source-implicit threshold convention, not a printed sign inequality; delta0 gives identically zero loss/coincident seams. Negative thresholds lose convexity/differentiability and are outside the algorithm guarantee.'
x['notation'][1]['meaning']='Actual complete real Hilbert-space predictors generalize source finite Euclidean vectors, including an unbounded full-space domain. Norm(z_t)<=Z with Z>=0; arbitrary labels/residuals/initial predictors/comparators have no bound. Source features are past stock opening prices available before prediction; arbitrary deterministic feature/label streams include that illustration without a stochastic stock-law claim. Three full definitions and actual CompleteSpace contexts are retained.'
x['notation'][2]['meaning']='For each positive known horizon T choose one constant eta_T=1/sqrt(T): coefficient1 is a valid instance of source eta proportional to1/sqrt(T), independent of comparator/future labels and gradients. These are separate horizon runs, not one anytime eta_t schedule. Eventual cutoffs depend on fixed u/epsilon and need not be uniform over unbounded comparators.'
x['algorithm']['steps'][0]['detail']='The current point depends only on strict-prefix losses. Current feature z_t is available before predicting inner(z_t,x_t); then y_t is revealed and defines the current residual/loss. Library index0 is source round1, and iterate T is the source point after T updates.'
x['algorithm']['steps'][1]['detail']='Actual seam calculus produces the scalar derivative, including both seams and delta0. The ambient inner-product chain rule then produces gradient H_delta\'(inner(z_t,x)-y_t)*z_t and norm<=delta*norm(z_t); no supplied desired-gradient, label/residual bound or regularity oracle.'
x['algorithm']['steps'][2]['detail']='The genuine nonempty/closed/convex fullSpace Domain has selected projection identity. Global convexity and differentiability PRODUCE RegularLoss fullSpace, discharging the stronger historical API globally. Subtract eta times the current gradient for the next point in the same shared causal recursion; no finite diameter or bounded predictor set.'
assert len(x['notation'])==3 and len(x['teaching_route'])==4 and len(x['source_theorems'])==1
card=x['source_theorems'][0]
card['math']=r'R_T(u)/T\le A/(2\sqrt T),\quad A=\|x_0-u\|^2+(\delta Z)^2,\quad A/(2\sqrt T)\longrightarrow0'
card['fallback']='Only the numeric upper envelope tends0. For each fixed predictor u and epsilon>0, actual average regret is eventually <epsilon; it may stay negative.'
card['plain']='The actual Huber loss produces scalar/vector calculus, full-space regularity and the same causal OGD performance guarantee.'
card['relationship']='ONE printed Example2.15,19retained supporting proofs/3full definitions, zero new proofs/registry nodes. Source finite Euclidean vectors specialize actual Complete real Hilbert-space formulas. Explicit delta>=0 is source-implicit/mathematically necessary, including0, not an arbitrary-real-threshold equivalence. Arbitrary deterministic streams generalize the stock-history illustration with currentfeature-before-prediction/currentlabel-afterwards; no stochastic stock law. Source proportional step is instantiated at coefficient1. Informal approach-to-any-fixed-predictor is reviewed as a ONE-SIDED no-regret comparison, not signed actual average regret Tendsto0 or absolute loss difference vanishing. Actual regret can remain negative. Library index0/source round1 and terminal iterate T/source x_(T+1).'
card['contract']['model']='Actual complete real Hilbert E, including source finite Euclidean R^d; unrestricted full-space predictors, linear feature prediction and exact half-quadratic/linear Huber residual loss.'
card['contract']['assumptions']='Delta>=0 source-implicit threshold; Z>=0 feature norm bound, finite prefix for fixed T or global for eventual claim. No labels/residual/predictor/diameter bound or supplied regularity/gradient/stability/regret oracle. Actual projection identity/global RegularLoss are produced.'
card['contract']['parameters']='Sharp fixed bound: eta>0 and every T>=0. Tuned average: positive known horizon T, coefficient1 constant eta_T=1/sqrt(T), independent of comparator/future feedback. Delta0/Z0 admitted; T0 fixed distance terms cancel, tuned guarantee excludes T0. Generic update identity allows any real eta separately.'
card['contract']['regret']='Actual shared causal iterate from any x0 against each fixed u, sum of current losses minus comparator losses; same horizon run serves all u. Eventual cutoff may depend on u/epsilon; no moving comparator/uniform cutoff.'
card['contract']['guarantee']='Fixed-step actual regret retains -norm(x_T-u)^2/(2eta); dropping only that nonpositive term yields explicit average upper envelope. Numeric envelope Tendsto0; actual average regret only eventually <every positive epsilon, a family of separate known-horizon runs.'
card['local_status']['label']='Retained actual Huber producer/OGD/one-sided average chain, freshly checked'
card['local_status']['boundary']='19retainedproofs3defs/whole14canaryproofs, zero new mathematical code/nodes. Distinct contract/body review and fresh36namedaxes/19guards are separate from combined/root/Tests/harness/site/finalreader/PR acceptance. Chapter2 mandatory total remains null/incomplete and the whole book Goal active; no anytime/strongly-convex guarantee.'
example=x['worked_example']
example['steps'][2]['detail']='For the separate T4 known-horizon run eta=1/sqrt4=1/2, x0=2,u=0,delta=Z=1. The true average upper bound is5/4; this is not equality of realized losses.'
example['takeaway']='Actual seam calculus, nonzero feature geometry and the shared causal full-space update feed a sharp endpoint before the positive-horizon average upper bound.'
example['boundary']='Whole unchanged14proof canary includes upperjoin/bothseams/delta0/interior/exterior; nonzero featuregradient6/bound6/globalconvex/zero threshold; actualstep2→3/2 and sharp negative-residual fixed bound; actualT4average<=5/4 and eventualactualaverage<1/10. No new Lean counterexample proof or literal signed-average convergence is claimed.'
bridge=x['proof_bridge']
bridge['steps'][0]['detail']='Matching seam values/derivatives glue actual adjacent differentiable formulas, producing both seams and coincident delta0. The derivative is a monotone clamp, giving global convexity. Nonnegative threshold is source-implicit; negative thresholds are outside this regularity result.'
bridge['steps'][1]['detail']='The ambient inner-product functional derivative and actual scalar derivative produce the vector gradient, affine-pullback global convexity and norm bound. This actually produces global RegularLoss on univ; labels, residuals and predictors are unrestricted. Actual Complete real Hilbert space includes source Euclidean vectors.'
bridge['steps'][2]['detail']='The full-space Domain is genuinely nonempty/closed/convex and its selected projection is identity. Produced global RegularLoss/true gradient norm bound instantiate the same causal shared fixed-positive-step OGD theorem. Preserve the final negative distance for every T>=0; at T0 initial/final distances cancel. Delta0/Z0 allowed; generic any-real-eta update identity is separate.'
bridge['steps'][3]['detail']='For positive known T, drop only the nonpositive residual, set one constant eta_T=1/sqrtT (source proportionality coefficient1), and divide by T>0. The numeric envelope tends0, giving actual average regret<epsilon eventually for each fixed u. Actual signed average need not tend0; cutoffs need not be uniform over unbounded u. These are separate known-horizon runs, not one anytime schedule.'
bridge['steps'][3]['math']=r'R_T^{(\eta_T)}(u)/T\le A/(2\sqrt T),\quad A/(2\sqrt T)\to0\quad\Longrightarrow\quad\forall\epsilon>0,\;R_T^{(\eta_T)}(u)/T<\epsilon\text{ eventually}'
bridge['boundary']='One printed example/19retained proofs/3full definitions/0newnodes. Mathlib actual seam/chain-rule/monotone-derivative and square-root/inverse-limit APIs plus shared theorem_2_13_fixed; scoped22nodes2954direct type/value references include definitions, not full/canary export. No supplied gradient/regret/regularity consumer, bounded predictor domain, literal signed-average Tendsto0, uniform unbounded-comparator cutoff, anytime or Chapter4 guarantee.'
write(p,d,True)
p=Path('website/content/highlights.json');d=load(p)
for x in d['highlights']:
 if x.get('chapter')!='online-huber':continue
 n=x['full_name'].rsplit('.',1)[-1]
 x['position']='Necessary library support for ONE Orabona v10 Example2.15, printed15–16/PDF27–28; not a separate printed theorem.'
 if n=='huber_convex':
  x['plain']='Produce global convexity from the actual monotone clamp derivative; both seams and delta0 are included.'
  x['proof_idea']='Matching-value/derivative gluing produces actual seam calculus, then the scalar derivative clamp and monotone-derivative criterion prove global convexity.'
  x['lean_notes']='Delta>=0 is source-implicit/mathematically necessary, not a printed sign assumption. Delta0 valid; negative thresholds not convex/differentiable. No strong/strict convexity claim.'
 elif n=='huber_linear_hasGradientAt':
  x['plain']='Derive the ambient gradient of the actual feature-residual Huber loss by the inner-product chain rule.'
  x['proof_idea']='Actual scalar hasDerivAt and innerSL affine functional produce gradient deriv(H)(inner(z,x)-y)*z, without a supplied gradient oracle.'
  x['lean_notes']='Actual Complete real Hilbert-space scope includes finite Euclidean source; arbitrary deterministic streams include stock-history features available before prediction/labels afterwards, without stock-law claim. No labels/residual/predictor/diameter bound; full definition/class contexts fixed.'
 elif n=='huber_regret_fixed':
  x['plain']='Apply shared causal OGD to produced Huber global regularity/actual gradients, retaining the negative terminal distance.'
  x['proof_idea']='Actual global convexity/gradient produce RegularLoss fullSpace, selected projection identity gives the true update, and feature norms bound actual gradients before shared theorem_2_13_fixed.'
  x['lean_notes']='Eta>0,T>=0,delta>=0,Z>=0,finiteprefixfeatures; anyx0/u in unbounded fullspace. At T0 distances cancel;delta0/Z0 retained. Generic update identity anyrealeta separate. No desired stability/regret/regularity consumer or bounded domain.'
 else:
  assert n=='huber_average_eventually'
  x['title']='One-sided eventual upper average regret'
  x['plain']='For each fixed comparator and positive epsilon, actual average regret is eventually below epsilon; only its numeric upper envelope is proved to tend0.'
  x['proof_idea']='Actual sharp fixed endpoint→positive-horizon eta_T=1/sqrtT algebra/drop nonpositive residual→actual average upper bound, then numeric-envelope Tendsto0/positive eventual horizon give literal eventual regret<epsilon.'
  x['lean_notes']='Coefficient1 is one printed proportional choice; separate known-horizon constant-step runfamily, nofutureloss/comparator tuning. Actual signedaverage may staynegative, not Tendsto0/absolute difference; cutoffdependsfixedu/epsilon, no uniformunbounded/movingcomparator/anytime/Chapter4 guarantee.'
 x['intuition']=x['plain'];x['why']='Links actual retained supporting producers to the one printed Example2.15 endpoint in the same shared Lean graph; no new proof-count gain.'
write(p,d,True)
p=Path('website/content/chapters.json');d=load(p);x=next(row for row in d['chapters'] if row['slug']=='online-huber')
x['summary']='One printed Huber prediction example: actual seam/vector calculus and full-space causal OGD, sharp residual regret, and a one-sided known-horizon upper average guarantee.'
x['completion_definition']='ONE Example2.15/19retained supporting proofs/3full definitions/0newproofs or nodes. Scalar/vector/full-space producers, negative-residual fixed bound and literal single-sided eventual average terminal; not completion of Chapter2 or the whole book.'
x['completion_blockers']=['Other mandatory Chapter2 main-text/necessary appendix obligations and historical source migrations still need matching/revalidation; some already have compiled code, so they are not uniformly unproved.','Chapter2 mandatory total remains incomplete/null; Chapters3–16 mandatory unenumerated and persistent whole-book Goal active.']
x['learning_goals']=['Produce actual Huber calculus at both seams and delta0 under explicit source-implicit threshold.','Derive ambient feature gradient/global regularity/full-space projection, without bounded predictors or labels.','Retain the negative fixed-step terminal distance, then use one coefficient1 known-horizon constant-step run per positive T.','Distinguish a vanishing numeric upper envelope from actual one-sided eventual performance; no signed convergence/anytime/uniform cutoff.']
x['open_gaps']=['Chapter2 mandatory remaining matching/migrations/appendix dependencies are required, including already compiled but unaudited modules; current inventory total remains null/incomplete.']
write(p,d,True)
for p,k,key in [('website/content/readings.json','readings','slug'),('website/content/chapters.json','chapters','slug'),('website/content/highlights.json','highlights','chapter')]:
 old=load(snap[p]['snapshot']);new=load(p)
 assert [row for row in old[k] if row.get(key)!='online-huber']==[row for row in new[k] if row.get(key)!='online-huber'],p
 for extra in set(old)-{k}:assert old[extra]==new[extra]
tokens=lambda s:re.sub(r'\s+',' ',_strip_lean_comments(s)).strip()
assert public.read_bytes().endswith(original) and tokens(public.read_text(encoding='utf-8'))==tokens(original.decode('utf-8'))
for n,h in freeze['headers'].items():assert hashlib.sha256(lean_declaration_header(public,n).encode()).hexdigest()==h,n
for p,h in dict(freeze['canary'],**freeze['root_Tests']).items():assert sha(p)==h,p
paths=[public.as_posix(),'website/content/readings.json','website/content/highlights.json','website/content/chapters.json'];names=load(run/'public-named-declarations-v1.json')['public_proofs']+load(run/'public-named-declarations-v1.json')['public_definitions']
c=load('research-wiki/contribution-contracts/online-guessing-migration-20261006.json')
c.update(id=task,frontier_cell='online-huber',target='Distinctly revalidate ONE Example2.15 retained19scalar/vector/fullspace/causal OGD/one-sided average proof chain and3full definitions, then qualify only its existing reader; all mathematical code/wholecanary/root/Tests fixed.',affected_files=paths,declarations=names)
c['source']['anchor']='Example2.15 printed15–16/PDF27–28, one printed Huber prediction example and19necessary retained supporting proofs/3definitions.'
c['reuse_plan']=dict(classification='reuse',decision='reuse_existing',searched_existing=['Fresh actual19public theorem headers/3full definitions/36@types; pinned seam/innerSL/monotone-derivative/sqrt/inverse APIs; same actual shared causal OGD fixed endpoint; fresh compiled22node2954directtype/valueedge graph.'],reused_declarations=names,new_shared_declarations=[],known_consumers=['Tests.OnlineHuberCanary'],planned_consumers=['Later Chapter4 loss-related or Chapter8 prediction source matching only after prior chapter gates; no competing chapter proof writing.'],no_duplicate_wrapper=True,decision_reason='Exact19retainedproofs/3defs/whole14canaryproofs; zero new mathematical code/nodes, one shared underlying registry.')
c['semantic_roundtrip'].update(status='accepted',verdict=r['verdict'],remaining_semantic_delta='Source-implicit delta>=0 including0; actual CompleteHilbert generality; stockillustration versus arbitrarydeterministicstreams; coefficient1 separateknown-horizon family; literal single-sided actualperformance versus numericTendsto. Distinct contract/body accepted, corrected reader/final package pending; nohuman/external/runtime attestation.')
c['graph_contribution'].update(lean_graph='reuse-only',focus_targets=names,functor_reason='Retained Huber calculus and shared OGD instantiation; no separately certified cross-setting functor or graph-derived discovery claim.',visual_review='Actual scoped22nodes2954directtype/valuereferences including3defs, notfull/canaryexport. Same22canonicalnodes/10809oldIDsURLs/0newexpected; registry/site pending.')
c['progress_updates'].update(teaching_route='updated: same online-huber four links/highlights, one source example and actual supporting producers; eight threshold/type/feedback/producer/residual/knownhorizon/one-sided/canary/completion qualifications.',website_surfaces=paths[1:])
c['truth_boundary']='19retainedproofs3defs/whole14canaryproofs/0newmathcode,nodes. Delta>=0 explicitsourceimplicit including0, CompleteHilbert generality/sourceEuclidean, arbitrarydeterministicfeatures/labels with realfeedbackorder/no stocklaw. TrueglobalRegularLoss/fullspaceprojection/gradient producers; no boundedpredictor/label/residual/diameter or gradient/stability/regretoracle. Sharpfixedeta>0 allT>=0 negativefinaldistance/T0cancellation,delta0/Z0admitted. Positiveknownhorizon coefficient1 eta_T=1/sqrtT, numericenvelopeTendsto0 versusactualeventualaverage<epsilon for eachfixedu; no literal signedconvergence/absolute difference/uniformcutoff/movingcomparator/anytime/Chapter4.36namedaxes19guards, actual22nodes2954directreferences notfull/canarygraph; finalgatespending. Chapter1migration/Chapter2null/incomplete/wholeGoalACTIVE;main/liveunchanged.'
c['verification'].update(focused_checks=['Fresh focused/public19body/whole14canary/36named standard3-or-none axiom audit/19native guards passed; all proof and definition tokens/wholecanary/rootTests fixed.'],owned_test_files=[],bandit_check='Fresh explicit sequentialroot/Tests/full harness pending recorded integration.',site_build='Clean lean-verified build only after current applicable combined Lean gate.',site_check='Same22canonicalnodes/10809oldIDsURLs/0new and source-qualified reader checks pending.')
write('research-wiki/contribution-contracts/online-huber-migration-20261006.json',c)
write(run/'reader-integration-v1.json',dict(status='integrated-package-pending',affected_files=paths,selected_route='online-huber',required_reader_corrections_addressed=True,all_other_Book_subtrees_unchanged=True,all_headers_proof_definition_tokens_canary_root_Tests_preserved=True,retained_proofs=19,retained_definitions=3,new_proofs=0,new_registry_nodes=0,source_terminal_accepted=False,chapter_complete=False,goal_complete=False))
with Path('MANIFEST.md').open('a',encoding='utf-8',newline='\n') as f:f.write('\n- Huber migration20261006: ONE Example2.15/19retained proofs3definitions/0newmathcode,nodes; produced seam/vector/globalregularity/fullspace causal OGD/sharp negative residual/knownhorizon one-sided actual average guarantee. Distinct contract/body reviewed; eight reader qualifications, complete36axes/19guards. Fullintegration/reader/PR pending; Chapter2/Book incomplete. See runs/online-huber-migration-20261006.\n')
print('Eight Huber reader qualifications applied; other Books/19proof3definitiontokens/wholecanary/rootTests preserved.')
