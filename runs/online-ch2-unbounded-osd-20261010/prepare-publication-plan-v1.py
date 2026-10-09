from common import *
import copy,gzip
fixed()
review=load(RUN/'canary-BODY-review-v1.json')
assert review['verdict'] in ['accepted','accepted-with-explicit-delta'] and not review['required_repairs']
assert sha(review['report'])==review['report_sha256'] and sha(review['input_manifest'])==review['input_manifest_sha256']
for r in load(review['input_manifest'])['rows']:assert sha(r['path'])==r['sha256'],r['path']
st=load(CONTRACT/'stabilized-v1.json')
names=['BanditRL.OnlineUnboundedOSD.'+s for s in ['powerSteps','phi','switchSlope','switchLoss']]+[t['name'] for t in st['targets']]
assert len(set(names))==15
graph={n['name']:n for n in load(RUN/'selected-value-graph-v1.json')['nodes']}
prior=ROOT/'tmp/online-ch2-prescient-source-site-v1/books/registry.json'
receipt=ROOT/'runs/online-ch2-prescient-source-20261010/registry-inspected-v1.json'
old=load(prior);old_receipt=load(receipt)
assert sha(prior)==old_receipt['registry_sha256'] and len(old['nodes'])==11026
write(RUN/'registry-baseline-v1.json.gz',gzip.compress(prior.read_bytes(),mtime=0))
write(RUN/'registry-baseline-binding-v1.json',dict(prior_source=prior.as_posix(),prior_complete_raw_sha256=sha(prior),compressed_snapshot_sha256=sha(RUN/'registry-baseline-v1.json.gz'),prior_actual_registry_receipt=rows([receipt]),source_commit=old['source_commit'],identity=old['identity'],total_shared_nodes=11026,expected_new_canonical_ids=['declaration:'+n for n in names],expected_new_theorems=11,expected_new_definitions=4,expected_total=11041,public_Test_and_generated_Test_excluded=True,scope='Parent PR213 clean local candidate site source7be6929f, preserved complete11026 objects; not a fresh build at later evidence head2f039d55.'))
known={n['id'][len('declaration:'):] for n in old['nodes']}|set(names)
route='online-ogd'
boundary=('This is the required Chapter2 forward dependency on the failure of THIS unprojected OSD algorithm with polynomially decreasing steps, not a lower bound against all learners. '
 'The fixed learner receives only the current loss and point when selecting a subgradient; eta_t=t^(-alpha) is a function of the current index and alpha. The adversarial witness may depend on the chosen horizon T. '
 'Four source witness definitions and eleven proof terminals close one source theorem plus its mandatory phi range/limit and proof dependencies; their count is not a printed-result or chapter denominator. '
 'All eight Chapter2 forward containers remain required/open pending dedicated source reconciliation and chapter gates; Chapter2 is partial with null complete proof denominator, Chapters3-16 remain unenumerated/null, and the Chapters1-16 Goal stays ACTIVE. '
 'Positive dimension is source-implicit and mathematically necessary: the zero space cannot have positive regret at comparator0. No bounded feasible domain, assumed desired regret, prescribed trajectory, minimax, oracle-distance-energy, PAC, adaptive or parameter-free endpoint is added. '
 'Stacked on OPEN draft unmerged PR213 exact '+BASE+'. No merge, deployment, main/live, CI or retirement claim.')
source=('Orabona, Online Learning: A Modern Introduction Using Convex Optimization, arXiv:1912.13213v10 (2026-06-21), '
 'required Chapter2 forward observation printed14/PDF26; Theorem5.4 printed52-53/PDF64-65. Pinned PDF SHA256 '+PDF_SHA+'. ')
objects=('Use the SAME canonical OnlineSubgradientDescent.currentSubgradient/step/iterate/regret and OnlineHuber.fullSpace, with existing full-space projection identity. '
 'Lean loss t and powerSteps alpha t correspond to source round t+1. State0 is source x1=0, and loss t is paid at state t BEFORE the update to state(t+1). Comparator0 is fixed. '
 'Set m=ceil(T/2)=(T+1)/2 and k=floor(T/2)=T/2; switchSlope is -1 on t<m and +1 afterwards, including a harmless extension beyond the played horizon. ')
source_assumptions=('Finite-dimensional real inner-product E with Nontrivial E (source proof treats dimension1 and embeddings into dimension>=2); 0<alpha<1; '
 'T is a natural number satisfying T>=2/((1-alpha)*phi(alpha)), which implies T>=2. '
 'Initial point/comparator0; unprojected actual OSD with eta_t=t^(-alpha) in source one-based indexing. Losses are real-valued and globally convex and1-Lipschitz. '
 'There exists a horizon-specific loss sequence; the learner is the fixed causal recursion, not an existential algorithm with access to future losses. ')
canaries=('Public Test scalar_actual_two_rounds proves eta0=1,0<eta1<eta0, actual states0->1->1-2^(-1/2), and pre-update two-round regret=1. T2 is below the source threshold and tests the exact identity rather than the asymptotic lower bound. '
 'finiteDim_source_lower_bound uses E=EuclideanSpace R(Fin2), unit first-coordinate direction and alpha=1/2,T64; it proves a nonzero first update, convexity/Lipschitz1, phi(1/2)>=1/15, the actual threshold, the printed bound,256/15<=R and17<R, and the fully applied source existential. '
 'The T2 and T64 witnesses have different switching times, so they are different loss streams, not common prefixes. '
 'Four independently selected compiled conjunct values retain the new scalar identity, vector lower bound twice, and complete theorem5.4 respectively; no unused theorem call is offered as numeric evidence. ')
specs=[
 ('Polynomially decreasing played steps','Definition, not a separately numbered theorem. All real alpha and natural t; no alpha restriction or dimension. The positive base t+1 avoids zero to a negative exponent.',
  r'\eta_t=(t+1)^{-\alpha}\quad(t\in\mathbb N_0).',
  'The definition only uses alpha and the current index. powerSteps_pos proves every step positive, while the source lower bound later restricts alpha to(0,1).'),
 ('The exact source coefficient phi','Definition on all real alpha using Lean total real division/power; source semantics and positivity are restricted to0<alpha<1.',
  r'\phi(\alpha)=\frac1{2-\alpha}+\frac{(1/2)^{1-\alpha}-1}{1-\alpha}.',
  'Preserve both denominators and the exact source expression. phi_range proves the source codomain, and phi_limit proves its left limit. Total phi(1)=1 is not its left limit, so no continuity at1 is claimed.'),
 ('The horizon-dependent adversarial signs','Definition for natural horizon T and natural t, including T0. This is the loss witness, not a horizon-dependent choice of learner.',
  r'c_t=\begin{cases}-1&t<\lceil T/2\rceil,\\+1&t\ge\lceil T/2\rceil.\end{cases}',
  'Split the first ceil(T/2) played losses and remaining floor(T/2) losses. The all-natural extension is only a total representation of a finite source sequence.'),
 ('Embed the switching losses along one direction','Definition in a real inner-product space E, no dimension or unit-norm premise; T,t natural, v,z arbitrary. Unit norm enters the regularity theorem.',
  r'\ell_t(z)=c_t\langle v,z\rangle.',
  'Use one canonical witness on E. In dimension1 with v=1 this is exactly the source sequence of -x and+x; a unit vector embeds the same scalar regret into a positive-dimensional E.'),
 ('The actual affine subgradient selector','Any real inner-product E; arbitrary a,x in E and real intercept b. No completeness, finite dimension, step or convexity premise is needed.',
  r'\operatorname{currentSubgradient}(z\mapsto\langle a,z\rangle+b,x)=a.',
  'The existing affine_subdifferential theorem identifies the global source subdifferential with the singleton{a}. The actual classical selector chooses a member of that singleton. No new oracle or desired-bound premise is introduced.'),
 ('One actual full-space affine update','Finite-dimensional real inner-product E; arbitrary real eta (including zero/negative), arbitrary a,x,b. Positive steps are only required at the source lower-bound endpoint.',
  r'\operatorname{step}_{E,\eta}(\langle a,\cdot\rangle+b,x)=x-\eta a.',
  'Unfold the SAME step, replace its actual selector by currentSubgradient_affine, then use the existing full-space projection identity. This derives the update rather than assuming a one-step regret inequality.'),
 ('Unroll the same affine recursion','Finite-dimensional real inner-product E; arbitrary eta:N->R,a:N->E,b:N->R,initial x0 and natural t including0. No positive-step or bounded-domain assumption.',
  r'I_t=x_0-\sum_{s=0}^{t-1}\eta_s a_s.',
  'Induct on the actual iterate definition; the successor uses step_affine_fullSpace and sum_range_succ. Only the played prefix appears. The canonical iterate_prefix theorem separately supplies information-causality semantics.'),
 ('Every polynomial step is positive','All real alpha and natural t including0; no restriction alpha in(0,1).',
  r'0<(t+1)^{-\alpha}.',
  'The natural successor has strictly positive real cast; apply Real.rpow_pos_of_pos. The source admissible alpha range is imposed by later theorems, not hidden here.'),
 ('Every constructed loss is globally convex and1-Lipschitz','Finite-dimensional real inner-product E as in the actual API; unit v with norm1, arbitrary T and t. No alpha or horizon threshold.',
  r'\ell_t\text{ convex on }E,\qquad |\ell_t(x)-\ell_t(y)|\le\|x-y\|.',
  'Affine convex-combination equality proves convexity. abs(c_t)=1 and Cauchy-Schwarz with norm(v)=1 prove LipschitzWith1. Regularity is produced for the actual witness, not assumed in the lower bound.'),
 ('Exact scalar regret of the actual run','Real scalar space with initial/comparator0; all real alpha and natural T including0,1. This is an identity with no desired-regret/trajectory premise.',
  r'R_T(0)=-(m-k)\sum_{i=1}^{m}i^{-\alpha}+\sum_{i=1}^{T}i^{1-\alpha}-T\sum_{i=m+1}^{T}i^{-\alpha}.',
  'Unroll the actual affine run, evaluate each PRE-update state, and interchange the finite strict triangular sums using Finset.sum_Ico_Ico_comm\u0027. Split at m, count the suffix signs and factor the polynomial steps. This is the source proof identity for even and odd horizons.'),
 ('The source coefficient has its stated range','Real alpha with0<alpha<1; no horizon or learner premises.',
  r'0<\phi(\alpha)<1-\ln2.',
  'Put beta=1-alpha and q(z)=(1+z)2^{-z}. Strict Bernoulli yields q(beta)>1. Two explicit derivatives show q concave on[0,1], hence its tangent at0 bounds q(beta)-1. Divide by beta(1+beta)>0 to obtain the strict source upper bound.'),
 ('The mandatory endpoint limit and numerical constant','No free parameters; left filter at1. The source interval is(0,1), and the total Lean definition at1 is deliberately not identified with the limit.',
  r'\lim_{\alpha\uparrow1}\phi(\alpha)=1-\ln2\ge\frac3{10}.',
  'Differentiate (1/2)^(1-z) at1 and use HasDerivAt.tendsto_slope on the left punctured filter. The first rational term tends to1; log(1/2)=-log2 gives the limit. The verified mathlib bound log_two_lt_d9 proves the numerical inequality.'),
 ('The printed scalar lower bound','Real alpha with0<alpha<1 and natural T>=2/((1-alpha)phi(alpha)); actual full-space scalar OSD, initial/comparator0, exact switching losses.',
  r'R_T(0)\ge\tfrac12\phi(\alpha)T^{2-\alpha}.',
  'Start from the exact scalar identity. Monotone/antitone sum-integral comparisons and integral_rpow give R>=-T^(1-alpha)/(1-alpha)+phi(alpha)T^(2-alpha). Control ceil/floor parity without discarding odd horizons. The proved horizon threshold absorbs the negative term into half the main coefficient.'),
 ('The same lower bound in a chosen unit direction','Finite-dimensional real inner-product E, any supplied unit v;0<alpha<1 and the exact natural horizon threshold. Unit v already excludes the zero-space instance.',
  r'R_T^{E}(0;\ell_t=c_t\langle v,\cdot\rangle)=R_T^{\mathbb R}(0)\ge\tfrac12\phi(\alpha)T^{2-\alpha}.',
  'Use iterate_affine_prefix to identify the ACTUAL vector states with the scalar coefficient times v. Unit inner-product evaluation identifies the same canonical regrets. Invoke switching_scalar_lower_bound; no arbitrary prescribed vector trajectory is substituted.'),
 ('Theorem5.4: unbounded decreasing-step OSD can fail',source_assumptions,
  r'\exists\ell_1,\ldots,\ell_T\text{ convex and1-Lipschitz}:\quad R_T(0)\ge\tfrac12\phi(\alpha)T^{2-\alpha}.',
  'Positive dimension supplies a unit vector using exists_norm_eq. Choose the actual switching loss witness. switching_loss_regular proves the required global regularity and switching_vector_lower_bound proves the actual run\u0027s regret. The separate phi_range and phi_limit terminals preserve the complete printed theorem content.')]
assert len(specs)==len(names)
notes=[]
for i,(name,spec) in enumerate(zip(names,specs)):
    title,assumptions,formula,proof=spec
    parents=sorted(p for p in graph[name]['value_dependencies'] if p in known and p!=name)
    notes.append(dict(full_name=name,title=title,chapter=route,featured=False,teaching_order=198+i,plain=objects+assumptions,math=formula,intuition=proof,why='Close the actual causal OSD lower-bound dependency required by Chapter2.',position=source+('Source witness definition, not a separately numbered theorem.' if i<4 else 'Derived proof/algorithm interface, not a separately numbered source result.' if i<10 else 'Mandatory Theorem5.4 coefficient range.' if i==10 else 'Mandatory Theorem5.4 left-limit/numerical supplement.' if i==11 else 'Constructive proof of Theorem5.4 for scalar/unit-direction witness.' if i<14 else 'Faithful complete existential Theorem5.4 endpoint, with positive dimension made explicit.'),proof_idea=proof,lean_notes=objects+assumptions+proof+' '+canaries+boundary,dependencies=parents))
card=dict(label='Chapter2 required dependency: Theorem5.4 unbounded decreasing-step OSD failure',pages='printed14,52-53 / PDF26,64-65',pdf_page=64,url='https://arxiv.org/pdf/1912.13213v10',math=specs[-1][2],plain=objects+source_assumptions,fallback=source_assumptions,relationship=source+boundary,contract=dict(model='Same canonical causal OSD recursion on fullSpace, actual affine subgradient selected from its singleton, pre-update scoring.',assumptions=source_assumptions,parameters='Source eta_t=t^(-alpha), Lean eta_t=(t+1)^(-alpha); state0=x1=0; m=ceil(T/2),k=floor(T/2). Exact horizon threshold; no bounded domain.',regret='Comparator0; exact half-phi*T^(2-alpha) lower bound. Supplement phi in(0,1-log2), left limit1-log2>=.3. Not minimax against all algorithms.',guarantee=canaries+boundary),local_status=dict(status='compiled',label='Theorem5.4 dependency compiled; chapter/container reconciliation pending',boundary=boundary))
proposal=dict(route=route,notes=notes,card=card,boundary=boundary,new_module_glob='BanditRLProof/OnlineUnboundedOSD.lean',added_learning_goal='Derive the unbounded polynomially decreasing-step OSD failure from its actual recursion, including phi range/left limit and the exact source horizon threshold.',completion_extension=' Additive required dependency progress: complete Theorem5.4 proof package, not Chapter2 or Chapter5 acceptance. '+boundary)
write(RUN/'reader-proposal-v1.json',proposal)
plans=[]
for rel,line in [('BanditRLProof.lean','import BanditRLProof.OnlineUnboundedOSD'),('Tests.lean','import Tests.OnlineUnboundedOSDCanary')]:
    p=ROOT/rel;raw=p.read_bytes();assert line.encode() not in raw
    before=RUN/('publication-before-'+p.name);after=RUN/('publication-after-'+p.name)
    write(before,raw);write(after,raw+('\n'+line+'\n').encode('utf8'))
    plans.append(dict(path=p.as_posix(),before_snapshot=before.as_posix(),before_sha256=sha(p),after_snapshot=after.as_posix(),after_sha256=sha(after),delta='Exact raw prefix plus single new import.'))
for key in ['chapters','readings','highlights']:
    p=ROOT/('website/content/'+key+'.json');new=copy.deepcopy(load(p))
    before=RUN/('publication-before-'+key+'.json');after=RUN/('publication-after-'+key+'.json')
    write(before,p.read_bytes())
    if key=='chapters':
        row=next(r for r in new['chapters'] if r['slug']==route)
        row['module_globs'].append(proposal['new_module_glob']);row['learning_goals'].append(proposal['added_learning_goal']);row['completion_definition']+=proposal['completion_extension']
    elif key=='readings':next(r for r in new['readings'] if r['slug']==route)['source_theorems'].append(card)
    else:
        assert not any(r['full_name'] in names for r in new['highlights'])
        new['highlights'].extend(notes)
    write(after,new)
    plans.append(dict(path=p.as_posix(),before_snapshot=before.as_posix(),before_sha256=sha(p),after_snapshot=after.as_posix(),after_sha256=sha(after),delta={'chapters':'Only online-ogd append module/goal/completion suffix.','readings':'Only online-ogd append one source-qualified card.','highlights':'Append15canonical production notes; every old note unchanged.'}[key]))
write(CONTRACT/'exact-publication-plan-v1.json',dict(rows=plans,reader_proposal_sha256=sha(RUN/'reader-proposal-v1.json'),allowed_old_mutations=5,all_other_baseline_paths_immutable=True,other_Books_preserved=True,old_links_fields_preserved=True,shared_registry_expected=11041,public_Tests_excluded=True,global_SGB_untouched=True,generated_site_not_edited=True,source_container_closed=False,chapter_complete=False,whole_goal='active'))
write(RUN/'publication-plan-review-inputs-v1.json',dict(rows=rows([CONTRACT/'exact-publication-plan-v1.json',RUN/'reader-proposal-v1.json',RUN/'registry-baseline-binding-v1.json',RUN/'registry-baseline-v1.json.gz',receipt,RUN/'canary-BODY-review-v1.json',RUN/'canary-BODY-review-v1.md',RUN/'full-public-values-inspected-v1.json',RUN/'materialize-publication-v1.py',RUN/'publication_guard_v1.py',PUBLIC,ROOT/'Tests/OnlineUnboundedOSDCanary.lean']+[Path(r[k]) for r in plans for k in ['before_snapshot','after_snapshot']])))
write(RUN/'publication-plan-request-v1.md','''# Separate exact publication plan review

Inspect15new per-target notes (4definitions,11proofs), one source-qualified Theorem5.4 card, all five exact before/after transitions, and complete11026 parent shared registry objects. Classify true helper assumptions: selector arbitrary inner-product E; step/prefix arbitrary eta but finite dimension; identity all alpha,T0/1; source alpha in(0,1)/exact threshold; positive dimension only full existential, or supplied unit v. Distinguish total phi(1)=1 from left limit, ceil/floor odd horizons, real source indexing/current-loss causal algorithm and PRE-update scoring, actual canary T2/T64 different witnesses. No minimax/all-learners/Chapter5 chapter acceptance. All eight Chapter2 containers remain open pending separate reconciliation.

Before/after roots/readers still unmodified. Also review the exact prospective materialize-publication-v1.py and publication_guard_v1.py in this manifest: they must fail closed on all reviewed inputs/plan/body/definition/header hashes and33852baseline except exactly five approved transitions, materialize only those five bytes plus own contribution, no external writes. Review the entire manifest prose including pending combined/site/FINAL states; it does not claim those passed.

Approve exactly five old paths plus own manifest/evidence,15newcanonicalproduction IDs, preserving every complete old registry object, old links/other Books/globalSGB. Local lean-verified site only after actual combined Lean gate; generated website/_site untouched. Output create-only publication-plan-review-v1.md/json,verdict/required_repairs/report+SHA/inputmanifest+SHA/approved_plan_sha256/approved_rows andRAWchecks, and publication_helper_verdict/approved_helper_hashes if acceptable. Not FINAL/package/chapter/Goal,merge/deploy or external/human/runtime attestation. Requested Astra/medium, reused distinct staged actor history disclosed.
''')
fixed()
print('15notes/one source card/five exact old-path transitions prepared, no old source mutation.',flush=True)
