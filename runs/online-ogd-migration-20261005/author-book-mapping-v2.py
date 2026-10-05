"""Correct the source-qualified OGD view in the one shared declaration registry."""
from pathlib import Path
import hashlib,json,copy
run=Path(__file__).parent
def load(p):return json.loads(Path(p).read_text(encoding='utf-8'))
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(p,v):
    with Path(p).open('w',encoding='utf-8',newline='\n') as f:
        json.dump(v,f,ensure_ascii=False,indent=2);f.write('\n')
review=load(run/'public-body-receipt-v2.json')
assert review['verdict']=='accepted-with-explicit-delta' and not review['required_repairs']
assert sha(review['report'])==review['report_sha256']
for row in review['reviewed_files']:assert sha(row['path'])==row['sha256'],row['path']
new='BanditRL.OnlineGradientDescentSource.'
old='BanditRL.OnlineGradientDescent.'
boundary=('Compiled local OGD source-repair candidate, with distinct source/body review. '
    'Full harness, actual graph, shared Book registry, final reader/site and PR gates remain separate. '
    'This is not all Chapter2 or the whole book, and is not merged or live.')
regularity=('Convexity on V and a supplied ambient real extension differentiable on an arbitrary '
    'open U containing V. U need not be convex. source_to_feasible proves the conversion to '
    'FeasibleRegularLoss: convexity on V and ambient derivatives at every feasible point. '
    'On a thin V the supplied extension fixes the gradient; extension independence is not claimed.')
readings_path=Path('website/content/readings.json');readings=load(readings_path)
reading=next(x for x in readings['readings'] if x['slug']=='online-ogd')
reading['notation'] += [
    dict(term='SourceRegularLoss → FeasibleRegularLoss',meaning=regularity),
    dict(term='Historical RegularLoss',meaning='The retained historical API requires a convex open '
         'differentiability neighborhood. Its proofs remain valid under that stronger premise; '
         'the source cards below now use the repaired shared declarations.')]
reading['teaching_route']=[old+'iterate',new+'lemma_2_12',new+'theorem_2_13_fixed',new+'equation_2_1']
replacement={old+n:new+n for n in ['lemma_2_12','theorem_2_13_fixed','equation_2_1','theorem_2_13_variable']}
for card in reading['source_theorems']:
    for a,b in replacement.items():card['relationship']=card['relationship'].replace(a,b)
    if not card['label'].startswith('Proposition'):
        card['relationship'] += ' The proved source_to_feasible adapter supplies the source arbitrary-open regularity on the same old projected recurrence.'
        card['contract']['assumptions'] += ' '+regularity
    card['local_status']=dict(status='compiled',label='Compiled local source-repair candidate',boundary=boundary)
    if card['label'].startswith('Lemma'):
        card['relationship']='Exact shared declaration: '+new+'lemma_2_12. Derive the loss comparison from feasible-set convexity and the ambient derivative. Prove the linear gradient, then specialize the retained quadratic projection lemma to the genuine linear loss with this gradient. Both inequalities use the same original step. '+regularity
    if card['label'].startswith('Theorem 2.13: fixed'):
        card['contract']['assumptions']='Nonempty closed convex V, feasible initial point and comparator, eta>0; no bounded-domain premise. '+regularity
        card['contract']['parameters']='Fixed eta and any natural horizon T, including T=0 where the two distances cancel.'
    if card['label'].startswith('Theorem 2.13: positive'):
        card['contract']['assumptions']='Nonempty closed convex bounded V; feasible initial point and comparator; T>=1; positive adjacent nonincreasing prescribed steps. '+regularity
        card['contract']['parameters']='Exact finite Metric.diam V. Both distance denominators use the last played step eta(T-1); D=0 is allowed.'
    if card['label'].startswith('Equation'):
        card['contract']['assumptions']='Nonempty closed convex V, feasible initial point; T,D,G>0; pairwise distances<=D and gradient norms<=G on this actual tuned trajectory. '+regularity
        card['contract']['parameters']='One horizon-prescribed eta=D/(G sqrtT) before the conclusion for all feasible comparators. No zero-parameter or anytime claim.'
reading['worked_example']['boundary'] += (' The repaired endpoints are instantiated in '
    'Tests.OnlineGradientDescentSourceCanary. A separate exact plane canary uses '
    'V={(x,0)}, f(x,y)=max(exp(-x),y), U={y<exp(-x)}. It proves U open/nonconvex, '
    'V unbounded, actual gradient(-1,0) at0 and next(1,0) for eta1, positive regret '
    '1-exp(-2) against(2,0), and terminal square1. This is not a Lean proof that '
    'every alternative convex differentiability neighborhood fails. The horizon-tuned '
    'interval bound does not claim each tuned iterate clips.')
write(readings_path,readings)
chapters_path=Path('website/content/chapters.json');chapters=load(chapters_path)
chapter=next(x for x in chapters['chapters'] if x['slug']=='online-ogd')
chapter['module_globs'].append('BanditRLProof/OnlineGradientDescentSource.lean')
chapter['summary']='The same causal projected algorithm with repaired arbitrary-open source regularity, sharp fixed/decreasing-step regret and fixed-horizon tuning.'
chapter['completion_definition'] += ' Source-facing loss bounds use OnlineGradientDescentSource through the proved arbitrary-open adapter; old RegularLoss declarations retain their stronger scope. Package and chapter gates are distinct.'
chapter['completion_blockers'].append('Current source-repair package final harness/graph/reader/site/PR gates remain pending; historical scope is preserved separately.')
chapter['learning_goals'].append('Distinguish arbitrary open differentiability neighborhoods from the retained stronger convex-neighborhood predicate.')
write(chapters_path,chapters)
highlights_path=Path('website/content/highlights.json');highlights=load(highlights_path)
for node in highlights['highlights']:
    if node['full_name'] in replacement:
        node['title'] += ' (historical stronger interface)'
        node['lean_notes'] += ' Uses RegularLoss with a convex open differentiability neighborhood. The repaired arbitrary-open source endpoint is '+replacement[node['full_name']]+'. Old links and true proofs are retained.'
        node['position']='Historical stronger-assumption interface in the same shared library; source cards use the repaired namespace.'
notes={
 'FeasibleRegularLoss':('Feasible-point loss regularity','Convexity on V and ambient derivatives at every feasible point.',r'\operatorname{ConvexOn}(V,f)\ \land\ \forall x\in V,\ f\text{ differentiable at }x','This is the weaker library interface; boundary/thin-domain points are included.',[]),
 'SourceRegularLoss':('Arbitrary-open source regularity',regularity,r'\exists U\supseteq V:\ U\text{ open},\ f\text{ convex on }V,\ f\text{ differentiable on }U','A supplied ambient extension; not an extension-existence or extension-independence theorem.',[]),
 'source_to_feasible':('Source hypothesis supplies the weaker interface','Every point of V lies in the open differentiability neighborhood.',r'\mathrm{SourceRegularLoss}(V,f)\Rightarrow\mathrm{FeasibleRegularLoss}(V,f)','Openness supplies a neighborhood at each feasible point; DifferentiableOn gives the ambient derivative.',[new+'SourceRegularLoss',new+'FeasibleRegularLoss']),
 'regular_to_feasible':('Compatibility with the historical predicate','The retained stronger predicate also supplies the repaired interface.',r'\mathrm{RegularLoss}(V,f)\Rightarrow\mathrm{FeasibleRegularLoss}(V,f)','Restrict convexity from the old U to convex V and take local ambient derivatives. No reverse implication.',[old+'RegularLoss',new+'FeasibleRegularLoss']),
 'linear_regular':('True linear loss satisfies the stronger interface','The function z ↦ inner(g,z) is globally convex and differentiable.',r'f_g(z)=\langle g,z\rangle','The continuous Riesz dual supplies an actual linear map and derivative, including g=0 and unbounded V.',[old+'RegularLoss']),
 'gradient_linear':('Actual gradient of the linear loss','The gradient of inner(g,·) equals g at every ambient point.',r'\nabla f_g(x)=g','Use the derivative of the continuous dual and the Riesz gradient identity; this is a producer, not an oracle assumption.',[]),
 'first_order':('Feasible-set first-order comparison','Loss comparison follows from convexity on V and the ambient derivative.',r'f(x)-f(u)\le\langle\nabla f(x),x-u\rangle','Apply the existing feasible convex_gradient_lower_bound and reverse the displacement.',[new+'FeasibleRegularLoss','BanditRL.OnlineConvex.convex_gradient_lower_bound']),
 'lemma_2_12':('Lemma 2.12 with source regularity','Both source one-step inequalities hold for the same actual projected update.',r'\eta(f(x)-f(u))\le\eta\langle g,x-u\rangle\le\tfrac12\|x-u\|^2-\tfrac12\|x^+-u\|^2+\tfrac{\eta^2}2\|g\|^2','Proved first-order bound plus genuine affine specialization of the retained quadratic lemma. No assumed one-step bound.',[new+'first_order',new+'linear_regular',new+'gradient_linear',old+'lemma_2_12',old+'step']),
 'theorem_2_13_fixed':('Theorem 2.13 fixed step with source regularity','No bounded-domain premise; the negative terminal distance is retained.',r'R_T(u)\le\frac{\|x_1-u\|^2}{2\eta}+\frac\eta2\sum_t\|g_t\|^2-\frac{\|x_{T+1}-u\|^2}{2\eta}','Sum the actual same-run one-step chain by induction, telescope and divide by eta>0. T=0 is a canceling extension.',[new+'lemma_2_12',old+'iterate_mem',old+'regret']),
 'variable_one_step':('Actual variable-step loss comparison','The current scheduled update supplies its divided one-step inequality.',r'\ell_t(x_t)-\ell_t(u)\le\frac{\|x_t-u\|^2-\|x_{t+1}-u\|^2}{2\eta_t}+\frac{\eta_t}2\|g_t\|^2','Use new lemma_2_12 and actual iterateVariable feasibility; only current eta_t must be positive here.',[new+'lemma_2_12',old+'iterateVariable_mem']),
 'theorem_2_13_variable_bound':('Sharp decreasing-step diameter-upper-bound interface','A pairwise distance upper bound supplies the weighted potential telescope.',r'R_T(u)\le\frac{D^2}{2\eta_T}+\sum_t\frac{\eta_t}2\|g_t\|^2-\frac{\|x_{T+1}-u\|^2}{2\eta_T}','T>=1, positive adjacent nonincreasing used steps; Lean last step is eta(T-1). D=0 allowed. Preserve the negative terminal.',[new+'variable_one_step',old+'weighted_potential_sum',old+'iterateVariable_mem']),
 'theorem_2_13_variable':('Theorem 2.13 exact finite diameter','Boundedness makes Metric.diam the source diameter in the repaired same-run bound.',r'D=\operatorname{diam}(V)','Apply the pairwise-bound producer with Metric.dist_le_diam_of_mem. No compactness or convex-open-neighborhood assumption.',[new+'theorem_2_13_variable_bound']),
 'equation_2_1_distance':('Positive horizon tuning for one comparator','An initial-distance bound and actual tuned-run gradient bounds give DG sqrtT.',r'\eta=\frac{D}{G\sqrt T},\qquad R_T(u)\le DG\sqrt T','D,G,T>0. Bound the initial distance and energy in the fixed sharp producer, then discard the nonnegative terminal magnitude. No future-gradient optimizer.',[new+'theorem_2_13_fixed']),
 'equation_2_1':('Equation (2.1) with arbitrary-open regularity','One prescribed tuned trajectory satisfies DG sqrtT for every feasible comparator.',r'\forall u\in V,\ R_T(u)\le DG\sqrt T','Positive D,G,T, pairwise domain distances<=D, actual tuned-run gradient norms<=G. No comparator-dependent rerun or anytime bound.',[new+'equation_2_1_distance'])}
assert len(notes)==14
for i,(name,(title,plain,math,proof,deps)) in enumerate(notes.items()):
    full=new+name;assert not any(x['full_name']==full for x in highlights['highlights'])
    highlights['highlights'].append(dict(full_name=full,title=title,chapter='online-ogd',
        featured=False,teaching_order=10+i,plain=plain,math='\\('+math+'\\)',intuition=plain,
        why='One repaired source chain using the existing shared projected algorithm.',
        position='Orabona v10 printed12–15/PDF24–27; library refinement, not an extra printed source result.',
        proof_idea=proof,lean_notes=regularity+' '+boundary,dependencies=deps))
write(highlights_path,highlights)
write(run/'book-mapping-v2.json',dict(stage='candidate',shared_registry=True,new_public_nodes=14,
    old_declaration_links_retained=True,old_teaching_slug='online-ogd',new_teaching_slug='online-ogd',
    source_cards=5,printed_source_result_counts_unchanged=True,
    modified_surfaces=['website/content/chapters.json','website/content/readings.json','website/content/highlights.json'],
    books_membership='Existing online-learning teaching:online-ogd route in books.json retained; no per-book library.',
    generated_site_edited=False,Lean_gate='root/Tests and axiom probes passed; full harness pending',
    final_reader_review='pending',chapter_complete=False,goal_complete=False))
print('Fourteen new shared nodes mapped; all old links retained; source cards repaired, full gates pending.')
