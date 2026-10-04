"""Author this package's source-qualified route in the shared registry metadata."""
from pathlib import Path
import copy, json, re

run = Path(__file__).parent
content = Path('website/content')
slug = 'online-osd-policy'
ns = 'BanditRL.OnlineSubgradientPolicy.'
ogd = 'BanditRL.OnlineGradientDescent.'
osd = 'BanditRL.OnlineSubgradientDescent.'
source = 'https://arxiv.org/pdf/1912.13213v10'
boundary = ('Actual public proofs and canaries compile locally. This package models a fixed '
    'exogenous deterministic support policy with finite loss/output history and the current '
    'whole loss. Performance needs legality at played points only. Source round1 is Lean0; '
    'output(T) is source x_(T+1). Noncomputable mathematical projection/choice is permitted. '
    'Randomized laws, measurability, independence, executable oracles and anytime tuning are '
    'separate. Final package gates and PR delivery are recorded separately. Chapter2, older '
    'stack migration and Chapters3-16 remain required; no merged/live claim.')
notes = ('Finite-dimensional real inner-product space; shared nonempty closed convex V. '
    'Proper EReal losses exclude bottom and have an ambient finite witness; global supports '
    'are nonempty at feasible points. Properness and actual supports justify finite toReal '
    'loss differences. Only played support membership enters performance. Fixed eta>0 '
    'allows T=0 and unbounded V. Variable steps need T>0 and positive nonincreasing played '
    'steps with pairwise diameter control. Tuning needs D,G,T>0 and actual selected-norm '
    'bounds on the same horizon-prescribed trajectory. Prefix comparisons hold the policy '
    'and initialization fixed; they do not impose independence on external parameters.')

# Each tuple gives its own formula and proof argument, not generic declaration-count prose.
rows = [
 ('history_zero','Initial finite history',r'H_0=(x_1)',
  'The time-zero history has one entry, the prescribed initialization.',
  'Reduce the dependent Nat.rec at zero.',[],False),
 ('history_succ','Append the actual projected update',r'H_{t+1}=H_t\mathbin{\|}\Pi_V(X_t-\eta_tg_t)',
  'The old finite history is preserved and its last entry is the actual projected next point.',
  'Unfold the successor branch of Nat.rec and the last-entry/selected-vector definitions.',[ns+'history'],False),
 ('output_zero','Prescribed first output',r'X_0=x_1',
  'The first output is chosen before any observed loss.',
  'Reduce the initial history and its only coordinate.',[ns+'history_zero'],False),
 ('output_succ','Algorithm2.2 actual update',r'X_{t+1}=\Pi_V(X_t-\eta_tg_t)',
  'Apply the same externally fixed history policy to the actual history and current loss.',
  'Evaluate Fin.snoc at its last coordinate; this yields the update used in every performance theorem.',[ns+'history',ns+'selected'],True),
 ('history_mem','Every stored output is feasible',r'x_1\in V\Longrightarrow\forall i\le t,\ H_t(i)\in V',
  'Feasible initialization and actual nearest projection keep every history coordinate in V.',
  'Induct on time, split the last coordinate from castSucc coordinates, and use projection membership.',[ns+'history_succ',ogd+'project_spec'],False),
 ('output_mem','Current output feasibility',r'x_1\in V\Longrightarrow X_t\in V',
  'The current point is a member of the same domain at every time, even for invalid future data.',
  'Apply history_mem at the last finite coordinate.',[ns+'history_mem'],False),
 ('history_prefix','Finite-history causality',r"(\forall s<t,\ f_s=f'_s,\eta_s=\eta'_s)\Longrightarrow H_t=H'_t",
  'Equal strict-past whole losses and rates give the same actual history for one common policy and initialization.',
  'Induct on time; identify the finite past-function input and old history before applying the same policy.',[ns+'history_succ'],False),
 ('output_prefix','Current output ignores future data',r"(\forall s<t,\ f_s=f'_s,\eta_s=\eta'_s)\Longrightarrow X_t=X'_t",
  'Changing the current or future losses cannot change the already determined output.',
  'Apply congrArg to the last coordinate of history_prefix. External policy parameters remain fixed.',[ns+'history_prefix'],True),
 ('oracle_feedback','Optional off-path law supplies played legality',r'\operatorname{OracleLaw}(p)\Longrightarrow g_t\in\partial f_t(X_t)\ (t<T)',
  'A universal legal oracle is a sufficient adapter, while performance also applies without it.',
  'Query the law on the actual finite history and use output_mem. The main performance hypotheses ask only LegalFeedback.',[ns+'output_mem'],False),
 ('trajectory_finite_loss','Finite played and comparator losses',r'f_t(X_t),f_t(u)\in\mathbb R\quad(X_t,u\in V)',
  'Finite real regret is justified before EReal values are converted with toReal.',
  'Use feasible output membership and the reused proper-function/subgradient finite-value theorem.',[ns+'output_mem',osd+'finite_loss'],False),
 ('one_step_chain','Actual support-to-projection inequality',r'\eta_t(f_t(X_t)-f_t(u))\le\eta_t\langle g_t,X_t-u\rangle\le\frac{\|X_t-u\|^2-\|X_{t+1}-u\|^2+\eta_t^2\|g_t\|^2}{2}',
  'A genuine played global support and positive current step give the full source Lemma2.31 chain.',
  'Instantiate the existing full lemma with the actual selected vector and rewrite output_succ. No desired one-step bound is supplied.',[ns+'output_succ',osd+'lemma_2_31'],True),
 ('one_step','Divide by the positive played rate',r'f_t(X_t)-f_t(u)\le\frac{\|X_t-u\|^2-\|X_{t+1}-u\|^2}{2\eta_t}+\frac{\eta_t}{2}\|g_t\|^2',
  'The two-point potential term follows from the actual source support/projection chain.',
  'Compose both inequalities and multiply through the positive eta; field_simp verifies the denominator identity.',[ns+'one_step_chain'],False),
 ('regret_fixed','Fixed rate with negative terminal',r'R_T(u)\le\frac{\|x_1-u\|^2}{2\eta}+\frac\eta2\sum_{t<T}\|g_t\|^2-\frac{\|X_T-u\|^2}{2\eta}',
  'For eta>0, every horizon including zero, every legal played policy and feasible comparator satisfy the same-run bound; no bounded-domain premise.',
  'Induct on T for the scaled regret. Prefix legality/loss hypotheses restrict to the old run; append the actual one-step chain and cancel its intermediate distance. Divide by eta.',[ns+'one_step_chain',ns+'output_zero'],True),
 ('regret_fixed_coarse','Source constant-rate coarse formula',r'R_T(u)\le\frac{\|x_1-u\|^2}{2\eta}+\frac\eta2\sum_{t<T}\|g_t\|^2',
  'The source printed21 formula is a consequence of the sharper retained-terminal result.',
  'Prove the removed endpoint quotient is nonnegative and weaken the sharp fixed bound.',[ns+'regret_fixed'],False),
 ('regret_variable_bound','Decreasing rates with explicit diameter',r'R_T(u)\le\frac{D^2}{2\eta_{T-1}}+\frac12\sum_{t<T}\eta_t\|g_t\|^2-\frac{\|X_T-u\|^2}{2\eta_{T-1}}',
  'Positive nonincreasing played steps and pairwise distance<=D control the weighted potential; the final denominator uses the last played rate.',
  'Sum the actual one-step inequalities and apply weighted_potential_sum to actual squared output distances, using output_mem and pairwise control.',[ns+'one_step',ns+'output_mem',ogd+'weighted_potential_sum'],False),
 ('regret_variable','Source decreasing-rate diameter branch',r'R_T(u)\le\frac{\operatorname{diam}(V)^2-\|X_T-u\|^2}{2\eta_{T-1}}+\frac12\sum_{t<T}\eta_t\|g_t\|^2',
  'At T>0 a bounded V supplies its actual metric diameter, with the negative endpoint retained.',
  'Instantiate explicit pairwise control with Metric.diam using boundedness and both points in V.',[ns+'regret_variable_bound'],True),
 ('regret_tuned_distance','Tuning for one comparator distance',r'\eta=\frac{D}{G\sqrt T},\ \|x_1-u\|\le D,\ \|g_t\|\le G\Longrightarrow R_T(u)\le DG\sqrt T',
  'D,G,T>0 and a distance bound give a tuned guarantee without requiring the entire domain bounded.',
  'Bound initial squared distance and the actual support energy, discard the nonnegative terminal subtraction, and verify the positive tuned-rate identity with sqrt(T)^2=T.',[ns+'regret_fixed'],False),
 ('regret_tuned','Same tuned run for all comparators',r'\eta=\frac{D}{G\sqrt T}\Longrightarrow\forall u\in V,\ R_T(u)\le DG\sqrt T',
  'One horizon-prescribed policy/trajectory serves every comparator when pairwise distances<=D and the actual selected norms<=G.',
  'Apply the one-comparator tuned theorem with the initial point and arbitrary feasible u. LegalFeedback and the norm bounds refer to this same tuned run.',[ns+'regret_tuned_distance'],True),
 ('canonicalPolicy_legal','The old current chooser is a legal policy',r'\operatorname{OracleLaw}(p_{\rm canonical})',
  'The prior current-function/current-point choice is one member of the general history-policy family.',
  'Use the existing Classical.choose membership theorem at a feasible query with nonempty global supports.',[osd+'currentSubgradient_mem'],False),
 ('canonical_output','Exact canonical trajectory bridge',r'X_t^{p_{\rm canonical}}=\operatorname{iterate}_{\rm old}(t)',
  'The general history implementation recovers the previous canonical recurrence at every time and every input regime.',
  'Induct on time, unfold the same projection update and current selector, and rewrite the previous output equality. No legality or positive-rate premise is needed.',[ns+'output_succ',osd+'iterate'],False),
 ('canonical_selected','Exact canonical selected-vector bridge',r'g_t^{p_{\rm canonical}}=G(f_t,\operatorname{iterate}_{\rm old}(t))',
  'The selected vector agrees exactly with the old currentSubgradient value, including the total-function fallback branch.',
  'Unfold the policy application and rewrite canonical_output.',[ns+'canonical_output',osd+'currentSubgradient'],False),
]
assert len(rows)==21

def load(name):
    return json.loads((content/(name+'.json')).read_text(encoding='utf-8'))
def save(path, obj):
    with path.open('w',encoding='utf-8',newline='\n') as f:
        json.dump(obj,f,ensure_ascii=False,indent=2); f.write('\n')
def item(title,detail,math=None):
    d={'title':title,'detail':detail}
    if math: d.update(math=math,fallback=detail)
    return d

chapters=load('chapters')
chapter={
 'slug':slug,'title':'Projected OSD with legal history-dependent support policies',
 'short_title':'History-dependent OSD','status':'compiled',
 'summary':'An actual finite-history policy recurrence with played-only legality and fixed/decreasing/tuned same-run regret.',
 'audience':'Readers of Algorithm2.2, Lemma2.31 and the Theorem2.13/eq2.1 transfer.',
 'completion_definition':'This package covers arbitrary fixed exogenous deterministic finite-history support policies, exact canonical bridges and their source performance transfer. It is not Chapter2 completion.',
 'completion_blockers':['Final package acceptance and stacked PR delivery are separate recorded gates.','Older-stack migration and remaining Chapter2 targets remain mandatory.'],
 'learning_goals':['Track the actual finite information available when a support is selected.','Distinguish played legality from a stronger off-path oracle law.','Derive real regret and retain the terminal subtraction on the same actual recurrence.'],
 'module_globs':['BanditRLProof/OnlineSubgradientPolicy.lean'],
 'open_gaps':['Randomized adaptive-law APIs and measurability are not established by deterministic prefix causality.','Noncomputable whole-function choices and projection are not an executable oracle.','Whole Chapter2 and Chapters3-16 remain required; no main/live update.']}
chapters['chapters']=[a for a in chapters['chapters'] if a.get('slug')!=slug]+[chapter]
save(content/'chapters.json',chapters)

highlights=load('highlights')
highlights['highlights']=[a for a in highlights['highlights'] if a.get('chapter')!=slug]
for i,(name,title,math,plain,proof,deps,featured) in enumerate(rows):
    highlights['highlights'].append({'full_name':ns+name,'title':title,'chapter':slug,
     'featured':featured,'teaching_order':i,'plain':plain,'math':math,'intuition':plain,
     'why':'Connect source Algorithm2.2 to its genuine selected-vector/projected trajectory and same-run bound.',
     'position':'Orabona v10 printed19-21/PDF31-33; Theorem2.13 and eq2.1 printed13-15/PDF25-27.',
     'proof_idea':proof,'lean_notes':notes,'dependencies':deps})
save(content/'highlights.json',highlights)

readings=load('readings')
primary=copy.deepcopy(next(a for a in readings['readings'] if a['slug']=='online-osd')['primary'])
reading={'slug':slug,'primary':primary,
 'notation':[
  {'term':'Finite policy input','meaning':'At zero-based time t, p receives t whole past losses, t+1 actual outputs, and the current whole loss. The next output is not an input. Policy and initialization are fixed exogenous parameters.'},
  {'term':'Played legality','meaning':'LegalFeedback requires the actual selected vector to be a true global support at every played query. An optional OracleLaw supplies this premise everywhere, but the performance statements do not require off-path legal choices.'},
  {'term':'Finite regret and endpoint','meaning':notes}],
 'algorithm':{'title':'Choose a legal support using the actual finite history','kind':'source algorithm',
  'steps':[item('Output first','The recursion constructs Xt from strict-past losses and rates before observing the current loss.'),
   item('Observe and select','The policy receives actual finite history and current whole loss; played support membership is checked at Xt.'),
   item('Project and append','The shared nearest projection of Xt-eta(t)gt is appended to the same stored history.')],
  'pseudocode':{'title':'Algorithm2.2 with a prescribed finite-history support policy',
   'intro':'All statements refer to this one genuine recursive path. The interface includes every deterministic choice that factors through the displayed finite inputs.',
   'formula_label':'Actual selected vector and update',
   'math':r'g_t=p(t,(f_s)_{s<t},(X_s)_{s\le t},f_t)\in\partial f_t(X_t),\quad X_{t+1}=\Pi_V(X_t-\eta_tg_t)',
   'fallback':'Output the current point, observe the current loss, select a played legal global support from finite history, and project the actual update.',
   'lines':['Fix the shared nonempty closed convex V, feasible x1 and one exogenous policy p.','Initialize the finite history with X0=x1.','For each zero-based t, output its last actual point Xt.','Observe ft and pay its finite value at Xt.','Apply p to strict-past whole losses, actual outputs through Xt and current ft; require gt in the true global support set at Xt.','Append the actual nearest projection of Xt-eta(t)gt to the history.'],
   'relationship':'The stronger universal OracleLaw is optional. Canonical bridges recover the prior current-only chooser exactly; invalid-input fallback is tested separately from valid-source performance.'}},
 'teaching_route':[ns+n for n in ['one_step_chain','regret_fixed','regret_variable','regret_tuned']],
 'source_theorems':[],
 'proof_bridge':{'title':'From played global supports to the source regret transfer',
  'summary':'Actual projection and global supports derive the step inequality; telescoping or weighted potentials apply to the same finite-history run.',
  'steps':[item('Produce finite losses','Properness and a true global support at each feasible query make the played and comparator values finite before toReal conversion.',r'f_t(X_t),f_t(u)\in\mathbb R'),
   item('Derive the full step chain','The actual selected vector satisfies the source support relation. Shared nearest projection and the norm expansion yield Lemma2.31.',rows[10][2]),
   item('Accumulate the same path','Constant rates telescope with a negative final distance. Decreasing rates use the last played eta(T-1) and actual bounded potentials.',rows[12][2]),
   item('Tune one run','D,G,T>0 and actual selected-norm bounds on the prescribed tuned run give DGsqrt(T) for all feasible comparators.',rows[17][2])],
  'boundary':boundary},
 'worked_example':{'title':'Actual history-sensitive policies and nonzero residuals',
  'intro':'Two histories have different first constant losses but the same current absolute loss and output at time1. The policy therefore legally selects opposite supports.',
  'steps':[item('Different histories, real updates','At eta=.5 and x1=.5, A outputs .5,.5,0,.5,0; B outputs .5,.5,1,.5,1. Both have real regret1/2, support energy3 and endpoint contribution1/4 against u=.5.',r'R_4(1/2)=0+\tfrac14\cdot3-\tfrac14=\tfrac12'),
   item('Only played legality is necessary','An explicit off-path policy returns999 at an unvisited flat-loss query, so its OracleLaw is false. Its actual trajectory is identical and it still instantiates fixed and tuned public theorems.',r'\neg\operatorname{OracleLaw}(p),\quad\operatorname{LegalFeedback}(p,4)'),
   item('Nonconstant played steps','Harmonic rates1/(2(t+1)) produce .5,.5,1/4,5/12,13/24. Real regret is1/3, weighted energy13/48, last eta1/8 and endpoint contribution1/144.',r'\eta_{4-1}=\tfrac18,\quad\frac{\|X_4-1/2\|^2}{2\eta_3}=\tfrac1{144}'),
   item('Boundary instances','T0 actually instantiates regret_fixed and cancels two positive1/36 distances. A spike loss has empty support at0; its total-function canonical selected vector and output are0, and played legality is proved false. No performance claim is made for that invalid loss.',r'R_0=\tfrac1{36}-\tfrac1{36}=0;\quad\partial f(0)=\varnothing,\ G(f,0)=0')],
  'takeaway':'A policy may depend on observed history while all regret quantities come from the same actual causal projection recurrence.',
  'boundary':boundary}}
for n in ['one_step_chain','regret_fixed','regret_variable','regret_tuned']:
    _,title,math,plain,proof,_,_=next(a for a in rows if a[0]==n)
    if n=='regret_fixed': assumptions='eta>0, T>=0, feasible x1/u, proper losses with global supports nonempty on V and actual played LegalFeedback; no bounded domain.'
    elif n=='regret_variable': assumptions='T>0, positive nonincreasing played rates, bounded V, feasible x1/u, proper subdifferentiable losses on V and actual played LegalFeedback.'
    elif n=='regret_tuned': assumptions='D,G,T>0, feasible x1, pairwise distances<=D, played proper subdifferentiable losses, actual legal selected vectors of norm<=G on this same tuned run.'
    elif n=='one_step_chain': assumptions='eta(t)>0, proper current loss subdifferentiable on V, actual selected global support at Xt, feasible u. No current/initial feasibility premise is added to this single-step lemma.'
    else: assumptions='Fixed shared domain/policy/initialization. Structural equalities need no source legality, rate positivity or loss propriety. Prefix equality requires equal strict-past whole loss functions and step values.'
    reading['source_theorems'].append({'label':title,'pages':primary['pages'],'pdf_page':31,'url':source,'math':math,'fallback':plain,'plain':plain,'relationship':proof,
     'contract':{'model':'Finite-dimensional real Euclidean path with the shared nearest projection and finite-history support policy.','assumptions':assumptions,'parameters':notes,'regret':'Finite real played loss minus finite comparator loss, summed over t<T. Structural equalities are stated directly.','guarantee':plain},
     'local_status':{'status':'compiled','label':'Actual public source-policy proof','boundary':boundary}})
readings['readings']=[a for a in readings['readings'] if a.get('slug')!=slug]+[reading]
save(content/'readings.json',readings)

books=load('books')
book=next(b for b in books['books'] if b['id']=='online-learning')
if 'teaching:'+slug not in book['chapter_refs']:
    book['chapter_refs'].insert(book['chapter_refs'].index('teaching:online-guessing-osd')+1,'teaching:'+slug)
book['summary']='Orabona v10: Chapter1 foundations and scoped Chapter2 convex analysis, causal gradient/subgradient algorithms, history-dependent played-legal policies and absolute-loss guessing. Chapter2/whole-book obligations remain open; all Books reference one shared Lean declaration graph.'
save(content/'books.json',books)
for f in ['website/scripts/build_site.py','website/scripts/check_site.py']:
    p=Path(f);s=p.read_text(encoding='utf-8')
    anchor='"online-guessing-osd",'
    assert s.count(anchor)==1
    s=s.replace(anchor,anchor+'\n'+('        ' if 'check_site' in f else '    ')+'"'+slug+'",')
    with p.open('w',encoding='utf-8',newline='\n') as out:out.write(s)

manifest=json.loads(Path('research-wiki/contribution-contracts/ONLINE-GUESSING-OSD-20261004.json').read_text(encoding='utf-8'))
allnames=[ns+n for n in re.findall(r'^(?:theorem|def|abbrev) (\w+)',Path('BanditRLProof/OnlineSubgradientPolicy.lean').read_text(encoding='utf-8'),re.M)]
manifest.update(id='ONLINE-OSD-POLICY-20261004',frontier_cell=slug,
 target='Algorithm2.2 deterministic finite-history legal-support family, full source step chain and same-run fixed/decreasing/tuned regret; canonical identity bridges',
 affected_files=['BanditRLProof.lean','BanditRLProof/OnlineSubgradientPolicy.lean']+['website/content/'+f+'.json' for f in ['books','chapters','readings','highlights']]+['website/scripts/build_site.py','website/scripts/check_site.py'],
 declarations=allnames,truth_boundary=boundary)
manifest['source']['anchor']='Algorithm2.2 printed20/PDF32, Lemma2.31/transfer printed19/PDF31, constant-rate formula printed21/PDF33; Theorem2.13/eq2.1 printed13-15/PDF25-27'
manifest['reuse_plan'].update(searched_existing=['Actual native declaration search and frozen context/signature probe before tactics.'],
 reused_declarations=[osd+'lemma_2_31',osd+'finite_loss',osd+'currentSubgradient_mem',ogd+'weighted_potential_sum',ogd+'project_spec'],
 new_shared_declarations=allnames,
 known_consumers=['OSDPolicyProbe.history_changes_actual_support','OSDPolicyProbe.offPath_actual_fixed','OSDPolicyProbe.harmonic_actual_variable','OSDPolicyProbe.zero_horizon_actual_fixed'],
 planned_consumers=['Remaining Chapter2 source targets and accepted older-stack migration.'],
 decision_reason='Reuse the shared source support/projection theory, add an actual finite-history policy recurrence and derive its performance from played membership; no duplicated per-Book project or assumed regret consumer.')
manifest['semantic_roundtrip'].update(status='accepted',blind_decoder='/root/normal_blind',
 remaining_semantic_delta='Clean v3 blind contract reconstruction and actual public-body review accepted with explicit source deltas. Added fallback/T0 canaries have a separate body overlay; final reader/raw bindings/package gates remain separate. No external human/model review.')
manifest['graph_contribution'].update(focus_targets=allnames,
 functor_reason='The same Euclidean projection/support mechanism with a broader finite-feedback policy interface; no separately certified cross-setting functor.',
 visual_review='Native proof-value graph export and complete rendered reader checks are separate actual run artifacts, pending at authoring time.')
manifest['progress_updates'].update(teaching_route='updated: source-qualified Algorithm2.2 policy family and sharp source performance in the same registry; Chapter2/whole Book remain incomplete.',
 inherited_source_caption='Existing source-caption and folded-Lean renderer inherited; this route has individual formulas/proof arguments for all21 theorems and required algorithm pseudocode.',
 results_ledger='no-change-with-reason: Bandit results unchanged; Online source inventory carries the scoped package.',
 roadmap='no-change-with-reason: persistent whole-book Goal remains active, Chapter2 partial, future chapters unenumerated and historical SGB pointer untouched.')
manifest['verification']={'focused_checks':['Actual public21 bodies and74canaries, unchanged source hashes and real public axioms.'],
 'bandit_check':'Combined root/Tests/full harness are separate real receipt gates.',
 'site_build':'Run lean-verified only after the applicable combined gate; no generated _site edits.',
 'site_check':'Shared registry exact headers, complete source reader, graph/schema/performance and final byte bindings must pass.',
 'independent_review':'Distinct automated neutral decoder and source reviewer; first body receipt and additional canary overlay scoped separately. No external human review.'}
save(Path('research-wiki/contribution-contracts/ONLINE-OSD-POLICY-20261004.json'),manifest)
print('authored one shared Book route,21individual theorem highlights,7source cards,30public declarations')
