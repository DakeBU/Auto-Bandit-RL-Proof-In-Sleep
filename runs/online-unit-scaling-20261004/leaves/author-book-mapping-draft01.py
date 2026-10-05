"""Map one source unit argument into the existing shared Lean declaration registry."""
from pathlib import Path
import json, re
run = Path(__file__).parent
content = Path('website/content')
slug = 'online-unit-scaling'
ns = 'BanditRL.OnlineUnitScaling.'
source = 'https://arxiv.org/pdf/1912.13213v10'
boundary = ('This package formalizes the unnumbered dimensional argument and coordinate example on printed21–22, '
    'with an explicit transport of the same finite-history policy. Unit exponents are an abstract additive model, '
    'not numerical physical quantities. The numerical algorithm is the shared whole-space causal OSD recurrence. '
    'Invertible transport assumes a fixed c>0; the two real calculus helpers allow arbitrary c. '
    'Structural identities for arbitrary schedules and EReal losses are algebraic, not finite-regret guarantees for improper losses. '
    'The sharp bound requires positive eta, proper full-space subdifferentiable losses and actual played legality, and keeps the negative terminal residual. '
    'Loss-value units are unchanged. No constrained-domain transport, independent canonical-choice equivariance, randomized-law transport or universal worse-regret claim is made. '
    'Chapter2 full acceptance, older production migration and Chapters3–16 remain mandatory. Local compilation and a stacked PR do not update main/live.')
notes = ('E is a finite-dimensional real inner-product space; V is the already shared fullSpace, with actual nearest projection. '
    'New coordinates y=x/c use f′(y)=f(cy), g′=cg and eta′=eta/c². scaledPolicy inverse-transforms only finite past whole loss functions, '
    'the finite played-output tuple and the current whole loss, queries the original fixed exogenous p, then scales its answer by c. '
    'No future loss, comparator or horizon is supplied to p. This is deterministic full-information mathematical choice, not an executable gradient oracle. '
    'Source round1 is Lean0; output at T is the source terminal x_(T+1). T0 is allowed in structural/fixed-positive-step statements; source1/sqrtT requires T≥1.')
rows = [
 ('unit_exponents','The step dimension forced by the update',r'H+(L-X)=X\Longrightarrow H=2X-L',
  'In an additive commutative group of unit exponents, consistency forces the step exponent to be twice the point exponent minus the loss exponent.',
  'Rearrange the additive group equation; addition and subtraction represent physical multiplication and division.',[],False),
 ('regret_unit_exponents','Both coarse regret terms have loss dimension',r'2X-(2X-L)=L,\quad(2X-L)+2(L-X)=L',
  'The squared-distance over step and step times squared-gradient terms both carry the loss exponent.',
  'Cancel the exponent sums in the same additive group model.',[],False),
 ('inverse_loss','Recover the original loss by inverse coordinate pullback',r'f(c(c^{-1}y))=f(y)',
  'A positive coordinate scale has an inverse pullback, even for extended-real losses.',
  'Cancel positive c and its reciprocal pointwise.',[ns+'scaledLoss'],False),
 ('proper_scaled_loss','Coordinate pullback preserves source properness',r'f\text{ proper}\Longrightarrow f(c\cdot)\text{ proper}',
  'The transformed loss is nowhere bottom and inherits an explicit finite witness at x/c.',
  'Transport the original finite witness through inverse scalar multiplication.',[ns+'scaledLoss'],False),
 ('subgradient_scaled','Transport an actual global support',r'g\in\partial f(cy)\Longrightarrow cg\in\partial(f(c\cdot))(y)',
  'For a proper extended-real loss, a global support at the old-coordinate point yields a global support at the new-coordinate point.',
  'Apply the shared affine subgradient inclusion to c times the identity and identify its scalar adjoint.',['BanditRL.OnlineConvex.theorem_2_28'],False),
 ('subdifferentiable_scaled','Preserve full-space subdifferentiability',r'\forall x,\ \partial f(x)\ne\varnothing\Longrightarrow\forall y,\ \partial(f(c\cdot))(y)\ne\varnothing',
  'Properness and support existence at every whole-space point survive positive coordinate conversion.',
  'Transport properness and choose a support at cy, then use support scaling.',[ns+'proper_scaled_loss',ns+'subgradient_scaled'],False),
 ('hasGradientAt_scaled','The real gradient chain rule',r'\nabla_y f(cy)=c\nabla_x f(cy)',
  'A real differentiable loss has the scaled gradient under scalar composition; this calculus identity also allows zero or negative c.',
  'Compose the Frechet derivative with the continuous scalar map and identify the inner-product dual.',[],False),
 ('gradient_scaled','Identify the transformed gradient operator',r'\operatorname{gradient}(f(c\cdot))(y)=c\operatorname{gradient}(f)(cy)',
  'Differentiability at cy identifies the actual mathlib gradient of the composed real function.',
  'Apply the real gradient chain rule and gradient uniqueness.',[ns+'hasGradientAt_scaled'],False),
 ('step_scaling','Correctly scaled steps commute with coordinates',r'c^{-1}(x-\eta g)=c^{-1}x-(\eta/c^2)(cg)',
  'The new-coordinate step eta/c² preserves the same physical update for any supplied vector.',
  'Cancel the positive scalar denominator and distribute scalar multiplication.',[],False),
 ('wrong_step_scaling','Keeping the numerical step changes its physical value',r'c(c^{-1}x-\eta(cg))=x-c^2\eta g',
  'One back-converted uncompensated step has physical step size c² eta.',
  'Distribute scalar multiplication and cancel the coordinate inverse.',[],False),
 ('scaled_eta_positive','Positive steps stay admissible',r'c,\eta_t>0\Longrightarrow\eta_t/c^2>0',
  'At every played time with a positive original step, the transformed step is positive.',
  'The positive square denominator preserves strict positivity.',[ns+'scaledEta'],False),
 ('history_scaling','The entire actual history is preserved',r'H'_t(i)=c^{-1}H_t(i)\quad(i\in\operatorname{Fin}(t+1))',
  'Correct coordinate, loss, schedule and policy transport preserve every point in the actual shared finite history.',
  'Induct on the shared history_succ append, recover observed policy inputs, use full-space projection identity and the scaled step.',[ns+'inverse_loss',ns+'step_scaling','BanditRL.OnlineSubgradientPolicy.history_succ','BanditRL.OnlineHuber.project_fullSpace'],True),
 ('output_scaling','Recover the same physical played point',r'x'_t=c^{-1}x_t',
  'The last element of each matched actual history is the same physical output in different units.',
  'Evaluate the history equality at Fin.last.',[ns+'history_scaling'],False),
 ('selected_scaling','Transport actual policy feedback',r'g'_t=cg_t',
  'The transformed policy selects c times the original selected vector on the matched actual run.',
  'Recover the original finite history and observed loss functions inside scaledPolicy.',[ns+'history_scaling',ns+'inverse_loss'],False),
 ('legal_feedback_scaling','Preserve played-point legality',r'g_t\in\partial f_t(x_t)\Longrightarrow g'_t\in\partial f'_t(x'_t)',
  'Proper losses and original played support legality give legality on the transformed actual trajectory.',
  'Combine actual output and selected-vector correspondence with global support transport.',[ns+'output_scaling',ns+'selected_scaling',ns+'subgradient_scaled'],False),
 ('loss_value_scaling','Played loss values are identical',r'f'_t(x'_t)=f_t(x_t)',
  'Coordinate conversion leaves the actual played extended-real loss value unchanged.',
  'Substitute the matched output and cancel c with its reciprocal.',[ns+'output_scaling'],False),
 ('regret_scaling','The same-run regret is invariant',r'R'_T(u/c)=R_T(u)',
  'The shared converted loss-difference sums match at the converted comparator. Finite performance requires the separate proper/legal assumptions.',
  'Match each actual played loss and comparator loss, then sum the identical converted differences.',[ns+'loss_value_scaling'],True),
 ('wrong_step_output','Identify the actual uncompensated run',r'cx'_t(\eta)=x_t(c^2\eta)',
  'Keeping the numerical new-coordinate step produces the original-coordinate algorithm actually rerun with effective schedule c² eta.',
  'Apply output correspondence to the effective schedule and cancel its transformed schedule. Feedback is regenerated on that actual run.',[ns+'output_scaling'],True),
 ('distance_square_scaling','Squared comparator distance changes by c²',r'\|x/c-u/c\|^2=\|x-u\|^2/c^2',
  'Positive coordinate conversion scales every squared distance by the inverse square.',
  'Use norm of scalar multiplication and positivity of c.',[],False),
 ('energy_scaling','Actual corrected-run gradient energy scales by c²',r'\sum_{t<T}\|g'_t\|^2=c^2\sum_{t<T}\|g_t\|^2',
  'The matched correctly scaled runs have squared selected-vector energy related by c².',
  'Apply actual selected-vector correspondence pointwise and distribute the constant over the finite sum.',[ns+'selected_scaling'],False),
 ('upper_bound_scaling','The numerical coarse bound is invariant',r'F_{A/c^2,c^2B}(\eta/c^2)=F_{A,B}(\eta)',
  'With positive c and eta, both terms of the shared scalar expression retain their numerical value after coordinate conversion.',
  'Cancel the square scaling in each term of the existing upperBound definition.',['BanditRL.OnlineOptimalStep.upperBound'],False),
 ('regret_fixed_scaled','Retain the sharp actual regret guarantee',r'R'_T(u/c)\le{\|x_0-u\|^2\over2\eta}+{\eta\over2}\sum_{t<T}\|g_t\|^2-{\|x_T-u\|^2\over2\eta}',
  'For positive eta and proper full-space subdifferentiable losses with legal played feedback, the transformed run satisfies the same sharp fixed-step bound.',
  'Use actual regret invariance and the shared causal fixed-step producer, keeping its negative terminal-distance term.',[ns+'regret_scaling','BanditRL.OnlineSubgradientPolicy.regret_fixed'],True),
]
assert len(rows)==22
def load(n):return json.loads((content/(n+'.json')).read_text(encoding='utf-8'))
def save(p,x):
    with Path(p).open('w',encoding='utf-8',newline='\n') as f:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
def item(title,detail,math):return dict(title=title,detail=detail,math=math,fallback=detail)

chapters=load('chapters')
assert not any(x['slug']==slug for x in chapters['chapters'])
chapters['chapters'].append(dict(slug=slug,title='Units and actual OSD coordinate transport',short_title='OSD unit scaling',status='compiled',
    summary='Dimension coherence, correctly transported actual histories and regret, and the one-million effective-step example.',
    audience='Readers of Orabona v10, printed21–22.',completion_definition='This package closes the unnumbered units discussion, not Chapter2.',
    completion_blockers=['Package semantic and combined gates are separately recorded.','Full Chapter2 audit and older production migration remain mandatory.'],
    learning_goals=['Separate dimension exponents from numerical coordinate conversion.','Transport the same finite-history policy and all observed inputs.','Keep the sharp negative terminal residual and positive-step boundaries.'],
    module_globs=['BanditRLProof/OnlineUnitScaling.lean'],open_gaps=['No constrained-domain or loss-unit conversion theorem is claimed.','No independent canonical chooser equivariance or universal worse-regret claim.','Whole-book Chapters3–16 remain mandatory.']))
save(content/'chapters.json',chapters)
highlights=load('highlights')
for i,(name,title,math,plain,proof,deps,featured) in enumerate(rows):
    label='One unnumbered source dimensional argument/example, expanded into explicit shared-library obligations; not22 printed theorems.'
    highlights['highlights'].append(dict(full_name=ns+name,title=title,chapter=slug,featured=featured,teaching_order=i,
        plain=plain,math=math,intuition=plain,why='Make units coherent on the actual same-policy OSD trajectory.',
        position='Orabona v10 Section2.2 printed21–22 / PDF33–34. '+label,proof_idea=proof,lean_notes=notes+' '+label,dependencies=deps))
save(content/'highlights.json',highlights)
primary=dict(title='Online Learning: A Modern Introduction Using Convex Optimization',authors='Francesco Orabona',
    edition='arXiv:1912.13213v10, 21 June 2026',sections='Section2.2, unnumbered dimensional analysis and meters-to-kilometers OSD example; printed21–22 / PDF33–34',
    pages='printed pp.21–22; PDF pp.33–34',pdf_page=33,url=source)
cards=[dict(label='Unnumbered dimensional consistency of OSD and its coarse bound',pages='Printed21 / PDF33',pdf_page=33,url=source,
    math=r'[g]=[\ell]/[x],\quad[\eta]=[x]^2/[\ell],\quad[R_T]=[\ell]',fallback='Gradient has loss per point unit; eta has squared-point per loss unit; both regret-bound terms have loss unit.',
    plain='Dimensional consistency of x−eta g determines the step dimension; the two coarse regret terms agree with the loss dimension.',
    relationship='unit_exponents and regret_unit_exponents use an abstract additive exponent model. Numerical coordinate/trajectory theorems are separate.',
    contract=dict(model='Whole-space OSD dimensional consistency; additive exponent abstraction.',assumptions='An additive commutative group of exponents and the update consistency equation. No numerical or probabilistic performance follows from units alone.',parameters='X is point unit exponent, L loss exponent, H step exponent; multiplication/division of units becomes addition/subtraction.',regret='Both coarse bound terms have loss dimension; this is coherence, not a new regret inequality.',guarantee='The exact step exponent and two loss-dimension identities.'),
    local_status=dict(status='compiled',label='Actual dimension identities',boundary=boundary)),
    dict(label='Unnumbered meters-to-kilometers actual OSD example',pages='Printed21–22 / PDF33–34',pdf_page=33,url=source,
    math=r'y=x/1000,\quad g'=1000g,\quad\eta'=\eta/10^6;\quad\eta_{\rm uncompensated}=10^6\eta',
    fallback='Changing meters to kilometers requires dividing eta by one million; the same numerical eta instead multiplies its physical effect by one million.',
    plain='Correct coordinate conversion preserves the entire actual history and regret; uncompensated conversion corresponds to an actually rerun original algorithm at c² eta.',
    relationship='history_scaling/output_scaling/regret_scaling prove the same-run correspondence; wrong_step_output regenerates feedback on the effective-step run. The real chain rule and proper EReal support transport are explicit refinements.',
    contract=dict(model='The shared whole-space causal OSD algorithm with one fixed exogenous support policy.',assumptions='Fixed c>0; structural identities allow arbitrary schedules/losses. The sharp regret bound additionally requires eta>0, proper full-space support existence, and legal actual played feedback.',parameters='The source uses c=1000. The policy receives finite past whole losses, the finite played-output tuple and current whole loss only; no comparator/horizon/future loss input.',regret='Correctly converted comparator u/c and loss-value units unchanged; finite regret interpretation requires the performance hypotheses.',guarantee='Exact actual histories/feedback/regret correspondence, effective schedule c² eta for the uncompensated run, and the sharp fixed-step bound retaining its terminal residual.'),
    local_status=dict(status='compiled',label='Actual causal trajectory and regret transport',boundary=boundary))]
cards[1]['math']=r'y=x/1000,\quad g_{\rm new}=1000g,\quad\eta_{\rm new}=\eta/10^6;\quad\eta_{\rm effective}=10^6\eta'
reading=dict(slug=slug,primary=primary,
    notation=[dict(term='Two separate models',meaning='An additive group records multiplicative unit exponents. Real scalar maps separately convert actual numerical coordinates.'),dict(term='Transported policy',meaning=notes),dict(term='Boundary',meaning=boundary)],
    algorithm=dict(title='Transport the same causal learner into new coordinates',kind='source OSD coordinate conversion with explicit policy refinement',
        steps=[item('Convert coordinates and losses','Use a fixed positive c and inverse coordinates.',r'y=x/c,\quad f'_t(y)=f_t(cy)'),
            item('Convert the step and observed inputs','Divide the step by c² and reconstruct original-coordinate finite observations before querying p.',r'\eta'_t=\eta_t/c^2,\quad g'_t=cg_t'),
            item('Use the actual shared update','The existing nearest projection is identity on the whole space.',r'y_{t+1}=y_t-\eta'_t g'_t')],
        pseudocode=dict(title='Coordinate conversion without future feedback',intro='One fixed exogenous policy is explicitly transported; an independent choice function is not assumed equivariant.',formula_label='Correct step in new coordinates',math=r'\eta'_t=\eta_t/c^2',fallback='eta_new(t)=eta(t)/c² for fixed c>0.',
            lines=['Fix c>0 and convert initialization to x0/c.','Observe finite past whole losses, the finite played-output tuple and the current whole loss in the new coordinates.','Inverse-pull back those observed functions and multiply played points by c before querying the same original policy.','Multiply its returned support by c and use eta(t)/c² in the existing whole-space OSD update.','Compare actual outputs and regret with the converted comparator; retain proper/played-legal and positive-step hypotheses for performance.'],
            relationship='The source1000 example is a special case. Keeping eta numerically unchanged corresponds to the original algorithm actually run with effective schedule c² eta.')),
    teaching_route=[ns+n for n in ['unit_exponents','subgradient_scaled','history_scaling','wrong_step_output','regret_scaling','regret_fixed_scaled']],source_theorems=cards,
    proof_bridge=dict(title='Transport observed inputs, then prove the actual recurrence',summary='Single-step algebra feeds a finite-history induction on the shared algorithm. Teaching links and actual compiled proof-value dependencies are separate.',
        steps=[item(rows[i][1],rows[i][3],rows[i][2]) for i in [4,8,11,16,21]],boundary=boundary),
    worked_example=dict(title='A genuine nonzero one-million path difference',intro='The named canaries use actual current real gradients on the full real line, loss f(x)=x, eta=1 and x0=0.',
        steps=[item('Correctly scale the gradient and step','The actual original gradient is1, the transformed selected vector is1000, and eta_new is1/1000000.',r'g=1,\quad g'=1000,\quad\eta'=10^{-6}'),
            item('Compare actual next outputs','The correctly scaled output is−1/1000; the unchanged numerical step gives−1000, which back-converts to−1000000 meters.',r'y_1^{\rm good}=-1/1000,\quad y_1^{\rm bad}=-1000'),
            item('Keep the sharp endpoint','At u=−2 and T=1 actual regret is2, actual energy is1 and terminal squared distance is1; the sharp RHS is exactly2.',r'R_1=2=4/2+1/2-1/2'),
            item('Check boundaries','c1 preserves output; c0 has no inverse loss identity; T0 fixed-positive-step endpoints cancel but1/sqrt0 is not a positive source schedule.',r'c>0,\quad\eta>0,\quad T\ge1\text{ for }1/\sqrt T')],
        takeaway='Unit conversion preserves the physical learner only when its step and observed policy inputs are transported coherently. A nonzero actual path can change under an uncompensated step; no universal worse-regret statement is made.',boundary=boundary))
readings=load('readings');readings['readings'].append(reading);save(content/'readings.json',readings)
books=load('books');book=next(b for b in books['books'] if b['id']=='online-learning')
book['chapter_refs'].insert(book['chapter_refs'].index('teaching:online-optimal-step')+1,'teaching:'+slug)
book['summary']='Orabona v10 uses one shared Lean graph: Chapter1 foundations and scoped Chapter2 convex analysis, causal OGD/OSD, scalar tuning, coordinate units and same-trajectory linearization. Full Chapter2 and whole-book obligations remain open.'
save(content/'books.json',books)
for name in ['website/scripts/build_site.py','website/scripts/check_site.py']:
    p=Path(name);s=p.read_text(encoding='utf-8');anchor='"online-optimal-step",';assert s.count(anchor)==1
    p.write_text(s.replace(anchor,anchor+'\n'+('        ' if 'check_site' in name else '    ')+'"'+slug+'",'),encoding='utf-8')
names=[ns+n for n in re.findall(r'^(?:theorem|def|abbrev)\s+(\w+)',Path('BanditRLProof/OnlineUnitScaling.lean').read_text(encoding='utf-8'),re.M)]
assert len(names)==26
affected=['BanditRLProof.lean','BanditRLProof/OnlineUnitScaling.lean']+['website/content/'+f+'.json' for f in ['books','chapters','readings','highlights']]+['website/scripts/build_site.py','website/scripts/check_site.py']
manifest=dict(schema_version='2.0',id='ONLINE-UNIT-SCALING-20261004',route='online-learning/chapter-2',frontier_cell=slug,source_facing=True,
    source=dict(kind='book',title=primary['title'],version=primary['edition']+'; SHA256 cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17',anchor=primary['sections'],url=source),
    target='Unnumbered dimensional consistency and actual whole-space coordinate/policy transport, effective uncompensated schedule and sharp fixed-step regret.',affected_files=affected,declarations=names,
    reuse_plan=dict(classification='adapt',decision='adapt_existing',searched_existing=['Actual memory/declaration/mathlib retrieval and API type checks before proof bodies.'],reused_declarations=['BanditRL.OnlineConvex.theorem_2_28','BanditRL.OnlineHuber.fullSpace','BanditRL.OnlineHuber.project_fullSpace','BanditRL.OnlineSubgradientPolicy.history_succ','BanditRL.OnlineSubgradientPolicy.regret_fixed','HasFDerivAt.comp'],new_shared_declarations=names,known_consumers=['UnitScalingProbe.physical_path_difference','UnitScalingProbe.correct_regret','UnitScalingProbe.actual_sharp_bound'],planned_consumers=['Complete Chapter2 semantic/production migration and later invariance analyses.'],no_duplicate_wrapper=True,decision_reason='Use existing whole-space projection, support and actual causal history APIs; no independent per-book project or duplicated public recursion.'),
    reader_contract=dict(source_anchor_visible=True,natural_language_formula_proof=True,hidden_assumptions_visible=True,source_vs_lean_delta_visible=True,lean_folded=True,dependencies_visible=True,remaining_boundary_visible=True),
    semantic_roundtrip=dict(required=True,status='source-reviewed',formalizer='/root',blind_decoder='/root/normal_blind',source_reviewer='/root/source_reviewer',verdict='accepted-with-explicit-delta',remaining_semantic_delta='22 frozen headers/four context definitions accepted; actual body/canary review and combined reader acceptance separately pending. Abstract exponents, proper EReal support/policy transport and sharp/T0 refinements explicit. No human/external review claim.'),
    graph_contribution=dict(lean_graph='new-node',overview_graph='updated',functor_hypergraph='none-found-with-reason',functor_reason='Explicit coordinate transport of the same shared causal recurrence; no separately certified functor.',focus_targets=names,visual_review='Actual compiled dependencies and reader acceptance separately pending.',edge_semantics='formal-solid; overlays-dashed'),
    progress_updates=dict(teaching_route='updated: source-qualified unit argument in the same registry; Chapter2 and whole-book remain incomplete.',banditrlwiki='no-change-with-reason: no new Bandit setting.',results_ledger='no-change-with-reason: Bandit results unchanged; Online source inventory records this package.',roadmap='no-change-with-reason: persistent whole-book Goal active, global historical SGB pointer unchanged.',website_surfaces=affected[2:],inherited_source_caption='Two unnumbered source cards and22 public notes; not22 separately printed source theorems.'),
    truth_boundary=boundary,verification=dict(focused_checks=['Actual22 public proofs and30 canary proofs compile; named axiom gate separately recorded.'],bandit_check='Applicable root/Tests/full harness separately pending.',site_build='Use lean-verified only after the applicable combined gate; generated_site untouched.',site_check='Registry/reader/immutable acceptance separately pending.',independent_review='Distinct required automated semantic actors, requested Astra/medium; no human/external review.'),contributor=dict(name='Codex for Ji Cheng',role='Formalization/integration with distinct required automated semantic actors; source attribution retained'))
save(Path('research-wiki/contribution-contracts/ONLINE-UNIT-SCALING-20261004.json'),manifest)
inventory=Path('docs/contracts/online-book-v1/source-inventory.json');x=json.loads(inventory.read_text(encoding='utf-8'))
row=next(i for i in x['items'] if i['source_id']=='C2-unit-scaling')
row.update(status='compiled-candidate',lean_name=ns+'history_scaling',lean_names=[ns+'history_scaling',ns+'wrong_step_output',ns+'regret_scaling',ns+'regret_fixed_scaled'],evidence=run.as_posix(),boundary=boundary)
save(inventory,x)
coverage=Path('docs/contracts/online-book-v1/coverage.json');x=json.loads(coverage.read_text(encoding='utf-8'))
c2=next(c for c in x['chapters'] if c['chapter']==2);c2.update(status='partial-with-compiled-unit-scaling-and-prior-packages',accepted=False,mandatory_count=None,latest_package_evidence=(run/'public-fence-audit-v1.json').as_posix());save(coverage,x)
print('Shared registry route:26 actual names,22 notes,two unnumbered source cards. Package/chapter/book acceptance pending.')
