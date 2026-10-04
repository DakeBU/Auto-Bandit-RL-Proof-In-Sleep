"""Author the source-qualified scalar calculation in the existing shared registry."""
from pathlib import Path
import json, re

run = Path(__file__).parent
content = Path('website/content')
slug = 'online-optimal-step'
ns = 'BanditRL.OnlineOptimalStep.'
source = 'https://arxiv.org/pdf/1912.13213v10'
boundary = ('This package proves the scalar minimization with its two coefficients fixed. '
    'It does not choose an online step size using future gradients, or minimize actual regret '
    'across trajectories rerun with different eta. The original sharp fixed-step OGD bound, '
    'including its negative terminal-distance term, remains in the shared library. '
    'This calculation minimizes the coarser two-term bound. Chapter 2, the older production '
    'migration and Chapters 3–16 remain required. Compilation, package acceptance, PR delivery '
    'and merged/live status are separate; no merged/live update is claimed.')
notes = ('Real A and B are frozen nonnegative coefficients. The nondegenerate source argmin '
    'requires A>0 and B>0; eta ranges over positive reals. With A=R² the distance adapter '
    'requires R>0 and B>0. Exogenous D,G>0 and natural T≥1 give A=D² and B=G²T; '
    'G names the source L. Real sqrt and division are total, but eta=0 is inadmissible for '
    'the optimization and the online algorithms. No loss sequence or learner is an input '
    'to these scalar functions; actual OGD/OSD regret guarantees are proved separately.')
rows = [
 ('gap_identity','Exact square gap above the scalar minimum',r'F(\eta)-\sqrt A\sqrt B=(\sqrt A-\eta\sqrt B)^2/(2\eta)',
  'For nonnegative frozen coefficients and a positive step, the exact excess is a nonnegative square quotient.',
  'Use the square identities for real square roots, clear the positive denominator, and expand.',[],False),
 ('lower_bound','Every positive step has the scalar lower bound',r'\sqrt A\sqrt B\le F(\eta)',
  'The square gap is nonnegative for every positive eta, including either zero coefficient.',
  'Apply the gap identity and nonnegativity of its quotient.',[ns+'gap_identity'],False),
 ('optimal_positive','The nondegenerate optimizer is admissible',r'A,B>0\Longrightarrow\eta_*={\sqrt A}/{\sqrt B}>0',
  'Both strictly positive coefficients are needed for the source optimizer to be a positive step.',
  'Real square roots of positive inputs and their quotient are positive.',[ns+'optimalStep'],False),
 ('optimal_value','The optimizer attains the scalar lower bound',r'F(\eta_*)=\sqrt A\sqrt B',
  'At the positive square-root ratio, the exact square gap vanishes.',
  'Cancel the nonzero square-root denominator in the gap identity.',[ns+'gap_identity',ns+'optimal_positive'],False),
 ('optimal_unique','Equality characterizes the positive optimizer',r'F(\eta)=F(\eta_*)\iff\eta=\eta_*\quad(A,B,\eta>0)',
  'When both coefficients are positive, no other positive step attains the minimum.',
  'A zero square gap forces sqrt A = eta sqrt B; divide by the positive sqrt B.',[ns+'gap_identity',ns+'optimal_value'],False),
 ('source_argmin','The source unnumbered scalar minimization',r'\eta_*>0,\quad F(\eta_*)=\sqrt{AB},\quad\forall\eta>0,\ F(\eta_*)\le F(\eta)',
  'The square-root ratio is an attained universal minimum for the two coefficients held fixed.',
  'Combine positivity, attained value and the universal scalar lower bound.',[ns+'optimal_positive',ns+'optimal_value',ns+'lower_bound'],True),
 ('distance_energy_argmin','Comparator-distance and realized-energy calculation',r'\eta_*={R}/{\sqrt B},\quad F(\eta_*)=R\sqrt B\quad(R,B>0)',
  'Substituting the squared comparator distance gives the source algebraic optimizer for a frozen energy.',
  'Rewrite sqrt(R²)=R and apply the same scalar minimum.',[ns+'source_argmin'],True),
 ('diameter_argmin','Optimize the exogenous diameter-gradient upper bound',r'\eta_*={D}/{(G\sqrt T)},\quad F(\eta_*)=DG\sqrt T\quad(D,G>0,T\ge1)',
  'Positive externally supplied D,G and horizon T determine the optimizer of the loose two-term bound.',
  'Substitute A=D² and B=G²T, split the square root of the product and reuse the distance-energy minimum.',[ns+'distance_energy_argmin'],True),
 ('zero_distance_decreases','Zero distance has no positive minimizer',r'B,\eta>0\Longrightarrow F_{0,B}(\eta/2)<F_{0,B}(\eta)',
  'If only the distance coefficient vanishes, halving any positive step strictly improves the scalar cost.',
  'The reciprocal-distance term is zero, leaving a strictly increasing positive linear term.',[ns+'upperBound'],False),
 ('zero_energy_decreases','Zero energy has no positive minimizer',r'A,\eta>0\Longrightarrow F_{A,0}(2\eta)<F_{A,0}(\eta)',
  'If only the energy coefficient vanishes, doubling any positive step strictly improves the scalar cost.',
  'The energy term is zero, so doubling the denominator halves the positive remaining term.',[ns+'upperBound'],False),
 ('zero_coefficients','Both zero coefficients give zero cost',r'F_{0,0}(\eta)=0',
  'Both coefficients zero make the totalized real expression zero; positive-step admissibility is still separate.',
  'Simplify both zero numerator and zero energy term.',[ns+'upperBound'],False),
]
assert len(rows) == 11

def load(n): return json.loads((content/(n+'.json')).read_text(encoding='utf-8'))
def save(p,o):
    with Path(p).open('w',encoding='utf-8',newline='\n') as f:
        json.dump(o,f,ensure_ascii=False,indent=2); f.write('\n')
def item(title,detail,math): return dict(title=title,detail=detail,math=math,fallback=detail)

chapters=load('chapters')
chapter=dict(slug=slug,title='Optimal step size for a frozen scalar bound',short_title='Scalar step-size optimization',
    status='compiled',summary='An attained minimum and its exact equality case for the two-term OGD bound, with explicit positivity and future-feedback boundaries.',
    audience='Readers of Orabona v10, printed page 15.',
    completion_definition='This package closes the unnumbered scalar calculation on printed page 15; it does not close Chapter 2.',
    completion_blockers=['Package acceptance and stacked PR are separately recorded.','Remaining Chapter 2 obligations and the whole-book goal remain mandatory.'],
    learning_goals=['Hold both coefficients fixed when minimizing the expression.','Separate an exogenous D/G/T choice from unavailable future gradient energy.','Check positive denominators and zero-coefficient boundaries.'],
    module_globs=['BanditRLProof/OnlineOptimalStep.lean'],
    open_gaps=['No global regret minimum across eta-dependent reruns is claimed.','Chapter 5 impossibility results remain mandatory later.','Chapter 2 unit scaling and the whole-book program remain incomplete.'])
chapters['chapters']=[c for c in chapters['chapters'] if c['slug']!=slug]+[chapter]
save(content/'chapters.json',chapters)
highlights=load('highlights')
highlights['highlights']=[h for h in highlights['highlights'] if h.get('chapter')!=slug]
for i,(name,title,math,plain,proof,deps,featured) in enumerate(rows):
    label=('Source unnumbered scalar calculation, instantiated with frozen coefficients.'
        if name in {'source_argmin','distance_energy_argmin','diameter_argmin'} else
        'Library gap, equality or degenerate-case refinement; not a separately printed source theorem.')
    highlights['highlights'].append(dict(full_name=ns+name,title=title,chapter=slug,featured=featured,
        teaching_order=i,plain=plain,math=math,intuition=plain,
        why='Make the source scalar minimum and its admissibility conditions precise.',
        position='Orabona v10 printed 15 / PDF 27. '+label,proof_idea=proof,lean_notes=notes+' '+label,dependencies=deps))
save(content/'highlights.json',highlights)
primary=dict(title='Online Learning: A Modern Introduction Using Convex Optimization',authors='Francesco Orabona',
    edition='arXiv:1912.13213v10, 21 June 2026',
    sections='Section 2.1.2, unnumbered scalar step-size minimization and warning about future gradients; printed 15 / PDF 27',
    pages='printed p. 15; PDF p. 27',pdf_page=27,url=source)
cards=[dict(label='Unnumbered distance-energy scalar minimum',pages='Printed 15 / PDF 27',pdf_page=27,url=source,
    math=r'\min_{\eta>0}\left({R^2\over2\eta}+{\eta B\over2}\right)=R\sqrt B,\quad\eta_*={R\over\sqrt B}',
    fallback='For positive frozen distance R and energy B, the minimum is R sqrt B, attained at R/sqrt B.',
    plain='The displayed calculation holds the comparator distance and realized gradient energy fixed.',
    relationship='Public source_argmin and distance_energy_argmin prove the attained universal scalar minimum. The source explicitly warns that gradients depend on eta and the comparator distance is unavailable. This is not an online learner.',
    contract=dict(model='Scalar minimization of the coarse two-term bound after OGD analysis.',
        assumptions='R>0, B>0, eta>0; A=R² and B=sum of squared gradients are held fixed during this calculation.',
        parameters='Real coefficients. The source uses x1; shared causal iterates use Lean index 0. No learner receives future feedback here.',
        regret='The optimized expression is an upper-bound expression, not actual regret across rerun trajectories.',
        guarantee='An attained universal minimum over positive eta with unique optimizer for positive coefficients.'),
    local_status=dict(status='compiled',label='Actual scalar argmin proofs',boundary=boundary)),
    dict(label='Unnumbered exogenous D/L/T loose-bound minimum',pages='Printed 15 / PDF 27',pdf_page=27,url=source,
    math=r'\min_{\eta>0}\left({D^2\over2\eta}+{\eta G^2 T\over2}\right)=DG\sqrt T,\quad\eta_*={D\over G\sqrt T}',
    fallback='For positive D,G and T≥1, the loose bound is minimized at D/(G sqrt T), with value DG sqrt T.',
    plain='This implementable formula uses externally supplied positive bounds and a positive known horizon.',
    relationship='Public diameter_argmin proves this scalar calculation. Existing public OGD/OSD theorems separately connect the bounds to actual causal algorithm regret. It does not remove their hypotheses or the sharp fixed-step residual.',
    contract=dict(model='Exogenous diameter/gradient/horizon scalar upper bound.',
        assumptions='D>0, G>0 and natural T≥1. A=D², B=G²T. The source names the gradient bound L; Lean names it G.',
        parameters='The scalar theorem requires no domain; using it for OGD/OSD regret requires their existing feasible domain, actual feedback and diameter/gradient hypotheses.',
        regret='Minimum of the coarse positive-step upper-bound expression.',
        guarantee='Positive known-horizon scalar optimizer and value DG sqrt T; no anytime or globally optimal realized-regret claim.'),
    local_status=dict(status='compiled',label='Actual D/G/T scalar minimum',boundary=boundary))]
reading=dict(slug=slug,primary=primary,
    notation=[dict(term='Frozen coefficients',meaning='F(eta)=A/(2 eta)+eta B/2. A and B remain fixed inside the universal scalar comparison.'),
        dict(term='Source future-feedback warning',meaning='Actual g_t depends on eta through the causal iterates. Minimizing with a realized B does not optimize regret after rerunning the algorithm at another eta.'),
        dict(term='Positive and degenerate boundaries',meaning=notes)],
    algorithm=dict(title='Calculate a step from externally supplied positive bounds',kind='scalar calculation, not a new source algorithm',
        steps=[item('Fix the loose coefficients','Use positive supplied D,G and known natural T≥1.',r'A=D^2,\quad B=G^2T'),
            item('Calculate the admissible step','The public positivity assumptions keep the denominator positive.',r'\eta_*={D\over G\sqrt T}>0'),
            item('Apply the existing algorithm theorem','To derive actual regret, retain all hypotheses of the already proved causal OGD/OSD guarantee.',r'F(\eta_*)=DG\sqrt T')],
        pseudocode=dict(title='Exogenous scalar tuning',intro='This is a scalar calculation. Future realized gradient energy is not an input to an online algorithm.',
            formula_label='Known-horizon loose-bound optimizer',math=r'\eta_*={D\over G\sqrt T}',fallback='D/(G sqrt T) for D,G>0 and T≥1.',
            lines=['Receive exogenous positive D,G and a known horizon T≥1.','Check D>0, G>0 and T≥1 so the computed step is positive.','Compute eta = D/(G sqrt T).','Invoke the existing causal OGD/OSD guarantee only with its actual loss, feedback, domain and bound hypotheses.','Evaluate the coarse scalar upper bound at this step as D G sqrt T.'],
            relationship='The sharp fixed-step terminal residual remains in the original shared OGD theorem; scalar minimization here concerns its coarser two-term bound.')),
    teaching_route=[ns+n for n in ['gap_identity','source_argmin','distance_energy_argmin','diameter_argmin']],source_theorems=cards,
    proof_bridge=dict(title='A square gap proves the minimum',summary='Use one exact algebraic identity, then instantiate its fixed coefficients. The teaching route and actual proof-value graph are shown separately.',
        steps=[item(rows[0][1],rows[0][3],rows[0][2]),item(rows[5][1],rows[5][3],rows[5][2]),item(rows[7][1],rows[7][3],rows[7][2]),
            item('Check zero boundaries','One zero coefficient gives strict improvements for every positive eta. T=0 is outside the positive-horizon formula; totalized division at eta=0 is not admissible.',r'A=0<B:\ \eta\mapsto\eta/2;\quad B=0<A:\ \eta\mapsto2\eta')],boundary=boundary),
    worked_example=dict(title='Strict scalar minimum and a genuine future-energy warning',
        intro='Named public canaries instantiate the scalar producers, then use actual projected OGD on the same quadratic losses to check the source warning.',
        steps=[item('A nonzero strict optimum','A=9, B=4 gives eta=3/2 and value 6; eta=1 costs 13/2. Equality holds only at the optimizer.',r'F_{9,4}(3/2)=6<13/2=F_{9,4}(1)'),
            item('Exogenous horizon tuning','D=3,G=2,T=4 gives eta=3/4 and loose-bound value 12; T=1 is also tested.',r'F_{9,16}(3/4)=12'),
            item('Actual same-loss OGD paths','On real unbounded V, initial x0=0 and every loss (x−1)²/2, actual projection and gradient give x1=eta, g0=−1, g1=eta−1.',r'B_2(\eta)=1+(\eta-1)^2'),
            item('Energy varies when rerunning','The same loss sequence gives energy 1 at eta=1 and energy 2 at eta=2. This prevents treating the realized energy as a constant across runs.',r'B_2(1)=1\ne2=B_2(2)'),
            item('Zero horizon is inadmissible for the tuning theorem','At T=0 the totalized D/(G sqrt T) is zero, whereas every positive eta has a strictly better doubled step for A=9,B=0.',r'T=0:\quad D/(G\sqrt T)=0;\quad F_{9,0}(2\eta)<F_{9,0}(\eta)\ (\eta>0)')],
        takeaway='The universal scalar minimum is proved with fixed coefficients; the actual OGD counterexample demonstrates why it cannot select a future-informed online optimizer.',boundary=boundary))
readings=load('readings'); readings['readings']=[x for x in readings['readings'] if x['slug']!=slug]+[reading]
save(content/'readings.json',readings)
books=load('books'); book=next(b for b in books['books'] if b['id']=='online-learning')
ref='teaching:'+slug
if ref not in book['chapter_refs']:book['chapter_refs'].insert(book['chapter_refs'].index('teaching:online-ogd')+1,ref)
book['summary']='Orabona v10 uses one shared Lean graph: Chapter 1 foundations and scoped Chapter 2 convex analysis, causal OGD/OSD, scalar tuning and same-trajectory linearization. Chapter 2 and whole-book obligations remain open.'
save(content/'books.json',books)
for name in ['website/scripts/build_site.py','website/scripts/check_site.py']:
    p=Path(name); s=p.read_text(encoding='utf-8'); anchor='"online-linearization",'
    assert s.count(anchor)==1
    with p.open('w',encoding='utf-8',newline='\n') as f:
        f.write(s.replace(anchor,anchor+'\n'+('        ' if 'check_site' in name else '    ')+ '"'+slug+'",'))
names=[ns+n for n in re.findall(r'^(?:noncomputable )?(?:theorem|def|abbrev) (\w+)',
    Path('BanditRLProof/OnlineOptimalStep.lean').read_text(encoding='utf-8'),re.M)]
assert len(names)==13
affected=['BanditRLProof.lean','BanditRLProof/OnlineOptimalStep.lean']+['website/content/'+f+'.json' for f in ['books','chapters','readings','highlights']]+['website/scripts/build_site.py','website/scripts/check_site.py']
manifest=dict(schema_version='2.0',id='ONLINE-OPTIMAL-STEP-20261004',route='online-learning/chapter-2',frontier_cell=slug,source_facing=True,
    source=dict(kind='book',title=primary['title'],version=primary['edition']+'; SHA256 cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17',anchor=primary['sections'],url=source),
    target='Unnumbered fixed-coefficient scalar minimization, attained unique positive optimizer, distance-energy and exogenous D/G/T adapters, with explicit degenerate/future-feedback boundaries.',
    affected_files=affected,declarations=names,
    reuse_plan=dict(classification='adapt',decision='adapt_existing',searched_existing=['Actual native memory/declaration retrieval and mathlib square-root/API type probes before proof bodies.'],
        reused_declarations=['Real.sq_sqrt','Real.sqrt_mul','Real.sqrt_pos','Real.sqrt_sq'],new_shared_declarations=names,
        known_consumers=['OptimalStepProbe.public_argmin','OptimalStepProbe.unique','OptimalStepProbe.tuned','OptimalStepProbe.zero_horizon_boundary'],
        planned_consumers=['Remaining Chapter 2 acceptance and later adaptive-step analyses.'],no_duplicate_wrapper=True,
        decision_reason='Reuse pinned mathlib scalar sqrt identities; the shared gap identity closes the source minimum. No new per-book project or duplicated projection theory.'),
    reader_contract=dict(source_anchor_visible=True,natural_language_formula_proof=True,hidden_assumptions_visible=True,source_vs_lean_delta_visible=True,lean_folded=True,dependencies_visible=True,remaining_boundary_visible=True),
    semantic_roundtrip=dict(required=True,status='source-reviewed',formalizer='/root',blind_decoder='/root/normal_blind',source_reviewer='/root/source_reviewer',verdict='accepted-with-explicit-delta',
        remaining_semantic_delta='Frozen 11-target contract, neutral blind decoding and actual public bodies/22 canaries accepted. Added named T=0 canary has a preserved prior Test snapshot and requires an additive review overlay. No public target changed; no human/external review claim.'),
    graph_contribution=dict(lean_graph='new-node',overview_graph='updated',functor_hypergraph='none-found-with-reason',functor_reason='Scalar substitution in the same shared graph; no separately certified functor.',focus_targets=names,visual_review='Actual compiled proof-value export and source reader are separately pending.',edge_semantics='formal-solid; overlays-dashed'),
    progress_updates=dict(teaching_route='updated: source-qualified scalar calculation in one registry; Chapter 2 and whole-book obligations remain open.',
        banditrlwiki='no-change-with-reason: this scalar Online Learning calculation adds no new Bandit setting.',results_ledger='no-change-with-reason: Bandit results unchanged; the Online source inventory records this package.',
        roadmap='no-change-with-reason: persistent whole-book Goal remains active; Chapter 2 partial; future chapters unenumerated; historical SGB pointer untouched.',website_surfaces=affected[2:],
        inherited_source_caption='Two unnumbered source calculation cards and eleven individual public notes; gap/equality/zero refinements are not claimed as eleven printed theorems.'),
    truth_boundary=boundary,
    verification=dict(focused_checks=['Actual 11 public proofs and original 22 canaries compile; named T=0 extension and updated 41-name axiom audit separately recorded.'],
        bandit_check='Root 9085 and pre-extension Tests 9224 passed; applicable post-extension Tests/full harness remain separate.',site_build='Use lean-verified only after the applicable combined Lean gate; generated website/_site untouched.',
        site_check='Registry, performance, reader and immutable acceptance are separately pending.',independent_review='Distinct automated blind decoder/source reviewer, medium; no human or external-model review.'),
    contributor=dict(name='Codex for Ji Cheng',role='Formalization and integration; distinct required automated semantic actors, source attribution retained'))
save(Path('research-wiki/contribution-contracts/ONLINE-OPTIMAL-STEP-20261004.json'),manifest)
inventory=Path('docs/contracts/online-book-v1/source-inventory.json'); obj=json.loads(inventory.read_text(encoding='utf-8'))
def walk(o):
    if isinstance(o,dict):
        if o.get('source_id')=='C2-optimal-step':o.update(status='compiled-candidate',lean_name=ns+'source_argmin',lean_names=[ns+'source_argmin',ns+'distance_energy_argmin',ns+'diameter_argmin'],evidence=run.as_posix(),boundary=boundary)
        for v in o.values():walk(v)
    elif isinstance(o,list):
        for v in o:walk(v)
walk(obj);save(inventory,obj)
coverage=Path('docs/contracts/online-book-v1/coverage.json');obj=json.loads(coverage.read_text(encoding='utf-8'))
c2=next(c for c in obj['chapters'] if c['chapter']==2)
c2.update(status='partial-with-compiled-scalar-step-optimization-and-prior-packages',accepted=False,mandatory_count=None,latest_package_evidence=(run/'public-actual-bindings.json').as_posix());save(coverage,obj)
print('Authored one shared source route, eleven public notes, two unnumbered calculation cards and thirteen registry declarations; package candidate only.')
