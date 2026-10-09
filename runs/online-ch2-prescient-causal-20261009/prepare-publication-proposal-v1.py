from common import *
import copy, gzip
fixed()
candidate = load(RUN / 'complete-candidate-inspected-v1.json')
assert candidate['both_selected_numeric_tails_retain_new_actual_transition']
assert candidate['production_sha256'] == sha(PUBLIC)
assert candidate['test_sha256'] == sha(ROOT / 'Tests/OnlinePrescientBregmanCanary.lean')
route = 'online-ogd'
boundary = ('This package adds eight derived proofs and two exact partial definitions for a required Chapter 2 prescient forward dependency. '
    'It does not complete Algorithm 15.8 or Theorem 15.30, or accept Chapters 6 or 15. '
    'Local ambient-extension equality and the actual current-only partial recursion are now proved; '
    'transport of the source X/interior regularity into a valid generated run, its source interior conditions, '
    'and sharp fixed/variable same-run cumulative bounds remain REQUIRED/OPEN, including the main-text fixed-step exercise. '
    'Earlier package boundary paragraphs describe their respective bounded scopes; the new locality and partial-state results are additive progress. '
    'All eight Chapter 2 forward containers stay open; Chapter 2 is partial, its complete proof denominator remains null, '
    'and the Chapters 1-16 Goal is ACTIVE. Stacked on OPEN draft unmerged PR #210 exact ' + BASE + '. '
    'No merge, deployment, main, live or CI acceptance claim.')
source = ('Orabona, Online Learning, arXiv:1912.13213v10 (2026-06-21): '
    'Chapter 2 prescient observation, printed 14 / PDF 26; properness/subgradients, printed 16-17 / PDF 28-29; '
    'Definition 6.4 and Lemma 6.7, printed 63-64 / PDF 75-76; '
    'Algorithm 15.8 and Theorem 15.30, printed 265-266 / PDF 277-278. PDF SHA256 ' + PDF_SHA + '.')
objects = ('Use the same canonical ordered divergence B_psi(a;b)=psi(a)-psi(b)-Dpsi(b)[a-b], with target first and derivative base second. '
    'The source divergence has domain X times interior X. An ambient total fderiv defaults to zero at nondifferentiable points, '
    'so its boundary values are not licensed as source derivatives. The locality and partial-state proofs use arbitrary real normed vector spaces; '
    'only the actual-transition loss bound retains the accepted parent complete real inner-product context. Finite Euclidean source spaces are included.')
information = ('The whole current loss is received before the played prediction. Lean state0 is source x0; '
    'Lean loss t is source round t+1 and played prediction is state(t+1). This is prescient feedback, '
    'not ordinary OGD prediction before the current loss. The producer consumes one current loss and step through Option.bind. '
    'It receives no horizon, comparator or future-loss oracle. Classical choice is noncomputable mathematical selection, '
    'not an executable optimizer or a measurable-selection theorem.')
generic = ('Generic advance and recursion specs allow empty V, arbitrary real eta including zero/negative with total inverse, '
    'and improper/infinite objectives. Returning some means a genuinely feasible minimum, even an infinite minimum in those generic cases. '
    'Returning none means no feasible attained minimum, not timeout, numerical failure or nonuniqueness. '
    'The initial center may lie outside V and the loss domain. Source performance uses positive eta and its stated loss/regularity hypotheses.')
performance = ('For the signed one-step result, both consecutive states must actually return some x and some p on the SAME recursion. '
    'V is convex, current eta is positive, the EReal loss is proper and has a global supporting subgradient at every feasible point. '
    'Each support compares all ambient y, not just feasible y; these premises establish finite compared loss values. '
    'Psi has actual ambient derivatives at BOTH x and p. Every u in V satisfies '
    'eta_t((loss_t p).toReal-(loss_t u).toReal) <= B_psi(u;x)-B_psi(u;p)-B_psi(p;x). '
    'The actual successor specification supplies the minimum and identifies its predecessor with x; the accepted extended-loss producer then applies. '
    'Both negative ordered residuals remain. No loss derivative, bounded domain, psi convexity or universal attainment is inferred. '
    'No infinity subtraction is used and residuals are not dropped without a separate nonnegativity argument.')
canaries = ('Four complete public Test conjunctions audit the boundary. Restricted absolute then different restricted affine -5z/8 on [-1,1], '
    'with psi=z^4/4+z^2/2, produce actual selected states 1/2 -> 0 -> 1/2; both losses are top outside the interval and abs is nonsmooth at zero. '
    'Genuine minima and uniqueness determine the chosen states; conditional local-attainment completion, actual successor extraction, '
    'whole-function prefix invariance and both actual one-step transitions are exercised. Ordered movements are 11/64 and 9/64; '
    'the two-round comparison gives -1/2 <= -5/16 at u=1/2. A restricted linear loss on [0,1] with quadratic psi starts at -1 outside BOTH V and the loss domain, '
    'selects boundary0 and gives movement1/2 and -1/2 <= 1/2. Both numerical tails retain the new actual-transition comparison by Eq.mp. '
    'For V=(-infinity,0], f(z)=z and psi=exp, source closed real-threshold sublevels, strict convexity and differentiability hold, '
    'yet the objective exp(z)-1 has no feasible minimum: p-1 always improves it. Advance is none and every positive state is none. '
    'This is a definedness audit, not a complete generated source run or author erratum. Finally z^2+z and z^2+abs(z) agree on X=[0,infinity); '
    'at interior base1/target2 the new locality theorem gives equal value1. At boundarybase0 their TOTAL-fderiv formulas give4 and6, '
    'and the second representative is proved nondifferentiable there. Those boundary values are diagnostics, not source-valid divergences. '
    'These four illustrative conjunctions are not additional printed results or canonical Book nodes.')
ps = 'BanditRL.OnlinePrescientBregman.'
specs = [
 ('BanditRL.OnlineBregman.divergence_extension_eq', 'Ambient representatives give the same divergence at interior bases',
  r'\begin{gathered}\psi|_X=\phi|_X,\ a\in X,\ b\in\operatorname{int}X\\ B_\psi(a;b)=B_\phi(a;b).\end{gathered}',
  'Equality on X and an interior base imply neighborhood equality. The actual local fderiv congruence gives equal derivatives at b, and equality of values at a,b finishes the ordered formula. No differentiability or convexity premise is needed for this algebraic equality; it does not supply regularity, an extension, positivity or equality of selected trajectories.',
  'Turn interior membership into an eventual neighborhood equality, reuse Filter.EventuallyEq.fderiv_eq, then substitute equal point values.'),
 (ps+'advance', 'Choose a current feasible minimum, or expose nonattainment',
  r'\begin{gathered}F_x(z)=\ell(z)+\eta^{-1}B_\psi(z;x),\\ A_x=\operatorname{some}(p)\text{ for a chosen feasible minimum},\\ A_x=\operatorname{none}\text{ when none exists}.\end{gathered}',
  'This exact definition tests existence of p in V that minimizes the actual EReal penalized current objective, chooses that witness if one exists, and returns none otherwise. Membership is part of the existence guard. It takes only V, psi, current eta, current loss and old x; no desired regret premise. Infinite minima remain possible in the unrestricted generic definition.',
  'An explicit dependent if separates mathematical attainment from nonattainment; Classical.choose is applied only under its actual existence proof.'),
 (ps+'iterate', 'Consume the current loss through the same partial recursion',
  r'I_0=\operatorname{some}(x_0),\qquad I_{t+1}=I_t\mathbin{\operatorname{bind}}A^{\eta_t}_{\ell_t}.',
  'State0 is some x0. Every successor binds the actual previous Option state to advance with exactly eta t and loss t. A missing state propagates through bind; there is no reset or substitute prediction. Reading a sequence as the mathematical input does not make the update consult future entries.',
  'The natural recursion calls the already fixed current-only selector at each successor.'),
 (ps+'advance_some_spec', 'Every returned point is an actual feasible current minimum',
  r'\begin{gathered}A_x=\operatorname{some}(p)\Longrightarrow p\in V,\\ \ell(p)+\eta^{-1}B_\psi(p;x)\le\ell(u)+\eta^{-1}B_\psi(u;x)\quad(u\in V).\end{gathered}',
  'If the exact advance returns some p, then p belongs to V and IsMinOn holds for precisely the current EReal objective. The impossible nonattainment branch is eliminated; Option.some injectivity identifies the returned value with the actual chosen witness. This is not a claim that every minimizer is selected or that it is unique or finite.',
  'Unfold the actual guard and use Classical.choose_spec, transporting its feasible-minimum conjunction to the returned point.'),
 (ps+'advance_none_iff', 'Failure is exactly absence of a feasible attained minimum',
  r'A_x=\operatorname{none}\iff\neg\exists p\in V,\ p\in\operatorname{argmin}_{z\in V}F_x(z).',
  'Both directions use the exact same feasibility-and-minimum existential as the definition. When the existential holds the chosen some cannot be none; when it fails the definition is none. Empty sets are allowed. Nonuniqueness does not cause failure, and this equivalence is not an equivalence with unboundedness.',
  'Split on the actual existence guard and prove the two iff branches without changing the objective or imposing regularity.'),
 (ps+'iterate_prefix', 'The actual state depends only on the consumed prefix',
  r'\bigl[\forall s<t,\ \eta_s=\eta_s^\prime,\ \ell_s=\ell_s^\prime\bigr]\Longrightarrow I_t=I_t^\prime.',
  'Two runs sharing V, psi and x0 have identical state t when steps and WHOLE current loss functions agree below t. This holds even for failed states and arbitrary real steps. The played point at t+1 uses loss t as well as earlier losses; the result does not convert prescient feedback into ordinary strict-past feedback.',
  'Induct on t; the predecessor states agree by the shorter prefix, then the equal current eta/loss give identical bind calls.'),
 (ps+'iterate_succ_some_spec', 'A successful successor exposes its real predecessor and current minimum',
  r'\begin{gathered}I_{t+1}=\operatorname{some}(p)\Longrightarrow\\ \exists x,\ I_t=\operatorname{some}(x),\quad p\in V,\quad p\in\operatorname{argmin}_{z\in V}\{\ell_t(z)+\eta_t^{-1}B_\psi(z;x)\}.\end{gathered}',
  'The previous x is the value actually returned by this recursion, and the current minimum is centered at that same x. No free predecessor, future-aware complete algorithm or desired one-step bound is assumed. The predecessor at round0 may be outside V.',
  'Option.bind_eq_some_iff extracts the real previous state and successful advance; advance_some_spec supplies its feasible minimum.'),
 (ps+'iterate_no_recovery', 'A missing state remains missing at every later offset',
  r'I_t=\operatorname{none}\Longrightarrow I_{t+k}=\operatorname{none}\quad(k\in\mathbb N).',
  'Every natural offset k, including zero, preserves none. A premise at time0 is impossible because state0 is some x0. This describes the exact partial recursion and does not provide an efficient test of minimizer existence or a restart policy.',
  'Induct on the offset; the next bind applied to none is none by definition.'),
 (ps+'iterate_complete_of_step_attained', 'Actual local attainment suffices for a finite successful run',
  r'\begin{gathered}\forall t<T,\ I_t=\operatorname{some}(x)\Longrightarrow\operatorname{argmin}_{V}F_{t,x}\ne\varnothing\\ \Longrightarrow\exists p,\ I_T=\operatorname{some}(p).\end{gathered}',
  'Assume for every reached some-state below T that its actual current EReal objective attains a feasible minimum. The same recursion then returns some at T. This is a proof premise about actual reached states, not an oracle read by the producer and not attainment deduced from closedness/strict convexity. T=0 needs no attainment and may return x0 outside V.',
  'Induct on the horizon, apply local attainment to the successful predecessor, rule out advance=none with the exact iff, and bind its successful value.'),
 (ps+'iterate_one_step', 'The very same produced transition gives both signed residuals',
  r'\eta_t(\ell_{t,\mathrm{fin}}(p)-\ell_{t,\mathrm{fin}}(u))\le B_\psi(u;x)-B_\psi(u;p)-B_\psi(p;x)\quad(u\in V).',
  performance,
  'Recover the actual predecessor and feasible current minimum from the successor; identify the predecessor with the supplied actual prior state by Option injectivity. Apply proximal_one_step_extended to that very minimum.')]
prod = load(CONTRACT / 'stabilized-v1.json')
assert {x[0] for x in specs} == {t['declaration'] for t in prod['targets'] + prod['definitions']}
prior = ROOT / 'tmp/online-ch2-extended-proximal-site-v1/books/registry.json'
receipt = ROOT / 'runs/online-ch2-extended-proximal-20261009/registry-inspected-v1.json'
old_registry = load(prior)
assert sha(prior) == load(receipt)['actual_current_registry_sha256']
assert len(old_registry['nodes']) == 11005 and old_registry['lean_verified']
assert old_registry['source_commit'] == '2b929d03d7ace7c418986e429d0ccf317a2721c6'
write(RUN / 'registry-baseline-v1.json.gz', gzip.compress(prior.read_bytes(), mtime=0))
names = {x['id'].removeprefix('declaration:') if hasattr(str, 'removeprefix') else x['id'][len('declaration:'):] for x in old_registry['nodes']}
names.update(x[0] for x in specs)
write(RUN / 'registry-baseline-binding-v1.json', dict(prior_source=prior.as_posix(),
    prior_complete_raw_sha256=sha(prior), compressed_snapshot_sha256=sha(RUN / 'registry-baseline-v1.json.gz'),
    prior_actual_registry_receipt_sha256=sha(receipt), source_commit=old_registry['source_commit'],
    total_shared_nodes=11005, identity=old_registry['identity'],
    expected_new_canonical_ids=['declaration:' + x[0] for x in specs],
    expected_new_definitions=2, expected_new_theorems=8, expected_total=11015,
    all_public_Test_and_generated_Test_nodes_excluded=True, main_live_updated=False,
    chapter_complete=False, whole_Goal_status='ACTIVE'))
graph = {n['name']: n for n in load(RUN / 'production-dependency-data-v2.json')['nodes']}
notes = []
for i, (name, title, formula, plain, proof) in enumerate(specs):
    parents = sorted(n for n in graph[name]['value_dependencies'] if n in names and n != name)
    notes.append(dict(full_name=name, title=title, chapter=route, featured=False,
        teaching_order=177+i, plain=objects + ' ' + plain, math=formula,
        intuition=proof, why='Certify the actual current-only partial update in the required Chapter 2 general prescient dependency.',
        position=source + ' Derived foundation or exact definition, not a separately numbered source result.',
        proof_idea=proof, lean_notes=objects + ' ' + information + ' ' + generic + ' ' + plain + ' ' + canaries + ' ' + boundary,
        dependencies=parents))
card = dict(label='Chapter 2 prescient dependency: actual partial updates and interior-base locality',
    pages='printed 14,16-17,63-64,265-266 / PDF 26,28-29,75-76,277-278', pdf_page=277,
    url='https://arxiv.org/pdf/1912.13213v10', math=specs[-1][2],
    plain=objects + ' ' + information + ' ' + generic + ' ' + performance,
    fallback=performance,
    relationship=source + ' ' + boundary,
    contract=dict(model='Exact Option partial recursion under known-current-loss feedback; no universal all-stream minimizer existence.',
        assumptions=objects + ' ' + generic + ' ' + performance,
        parameters='State0=x0; loss t/eta t consumed for state(t+1). Positive current eta only for performance; arbitrary eta for generic specs.',
        regret='Same-produced-transition finite-part loss difference with both signed residuals, plus two finite concrete run instances. Full cumulative source endpoints remain open.',
        guarantee=information + ' ' + performance + ' ' + canaries + ' ' + boundary),
    local_status=dict(status='compiled', label='Partial causal update foundations compiled; full source remains open', boundary=boundary))
proposal = dict(route=route, notes=notes, card=card, boundary=boundary,
    new_module_glob='BanditRLProof/OnlinePrescientBregman.lean',
    added_learning_goal='Trace a genuine current-loss partial argmin recursion, its exact failure and prefix semantics, and its actual signed one-step bound.',
    completion_extension=' Additive actual-update foundation: eight derived proofs and two exact definitions; full cumulative source container remains open. ' + boundary)
write(RUN / 'reader-proposal-v1.json', proposal)
plans = []
for rel, line in [('BanditRLProof.lean', 'import BanditRLProof.OnlinePrescientBregman'),
                 ('Tests.lean', 'import Tests.OnlinePrescientBregmanCanary')]:
    p = ROOT / rel
    raw = p.read_bytes()
    assert line.encode() not in raw
    before = RUN / ('publication-before-' + Path(rel).name)
    after = RUN / ('publication-after-' + Path(rel).name)
    write(before, raw)
    write(after, raw + ('\n' + line + '\n').encode('utf8'))
    plans.append(dict(path=p.as_posix(), before_snapshot=before.as_posix(), before_sha256=sha(p),
        after_snapshot=after.as_posix(), after_sha256=sha(after), delta='Raw prefix preserved plus one import.'))
for key in ['chapters', 'readings', 'highlights']:
    p = ROOT / ('website/content/' + key + '.json')
    new = copy.deepcopy(load(p))
    before = RUN / ('publication-before-' + key + '.json')
    after = RUN / ('publication-after-' + key + '.json')
    write(before, p.read_bytes())
    if key == 'chapters':
        row = next(x for x in new['chapters'] if x['slug'] == route)
        row['module_globs'].append(proposal['new_module_glob'])
        row['learning_goals'].append(proposal['added_learning_goal'])
        row['completion_definition'] += proposal['completion_extension']
    elif key == 'readings':
        next(x for x in new['readings'] if x['slug'] == route)['source_theorems'].append(card)
    else:
        assert not any(x['full_name'] in {n['full_name'] for n in notes} for x in new['highlights'])
        new['highlights'].extend(notes)
    write(after, new)
    plans.append(dict(path=p.as_posix(), before_snapshot=before.as_posix(), before_sha256=sha(p),
        after_snapshot=after.as_posix(), after_sha256=sha(after),
        delta={'chapters':'Only online-ogd: append module/goal/completion suffix.',
               'readings':'Only online-ogd: append one precise source-qualified card.',
               'highlights':'Append ten canonical production notes; preserve every old note.'}[key]))
write(CONTRACT / 'exact-publication-plan-v1.json', dict(rows=plans,
    reader_proposal_sha256=sha(RUN / 'reader-proposal-v1.json'), allowed_old_mutations=5,
    all_other_baseline_paths_immutable=True, other_Books_preserved=True,
    old_links_and_fields_preserved=True, shared_registry_not_per_Book=True,
    global_SGB_untouched=True, generated_site_not_edited=True,
    source_container_closed=False, chapter_complete=False, whole_Goal_status='ACTIVE'))
write(RUN / 'publication-director-v1.md', 'Prospective exact five-path materialization only; no existing root/Test/reader mutation yet. '
    'Ten production notes are eight derived proofs/two exact definitions, not ten printed source results. '
    'All old fields/links and other Books preserved. Actual VALUE parents drawn only from the inspected compiled graph and known canonical registry; '
    'imports/teaching/source overlays are not proof edges. Same shared registry baseline11005 expected plus10canonical productionIDs=11015; four Test conjunctions excluded. '
    'Functor none-found-with-reason: partial mathematical definedness and local representation equality within one feedback setting, '
    'no new certified map combining different problem models. ' + boundary + ' ' + canaries)
fixed()
print('Ten source-qualified production notes and five exact prospective transitions drafted; old paths unchanged.')
