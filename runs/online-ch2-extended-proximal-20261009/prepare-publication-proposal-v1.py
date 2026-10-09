from common import *
import copy
fixed()
route = 'online-ogd'
boundary = ('These three derived bridges lower a required Chapter 2 prescient forward dependency. '
    'They do not complete Algorithm 15.8 or Theorem 15.30, or accept Chapters 6 or 15. '
    'The source domain X, interior and ambient extension locality, attained current-loss causal recursion, '
    'interior invariants and sharp fixed/variable same-run telescopes remain REQUIRED/OPEN, including the '
    'main-text fixed-step exercise. All eight Chapter 2 forward containers remain open; Chapter 2 is partial '
    'and the Chapters 1–16 Goal is ACTIVE. Stacked on OPEN draft unmerged PR #209 exact ' + BASE + '. '
    'No merge, deployment, main, live or CI acceptance claim.')
source = ('Orabona, Online Learning, arXiv:1912.13213v10 (2026-06-21): '
    'Definitions 2.18/2.20 and Theorem 2.21, printed 16–17 / PDF 28–29; '
    'Definition 6.4 and Lemma 6.7, printed 63–64 / PDF 75–76; '
    'Algorithm 15.8/Theorem 15.30, printed 265–266 / PDF 277–278. PDF SHA256 ' + PDF_SHA + '.')
objects = ('The same EReal loss f, convex feasible set V and canonical ordered divergence '
    'Bψ(a;b)=ψ(a)−ψ(b)−Dψ(b)[a−b] are used throughout. Properness excludes negative infinity everywhere '
    'and supplies one finite point. At every feasible z, a source subgradient supports f at every ambient y. '
    'This global support condition implies that f is finite at every point of V; outside V, positive infinity is allowed. '
    'The first bridge uses an arbitrary real inner-product space. The other two explicitly retain completeness '
    'from the reused minimum-order API. Finite Euclidean source spaces are covered; minimal assumptions are not claimed.')
finite = ('The result is convexity of z ↦ (f z).toReal restricted to V. '
    'Taking toReal at infinity gives zero, so the total real function need not be globally convex. '
    'The proof selects a global support at the feasible convex combination, compares the two feasible endpoints, '
    'and cancels the weighted inner products after feasible finiteness has been established.')
minimum = ('For a supplied p in V and finite f on V, the actual EReal objective '
    'f(z)+η⁻¹ Bψ(z;x) has a minimum at p exactly when its real finite-part objective does. '
    'This order equivalence permits every real η, including zero and negative values, with Lean’s total inverse. '
    'It needs no convexity, derivative, positive step size or attainment premise beyond the supplied minimum in each direction. '
    'The center x may be outside V and the loss domain. The proof reuses the shared minOn_finitePart_iff on the actual penalized objective.')
step = ('For the one-step comparison, η is positive, V is convex, f is proper and has global supports at '
    'every feasible point, p belongs to V and actually minimizes the EReal penalized objective there. '
    'The generator ψ has actual ambient derivatives at both x and p. Every u in the same V satisfies '
    'η((f p).toReal−(f u).toReal) ≤ Bψ(u;x)−Bψ(u;p)−Bψ(p;x). '
    'Both negative residuals and their target/base order are retained. No infinity subtraction, loss derivative, '
    'convexity of ψ, closedness of V, bounded domain or existence of minimizers is asserted. '
    'Dropping residuals requires separate nonnegativity hypotheses.')
canaries = ('Two exact public Test conjunctions use losses equal to positive infinity outside their intervals. '
    'On [−1,1], the absolute loss with ψ(z)=z⁴/4+z²/2 has actual minimum 0 at center 1/2, '
    'is nondifferentiable at zero and gives divergences 9/64 and 11/64. '
    'On [0,1], the linear loss with ψ(z)=z²/2 has actual boundary minimum 0 at center −1, '
    'which is outside both V and the loss domain. Both prove feasible convexity and failure of global finite-part convexity. '
    'Their universal comparisons and final numeric proof branches invoke the new extended one-step helper. '
    'These are static illustrative instances, not additional printed results or causal trajectories. '
    'Focused compilation and public proof probes are distinct from package and chapter acceptance.')
specs = [
    ('finitePart_convex_of_subdifferentiable', 'Global supports give convexity on the finite feasible domain',
     r'\partial f(z)\ne\varnothing\ (z\in V),\ f\text{ proper}\ \Longrightarrow\ \operatorname{ConvexOn}_V(f_{\rm fin}).',
     finite, 'Evaluate a support at the convex combination and compare both feasible endpoints.',
     ['BanditRL.OnlineConvex.subgradient_point_finite']),
    ('proximal_finitePart_minimizer_iff', 'The actual extended proximal minimum has a real finite-part equivalent',
     r'p\in\arg\min_{z\in V}\{f(z)+\eta^{-1}B_\psi(z;x)\}\iff p\in\arg\min_{z\in V}\{f_{\rm fin}(z)+\eta^{-1}B_\psi(z;x)\}.',
     minimum, 'Use finite embeddings only at feasible points, then reuse the shared minimum-order equivalence.',
     ['BanditRL.OnlineConvex.minOn_finitePart_iff']),
    ('proximal_one_step_extended', 'An extended proximal minimum gives the signed one-step comparison',
     r'\eta(f_{\rm fin}(p)-f_{\rm fin}(u))\le B_\psi(u;x)-B_\psi(u;p)-B_\psi(p;x)\quad(u\in V).',
     step, 'Derive feasible convexity and transport the actual minimum, then invoke the accepted real proximal theorem.',
     ['BanditRL.OnlineConvex.subgradient_point_finite',
      'BanditRL.OnlineBregman.finitePart_convex_of_subdifferentiable',
      'BanditRL.OnlineBregman.proximal_finitePart_minimizer_iff',
      'BanditRL.OnlineBregman.proximal_one_step'])]
notes = []
for i, (short, title, formula, plain, idea, parents) in enumerate(specs):
    notes.append(dict(full_name='BanditRL.OnlineBregman.' + short, title=title, chapter=route,
        featured=False, teaching_order=174+i, plain=objects + ' ' + plain, math=formula,
        intuition=idea, why='Preserve extended losses in the required Chapter 2 general prescient dependency.',
        position=source + ' Derived bridge, not a separate numbered source theorem.', proof_idea=idea,
        lean_notes=objects + ' ' + plain + ' ' + canaries + ' ' + boundary, dependencies=parents))
card = dict(label='Chapter 2 prescient dependency: extended losses on a finite feasible domain',
    pages='printed 16–17,63–64,265–266 / PDF 28–29,75–76,277–278', pdf_page=277,
    url='https://arxiv.org/pdf/1912.13213v10', math=specs[2][2],
    plain=objects + ' ' + finite + ' ' + minimum + ' ' + step, fallback=step,
    relationship=source + ' ' + boundary,
    contract=dict(model='Static actual EReal objective and supplied feasible minimum; no causal or attainment conclusion.',
        assumptions=objects + ' ' + step,
        parameters='Arbitrary real eta for minimum equivalence; positive eta for the signed comparison. Every comparator is in V.',
        regret='A one-step finite loss difference with both signed residuals; no cumulative regret or horizon claim.',
        guarantee=finite + ' ' + minimum + ' ' + step + ' ' + boundary),
    local_status=dict(status='compiled', label='Extended-loss bridges compiled; full source remains open', boundary=boundary))
proposal = dict(route=route, notes=notes, card=card, boundary=boundary,
    new_module_glob='BanditRLProof/OnlineBregmanExtended.lean',
    added_learning_goal='Derive feasible finite-part convexity, the actual extended proximal minimum equivalence and the signed one-step comparison.',
    completion_extension=' Additive extended-loss foundation: three derived helper proofs, zero new definitions and no full source-container closure. ' + boundary)
write(RUN / 'reader-proposal-v1.json', proposal)
plans = []
for rel, line in [('BanditRLProof.lean', 'import BanditRLProof.OnlineBregmanExtended'),
        ('Tests.lean', 'import Tests.OnlineBregmanExtendedCanary')]:
    p = ROOT / rel
    raw = p.read_bytes()
    assert line.encode() not in raw
    before = RUN / ('publication-before-' + Path(rel).name)
    after = RUN / ('publication-after-' + Path(rel).name)
    write(before, raw)
    write(after, raw + ('\n' + line + '\n').encode('utf8'))
    plans.append(dict(path=p.as_posix(), before_snapshot=before.as_posix(), before_sha256=sha(p),
        after_snapshot=after.as_posix(), after_sha256=sha(after), delta='Raw prefix preserved; append one import.'))
for n in ['chapters', 'readings', 'highlights']:
    p = ROOT / ('website/content/' + n + '.json')
    new = copy.deepcopy(load(p))
    before = RUN / ('publication-before-' + n + '.json')
    after = RUN / ('publication-after-' + n + '.json')
    write(before, p.read_bytes())
    if n == 'chapters':
        row = next(x for x in new['chapters'] if x['slug'] == route)
        row['module_globs'].append(proposal['new_module_glob'])
        row['learning_goals'].append(proposal['added_learning_goal'])
        row['completion_definition'] += proposal['completion_extension']
    elif n == 'readings':
        next(x for x in new['readings'] if x['slug'] == route)['source_theorems'].append(card)
    else:
        assert not any(x['full_name'] in {y['full_name'] for y in notes} for x in new['highlights'])
        new['highlights'].extend(notes)
    write(after, new)
    plans.append(dict(path=p.as_posix(), before_snapshot=before.as_posix(), before_sha256=sha(p),
        after_snapshot=after.as_posix(), after_sha256=sha(after),
        delta={'chapters': 'Only online-ogd: append one module/goal/completion suffix.',
            'readings': 'Only online-ogd: append one bounded source-qualified card.',
            'highlights': 'Append three public production notes; preserve every old note.'}[n]))
write(CONTRACT / 'exact-publication-plan-v1.json', dict(rows=plans,
    reader_proposal_sha256=sha(RUN / 'reader-proposal-v1.json'), allowed_old_mutations=5,
    all_other_baseline_paths_immutable=True, other_Books_preserved=True, global_SGB_untouched=True,
    generated_site_not_edited=True, source_container_closed=False, chapter_complete=False, whole_Goal_status='ACTIVE'))
write(RUN / 'publication-director-v1.md',
    'PROSPECTIVE bytes only: no root, Test root or reader mutation. Three production proofs, zero new definitions, '
    'not three printed results. Exact five-path before/after scope requires distinct review. '
    'Teaching links must match selected actual compiled VALUE parents; the complete shared registry is pending. '
    'Functor none-found-with-reason: finite-part representation/order transport inside one setting, '
    'not a proved map composing distinct problem models. ' + boundary + ' ' + canaries)
fixed()
print('Three source-qualified reader notes and five exact prospective file transitions drafted; all old bytes unchanged.')
