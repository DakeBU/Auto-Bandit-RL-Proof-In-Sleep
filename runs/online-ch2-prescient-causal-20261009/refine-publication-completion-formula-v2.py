from common import *
fixed()
proposal = load(RUN / 'reader-proposal-v1.json')
name = 'BanditRL.OnlinePrescientBregman.iterate_complete_of_step_attained'
formula = r'\begin{gathered}[\forall t<T,\ \forall x,\ I_t=\operatorname{some}(x)\Longrightarrow\\ \exists p\in V,\ p\in\operatorname{argmin}_{z\in V}F_{t,x}(z)]\\ \Longrightarrow\exists p,\ I_T=\operatorname{some}(p).\end{gathered}'
note = next(n for n in proposal['notes'] if n['full_name'] == name)
old_formula = note['math']
assert formula != old_formula
note['math'] = formula
write(RUN / 'reader-proposal-v2.json', proposal)
plan = load(CONTRACT / 'exact-publication-plan-v1.json')
for row in plan['rows']:
    assert sha(row['path']) == row['before_sha256']
    if row['path'].endswith('/highlights.json'):
        data = load(row['after_snapshot'])
        note = next(n for n in data['highlights'] if n['full_name'] == name)
        assert note['math'] == old_formula
        note['math'] = formula
        after = RUN / 'publication-after-highlights-v2.json'
        write(after, data)
        row['after_snapshot'] = after.as_posix()
        row['after_sha256'] = sha(after)
plan['reader_proposal_sha256'] = sha(RUN / 'reader-proposal-v2.json')
plan['prospective_refinement'] = 'Make every reached predecessor x explicitly universally quantified and bracket the entire attainment premise before its terminal implication; no Lean statement or existing reader path changed.'
write(CONTRACT / 'exact-publication-plan-v2.json', plan)
write(RUN / 'publication-director-v2.md', 'Formalizer self-review before source publication review caught a free x and ambiguous scope in the completion display. The v2 prospective note quantifies every x and brackets the local-attainment premise before the terminal implication, preserving the exact frozen theorem. Only one new math field differs between v1/v2 prospective highlights; all old live paths remain unchanged. Production and all Test headers/bodies fixed. No source/chapter/native/publication acceptance is inferred.')
fixed()
