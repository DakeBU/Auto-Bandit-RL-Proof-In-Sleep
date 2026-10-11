from common import *
review = RUN/'parent-BODY-review-v1.json'
r = load(review)
assert sha(review) == 'e8c1267c19946e48db58b9111d9ab7499bddb2d773d895fca228d7bf0bbf8e92'
assert not r['required_blocking_repairs'] and r['inputs_unchanged']
for x in r['raw_input_checks']:
    assert sha(x['path']) == x['expected_sha256'] == x['before_sha256'] == x['after_sha256']
public = ROOT/'BanditRLProof/OnlineAdaptiveOSD.lean'
frontier = dict(package=TASK, branch=BRANCH, base=BASE, Goal_status='ACTIVE',
    stage='Actual same-run parameterized terminal locally compiled and distinct BODY-reviewed; source endpoints/benchmark/algorithm canary and full package remain open.',
    production_sha256=sha(public), parent=dict(name='BanditRL.OnlineAdaptiveOSD.regret_bound',
        BODY_present=True, header_sha256=r['header_sha256'], normalized_statement_hash=r['normalized_statement_hash'],
        full_negative_terminal=True, T0_D0_zero_energy_included=True,
        focused_public_axioms_fence_VALUE='actual successful evidence',
        BODY_review_sha256=sha(review), package_accepted=False),
    locally_closed_dependency_families=['weighted potential plus FULL canaries',
        'actual joint causal recurrence and strict-past whole state',
        'same-run energy feasibility finiteness lawful canonical adapter',
        'actual zero/nonzero support and projection one-step',
        'actual same-run cumulative negative-terminal bound'],
    current_frontier=['Four precise explicit-convexity source and canonical endpoints drafted/typechecked; neutral context expansion repair in progress.',
        'Separate minimum/infimum repair mathematically reviewed; exact Lean benchmark not yet frozen/proved.',
        'Nondegenerate actual algorithm canary not yet drafted.',
        'Combined root Tests full harness axiom registry reader shadow site FINAL native delivery required.'],
    chapter='Chapter2 partial/null; all eight required forward containers remain open until exact obligations close.',
    other_chapters='Chapter1 prior accepted-local; Chapters3-16 unenumerated/null; no chapter gate advanced.',
    global_preservation='Global SGB/source/old contracts/shared stores and runtime unchanged.',
    delivery='No current package commit push PR merge deploy. PR217 exact head is the explicit unmerged stacked base.')
write(RUN/'causal-frontier-v3.json', frontier)
write(RUN/'memory-digest-v3.md', '''The actual parent frontier has closed locally: the same causal state's one_step is now summed via the zero/stalled-weight potential and its own selected norm energy bound. The exact original all-T, D>=0 negative-terminal header is unchanged. T0 and D0 are explicit and total energy sqrt is never canceled. Focused/public/standard axioms/fence and actual seven direct VALUE parents separately passed; distinct staged BODY review accepts with the support-sufficient/source-convex delta. This is not source endpoint/package/chapter acceptance.

Four source-convex Eq4.4/Theorem4.14 and canonical endpoints are drafted with actual IsConvexExtended retained. The first decoder refused to guess its imported epigraph body; a neutral-context-only v2 appends the exact realEpigraph/IsConvexExtended definitions, preserving all v1 bytes/headers. This is an input-context repair, not a failed theorem or changed target. Source minimum/infimum repair remains separate from the withdrawn missing-/2 allegation. Actual benchmark and algorithm canary/full combined/publication gates remain required. Local digest only, no certified global memory promotion.
''')
addition = '''

## Current causal terminal frontier v3

Latest snapshot: runs/online-ch2-adaptive-osd-20261010/causal-frontier-v3.json. Older pending descriptions above are historical. Actual seven zero/nonzero-step proofs and the unchanged same-run negative-terminal regret_bound now locally compile, have full public applications/standard axioms/frozen checks/selected compiled VALUE parents, and favorable distinct BODY reviews. T0,D0,leading/all-zero energy and fixed-common-policy information boundary remain explicit. This lowers the source-terminal frontier to exact Eq4.4/Theorem4.14 convex and canonical specializations, the separate required minimum/infimum Lean benchmark, and actual algorithm canary. Four source headers/typechecks are draft; neutral imported-predicate expansion is being repaired without header change. Interface counts are not source or chapter coverage.

No current package combined root/Tests/full harness/registry/reader/site/native/FINAL/delivery gate or commit/push/PR yet. All eight Chapter2 forward containers remain required/open and whole Goal ACTIVE. No global SGB or old source/contract change; no main/live update or worktree retirement.
'''
for folder in ['proof-obligations', 'conversion-windows', 'research-wiki/retrieval-index']:
    path = ROOT/folder/(TASK+'.md')
    before = path.read_bytes()
    write(RUN/('before-causal-frontier-v3-'+folder.replace('/','-')+'.md'), before)
    path.write_bytes(before+addition.encode('utf8'))
event('parent-candidate-event-v1', 'candidate', dict(current_leaf='regret_bound',
    BODY_review_sha256=sha(review), frontier_sha256=sha(RUN/'causal-frontier-v3.json'),
    boundary='Local parent candidate; no native accepted or package/chapter acceptance.'))
print('Parent local candidate/frontier recorded; full package and Goal remain open.', flush=True)
