from common_v1 import *

fixed()
for command in ['list-mathlib', 'list-papers', 'list-weapons']:
    native(command + '-v2', command)
native('search-memory-independence-v2', 'search-memory', 'independence')
native('list-lean-history-policy-v2', 'list-lean-decls', 'history_policy', '--statement')
native('list-lean-private-seed-v2', 'list-lean-decls', 'private_seed', '--statement')
native('retrieval-record-help-v2', 'retrieval-record', '--help')
native('retrieval-record-v2', 'retrieval-record', '--task', TASK,
    '--query', 'IndepFun whole-seed triple grouping measurable product associativity and strict-past comap',
    '--candidate', 'ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map',
    '--candidate', 'MeasureTheory.Measure.prodAssoc_prod',
    '--candidate', 'MeasurableEquiv.map_measurableEquiv_injective',
    '--candidate', PRE + 'history_policy_independent',
    '--rejection', 'pairwise seed-target independence=does not imply joint seed+past current independence',
    '--compiled-scratch', 'lake env lean runs/online-randomized-iid-20261008/draft-types-and-API-v2.lean',
    '--provenance', 'research-wiki/retrieval-index/local_lean_declarations.json',
    '--output', (RUN / 'native-retrieval-record-v2.json').as_posix())
write(RUN / 'retrieval-packet-v2.md', '''Local-first reviewed route candidates, not proof claims. Cards MLIB-PROBABILITY-INDEPENDENCE, MLIB-MEASURE-INTEGRAL, MLIB-PROBABILITY-VARIANCE. Source card docs/contracts/online-randomized-iid-v1/source-card-v2.json (Orabona v10 printed1–2/PDF13–14); scenario private tape independent of whole IID target process, strict-past finite tuple/subordinate sigma field. No proof weapon used as a dependency. General R001 mathlib-candidate locally UNPROVED; R002–R007 project-local producer/interfaces. Native reference-index/list-mathlib/list-papers/list-weapons/search-memory/list-lean-decls/typed actual #checks retained.

Searches actually run: IndepFun(prodMk,pi,pair,comp), iSup disjoint grouping, measurable product map/associativity, comap compose/le/mono, old expectedFixed/history policy. No exact natural joint-seed regrouping wrapper found locally; not a global novelty claim. Initially guessed missing Kernel/Defs and Constructions/Prod/Basic paths (session raw outputs retained), actual Kernel/Indep.lean and MeasurableSpace/Constructions.lean located. Actual namespace correction from draft compile: map_measurableEquiv_injective is MeasurableEquiv. Actual prodAssoc_prod and independence/product-law equivalence types compiled under pinned project. Direct source files inspected, not copied wholesale.

R001 route: infer joint law of(S,(X,Y)), use X/Y independence then measurable product associativity and injectivity to regroup into((S,X),Y), infer pair marginal and factorized law. Need measurable all functions/probability maps (SFinite) and explicit assoc domain universes. R002 takes hseed for WHOLE process, composes exact finite past/current vector extraction and applies R001 with joint-IID past/current fact. R003 restricts longer tuple via measurable coordinate projections and comap monotonicity. R004 uses comap(P)≤F≤generatedInfo and weakens left independent sigma field. R006 derives ambient measurable prediction through generatedInfo≤ambient, derives L2 from a.s.bound; then actual PR194 benchmark/cumulative decomposition. R007 supplies generatedInfo exactly and legal-history a.s.support. No stabilized body yet.
''')
write(RUN / 'canary-plan-v2.json', dict(status='planned-not-proved',
    actual_seed_model='fair Bernoulli seed independently product with actual infinite fair IID target law',
    targets=['whole-seed process independence', 'generated past information monotone',
        'seed-only initial and past-dependent later policy measurability and legal-cube feasibility',
        'actual finite cumulative identity/nonnegativity at T0 and T2, positive variance1/4',
        'general predictable generated information wiring',
        'XOR seed individually independent of two IID targets but jointly reveals current with past; joint seed independence fails',
        'current-target leak violates information interface', 'off-cube infeasible values do not invalidate legal-only policy'],
    source_items_closed=0, chapter_complete=False, goal_complete=False))
indexes = ['bandit_paper_cards.json', 'bandit_scenario_cards.json', 'bandit_textbook_cards.json',
    'local_leaf_cards.json', 'local_lean_declarations.json', 'proof_weapon_cards.json']
report = []
for name in indexes:
    p = Path('research-wiki/retrieval-index') / name
    old = json.loads(subprocess.check_output(['git', 'show', BASE + ':' + p.as_posix()]))
    new = load(p)
    report.append(dict(path=p.as_posix(), old_type=type(old).__name__, new_type=type(new).__name__,
        old_count=len(old), new_count=len(new), old_top_keys=list(old)[:8] if isinstance(old,dict) else None,
        new_top_keys=list(new)[:8] if isinstance(new,dict) else None,
        actual_raw_changed=sha(p) != hashlib.sha256(subprocess.check_output(['git', 'show', BASE + ':' + p.as_posix()])).hexdigest(),
        semantic_equal=old == new))
write(RUN / 'native-reference-index-draft-audit-v2.json', report)
fixed()
print('Actual retrieval and unproved canary plan recorded; source review precedes proof search.')
