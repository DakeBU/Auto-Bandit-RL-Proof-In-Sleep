from common import *
from collections import Counter
sys.path.insert(0, str(ROOT))
from tools import bandit

fixed()
capture('native-current-online-lookup-v1', sys.executable, '-B', '-X', 'utf8', RUN / 'native-scoped.py',
    'list-lean-decls', 'Online', '--statement')
inventory_path = ROOT / 'docs/contracts/online-ch2-chapter-audit-v1/complete-source-reconciliation-draft-v3.json'
inventory = load(inventory_path)
old_index_path = ROOT / 'runs/online-ch2-chapter-audit-20261009/current-online-declaration-retrieval-v1.json'
old_index = {r['full_name']: r for r in load(old_index_path)['rows']}
scanned = bandit.scan_lean_declarations(include_tests=True)
selected = [r for r in scanned if Path(r['file']).name.startswith('Online')]
index = {}
for r in selected:
    name = r['full_name']
    assert name not in index, name
    p = ROOT / r['file']
    h = bandit.lifecycle.lean_declaration_header(p, name)
    index[name] = dict(r, source_file_sha256=sha(p), native_header=h,
        native_statement_hash=bandit.lifecycle.statement_hash(h),
        scope_context='Complete current module, including imports, scoped variables, definitions and BODY; native header alone does not include all section parameters.',
        retrieval_only=True, newly_compiled=False)
write(RUN / 'current-online-declarations-v1.json', dict(rows=list(index.values()),
    production_count=sum(r['file'].startswith('BanditRLProof/') for r in index.values()),
    Tests_count=sum(r['file'].startswith('Tests/') for r in index.values()),
    scanner_and_header_API='Actual tools.bandit.scan_lean_declarations(include_tests=True), lifecycle.lean_declaration_header and statement_hash',
    boundary='Actual source declaration/type retrieval only. Not a compiler result, source completeness, or fresh review of all listed bodies.'))

joins = []
for source in inventory['rows']:
    for old in source.get('exact_current_terminal_bindings', []):
        name = old['declaration']
        current = index[name]
        assert current['file'] == old['module']
        assert current['source_file_sha256'] == old['complete_scope_and_BODY_sha256'], name
        assert current['native_statement_hash'] == old['native_statement_hash'], name
        assert current['native_header'] == old['native_header'], name
        joins.append(dict(source_id=source['source_id'], declaration=name,
            source_inventory_header_sha256=old['native_statement_hash'],
            current_header_sha256=current['native_statement_hash'],
            complete_current_module_sha256=current['source_file_sha256'],
            module=current['file'],
            current_header_exact=True, current_complete_module_exact=True,
            historical_candidate_receipt_paths=old.get('prior_complete_file_matching_receipts', []),
            source_acceptance_from_hash_only=False))
write(RUN / 'inventory-current-native-join-v1.json', dict(rows=joins,
    inventory_path=inventory_path.as_posix(), inventory_sha256=sha(inventory_path),
    source_container_rows=len(inventory['rows']), joined_bindings=len(joins),
    distinct_declarations=len({r['declaration'] for r in joins}),
    distinct_complete_modules=len({r['module'] for r in joins}),
    boundary='Exact mechanical current type and complete-module join only; relevant semantic/BODY/FINAL review scope still must be selected and checked. Container/declaration/module counts are not independent source obligations.'))

manifests = []
for p in sorted((ROOT / 'research-wiki/contribution-contracts').glob('*.json')):
    c = load(p)
    names = set(c.get('declarations', []))
    hits = sorted(names.intersection(index))
    if not hits:
        continue
    manifests.append(dict(path=p.as_posix(), sha256=sha(p), id=c.get('id'),
        source=c.get('source'), target=c.get('target'), affected_files=c.get('affected_files'),
        declarations=hits, semantic_roundtrip=c.get('semantic_roundtrip'),
        verification=c.get('verification'), truth_boundary=c.get('truth_boundary'),
        boundary='Manifest prose can contain historical pending fields. Exact later review/delivery receipts must independently supply any current acceptance.'))
write(RUN / 'current-online-manifest-candidates-v1.json', dict(rows=manifests,
    boundary='Current manifest declarations intersected with actual retrieved names; not acceptance based on manifest status strings.'))

additional = {}
for source_id, manifest_id in [
    ('additional:absolute-hinge-convex-nondifferentiable-introduction', 'ONLINE-CH2-NONSMOOTH-20261009'),
    ('additional:prescient-lookahead-nonpositive-stability', 'ONLINE-CH2-PRESCIENT-SOURCE-20261010'),
    ('forward:chapter5-unbounded-variable-OGD-failure', 'ONLINE-CH2-UNBOUNDED-OSD-20261010'),
]:
    p = ROOT / 'research-wiki/contribution-contracts' / (manifest_id + '.json')
    c = load(p)
    additional[source_id] = dict(manifest_path=p.as_posix(), manifest_sha256=sha(p),
        current_targets=[index[n] for n in c['declarations']],
        source=c['source'], remaining_semantic_delta=c['semantic_roundtrip']['remaining_semantic_delta'],
        proposed_only=True, source_container_accepted=False,
        boundary='Delivered package candidate for exact source container mapping; this join does not itself close the container or certify its whole printed branch scope.')
write(CONTRACT / 'additional-source-bindings-draft-v1.json', dict(rows=additional,
    scope='NEW mappings proposed for three previously unbound source containers; no old v3 row or theorem changed.',
    chapter_complete=False, whole_Goal='ACTIVE'))

write(RUN / '30_worker-current-join-v1.md', '# First finite reconciliation leaf\n\n'
    'Actual CLI declaration retrieval and current native API join succeeded. Every previously attached inventory binding has exactly the same normalized header and complete module RAW bytes. '
    'New nonsmooth/prescient/unbounded source-container candidates were joined to current named declarations via their contribution manifests. '
    'This is reusable mechanical audit evidence, not mathematical closure or chapter acceptance. The next leaf must select genuinely relevant exact blind/source/BODY/FINAL/delivery evidence; unrelated matching hashes and stale manifest pending prose cannot certify source coverage.\n')
write(RUN / 'current-join-summary-v1.json', dict(source_containers=len(inventory['rows']),
    joined_bindings=len(joins), distinct_previously_bound_declarations=len({r['declaration'] for r in joins}),
    distinct_previously_bound_modules=len({r['module'] for r in joins}),
    current_retrieved_declarations=len(index), manifest_candidates=len(manifests),
    new_container_binding_candidates=len(additional), new_mathematical_proofs=0,
    chapter_complete=False, whole_Goal='ACTIVE'))
fixed()
print('Current mechanical type/BODY and manifest joins recorded; source scope review pending.', flush=True)
