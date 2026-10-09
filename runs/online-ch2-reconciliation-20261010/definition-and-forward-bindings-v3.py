from common import *
fixed()
previous = CONTRACT / 'omitted-definition-context-bindings-draft-v1.json'
assert len(load(previous)['rows']) == 7
for row in load(previous)['rows']:
    assert sha(ROOT / row['module']) == row['complete_module_sha256']
    for stage in row['explicit_staged_definition_scope_bindings']:
        assert sha(stage['path']) == stage['sha256']
        assert sha(stage['report']['path']) == stage['report']['sha256']
inventory = load(ROOT / 'docs/contracts/online-ch2-chapter-audit-v1/complete-source-reconciliation-draft-v3.json')
owners = {
    'additional:prescient-lookahead-nonpositive-stability': 15,
    'forward:chapter5-unbounded-variable-OGD-failure': 5,
    'forward:chapter5-oracle-distance-energy-rate-impossibility': 5,
    'forward:chapter5-DLsqrtT-minimax-optimality': 5,
    'forward:chapter3-unbounded-SGD': 3,
    'forward:chapter4-adaptive-oracle-like-rates': 4,
    'forward:chapter4-square-OGD-improvement': 4,
    'forward:chapter13-parameter-free-oracle-like-rates': 13,
}
forward = []
for source in inventory['rows']:
    ident = source['source_id']
    if ident not in owners:
        continue
    assert source['required'] is True
    forward.append(dict(source_id=ident, owner_chapter=owners[ident], required_in_whole_book=True,
        source_pages=source['source_pages'], exact_source_page_texts=[dict(path=p['text_path'], sha256=sha(p['text_path']), text=Path(p['text_path']).read_text(encoding='utf8')) for p in source['source_pages']],
        mathematical_intent=source['mathematical_intent'], local_navigation_mapping='explicit ownership edge proposed',
        mathematical_dependency_status='required/open', exact_future_theorem_enumeration='pending' if ident not in [
            'additional:prescient-lookahead-nonpositive-stability', 'forward:chapter5-unbounded-variable-OGD-failure'] else 'exact separately delivered candidate bound; chapter-source reconciliation pending',
        local_Chapter2_accepted=False, local_explanatory_mapping_does_not_discharge_mathematics=True,
        candidate_package={'additional:prescient-lookahead-nonpositive-stability': 'ONLINE-CH2-PRESCIENT-SOURCE-20261010',
            'forward:chapter5-unbounded-variable-OGD-failure': 'ONLINE-CH2-UNBOUNDED-OSD-20261010'}.get(ident)))
assert len(forward) == 8
write(CONTRACT / 'required-forward-dependencies-draft-v1.json', dict(rows=forward,
    required_open_count=8, future_statements_unenumerated_count=6,
    counting_boundary='Eight source containers/ownership edges, not eight independent theorem counts. Each exact later theorem and necessary dependencies must be enumerated before proof. No difficult target excluded.',
    Chapter2_status='partial', whole_Goal='ACTIVE', chapter_complete=False))
fixed()
print('Seven exact definition-context bindings and eight required/open forward ownership rows recorded; review pending.', flush=True)
