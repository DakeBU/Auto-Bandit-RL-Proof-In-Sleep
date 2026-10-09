from common import *

fixed()
index = load(RUN / 'current-online-declarations-v1.json')['rows']
questions = [b for g in load(CONTRACT / 'appropriate-scope-receipt-selection-draft-v1.json')['rows']
    for b in g['exact_bound_declarations'] if not b['manifest_contains_declaration']]
assert len(questions) == 7
bindings = []
for row in questions:
    current = next(r for r in index if r['full_name'] == row['declaration'])
    module = ROOT / current['file']
    lines = module.read_text(encoding='utf8').splitlines()
    following = [r['line'] for r in index if r['file'] == current['file'] and r['line'] > current['line']]
    end = min(following) - 1 if following else len(lines)
    block = '\n'.join(lines[current['line'] - 1:end]) + '\n'
    ident = 'online-ftl-state-20261007' if row['declaration'].endswith('.ftlPredict') else 'online-osd-policy-public-20261007'
    run = ROOT / 'runs' / ident
    stages = []
    for name in ['source-contract-receipt-v1.json', 'public-body-receipt-v1.json', 'final-reader-receipt-v1.json']:
        receipt = run / name
        data = load(receipt)
        assert data['verdict'].startswith('accepted') and not data.get('required_repairs')
        module_rows = [r for r in data['reviewed_files'] if r.get('path') == current['file']]
        assert len(module_rows) == 1 and module_rows[0]['sha256'] == sha(module)
        report = ROOT / data['report']
        assert sha(report) == data['report_sha256']
        if ident == 'online-ftl-state-20261007':
            verdict = next(v for v in data['definition_verdicts'] if v['target'] == 'ftlPredict')
            evidence = dict(explicit_definition_verdict=verdict)
        else:
            text = report.read_text(encoding='utf8')
            assert any(k in text for k in ['definitions', 'definition', 'Nat.rec', 'history'])
            evidence = dict(complete_report_binding=True,
                exact_definition_source_contract_report=rows([run / 'source-contract-review-v1.md']),
                source_report_definition_scope='Source report lines19-21 explicitly checks TYPE and VALUE of Domain/SupportPolicy/history/output/selected/OracleLaw/canonicalPolicy/LegalFeedback/regret under nine-name map; seven definitions/two abbreviations fully specified. Later relevant BODY/FINAL scopes retain the exact current complete module.',
                per_definition_fresh_semantic_review='pending bounded definition-context reconciliation; no acceptance from manifest omission or unrelated file hashing')
        stages.append(dict(path=receipt.as_posix(), sha256=sha(receipt), report=dict(path=report.as_posix(), sha256=sha(report)),
            exact_current_complete_module=True, appropriate_definition_evidence=evidence))
    bindings.append(dict(declaration=row['declaration'], module=current['file'], complete_module_sha256=sha(module),
        source_first_line=current['line'], source_last_line=end, exact_source_segment=block,
        exact_source_segment_sha256=hashlib.sha256(block.encode('utf8')).hexdigest(),
        native_header=current['native_header'], native_header_sha256=current['native_statement_hash'],
        manifest_omission_preserved=True, explicit_staged_definition_scope_bindings=stages,
        source_definition_candidate=True, standalone_source_proof_result=False))
write(CONTRACT / 'omitted-definition-context-bindings-draft-v1.json', dict(rows=bindings,
    scope='Seven definitions omitted from proof-only manifests, explicitly bound to exact complete source/definition segments and appropriate staged reviews.',
    chapter_complete=False, source_model_repair_review='pending'))

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
        source_pages=source['source_pages'], exact_source_fragment=source['historical_inclusive_fragment'],
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
