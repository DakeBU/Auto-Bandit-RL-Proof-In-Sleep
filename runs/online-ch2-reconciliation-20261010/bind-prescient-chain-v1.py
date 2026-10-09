from generic_ftl_proof import *

fixed()
index = load(RUN / 'current-online-declarations-v1.json')['rows']
profiles = [
    ('online-ch2-proximal-20261009', 'OnlineProximalComparison',
     ['contract-review-v1.json', 'BODY-canary-contract-review-v1.json', 'FINAL-review-v1.json']),
    ('online-ch2-bregman-20261009', 'OnlineBregmanProximal',
     ['contract-review-v1.json', 'BODY-canary-contract-review-v1.json', 'FINAL-review-v1.json']),
    ('online-ch2-extended-proximal-20261009', 'OnlineBregmanExtended',
     ['contract-review-v1.json', 'BODY-canary-contract-review-v1.json', 'FINAL-review-v1.json']),
    ('online-ch2-prescient-causal-20261009', 'OnlinePrescientBregman',
     ['contract-review-v1.json', 'BODY-canary-contract-review-v1.json', 'FINAL-review-v1.json']),
    ('online-ch2-prescient-cumulative-20261009', 'OnlinePrescientBregmanRegret',
     ['CONTRACT-review-v1.json', 'five-BODY-review-v1.json', 'FINAL-review-v1.json']),
    ('online-ch2-prescient-source-20261010', 'OnlinePrescientBregmanSource',
     ['contract-source-review-v1.json', 'six-BODY-review-v1.json', 'FINAL-review-v1.json']),
]
bindings = []
names = []
for ident, module_name, stages in profiles:
    module = ROOT / 'BanditRLProof' / (module_name + '.lean')
    declarations = [row for row in index if row['file'] == module.relative_to(ROOT).as_posix()]
    assert declarations
    names.extend(row['full_name'] for row in declarations)
    receipts = []
    for stage_index, name in enumerate(stages):
        receipt = ROOT / 'runs' / ident / name
        data = load(receipt)
        assert data['verdict'].startswith('accepted') and not data.get('required_repairs')
        report = ROOT / data['report']
        assert sha(report) == data['report_sha256']
        raw_rows = data['reviewed_files']
        matched = [row for row in raw_rows if (ROOT / row['path']).resolve() == module.resolve()]
        if stage_index:
            assert len(matched) == 1 and matched[0]['sha256'] == sha(module), (ident, name)
        else:
            assert not matched, (ident, 'source CONTRACT is preimplementation; bind frozen context separately')
        frozen_context = []
        for row in raw_rows:
            p = ROOT / row['path']
            if '/docs/contracts/' in p.as_posix():
                assert sha(p) == row['sha256'], p
                frozen_context.append(dict(path=p.as_posix(), sha256=sha(p)))
        assert frozen_context
        receipts.append(dict(stage=['source-CONTRACT', 'production-BODY', 'FINAL'][stage_index],
            receipt=dict(path=receipt.as_posix(), sha256=sha(receipt)),
            report=dict(path=report.as_posix(), sha256=sha(report)),
            exact_current_complete_module_bound=bool(matched), frozen_contract_context=frozen_context,
            semantic_scope=dict((k, v) for k, v in data.items() if k not in ['reviewed_files', 'raw_input_checks']),
            distinction='Source CONTRACT freezes definitions/headers before implementation; BODY/FINAL bind the actual complete current module.'))
    bindings.append(dict(package=ident, module=module.relative_to(ROOT).as_posix(),
        current_complete_module_sha256=sha(module), declarations=declarations,
        appropriate_staged_reviews=receipts,
        current_reconciliation_semantic_review='pending', newly_proved=False))
assert len(names) == 31
ftl_names = ['BanditRL.OnlineFTLSelector.' + n for n in ['cumulative', 'minimizers', 'select', 'predict']]
ftl_names += [row['declaration'] for row in load(LEAF / 'frozen-headers-draft-v1.json')['rows']]
selected = names + ftl_names
template = ROOT / 'runs/online-ch2-prescient-source-20261010/export-selected-dependencies-v1.lean'
script = template.read_text(encoding='utf8')
script = script.replace('import Tests.OnlinePrescientBregmanSourceCanary',
    'import BanditRLProof.OnlinePrescientBregmanSource\nimport BanditRLProof.OnlineFTLSelector')
script = script.replace('Lean.importModules #[{ module := `Tests.OnlinePrescientBregmanSourceCanary }]',
    'Lean.importModules #[{ module := `BanditRLProof.OnlinePrescientBregmanSource }, { module := `BanditRLProof.OnlineFTLSelector }]')
a = script.index('def targets : Array Name := #[')
b = script.index('\n\ndef moduleName', a)
script = script[:a] + 'def targets : Array Name := #[\n' + ',\n'.join('`' + n for n in selected) + ']' + script[b:]
script = script.replace('(\"root_module\", toJson \"BanditRLProof\")',
    '(\"root_module\", toJson \"selected-production-module-union\")')
script = script.replace('Six frozen production proofs and two complete concrete Test conjunctions plus referenced compiler-generated Test auxiliaries. Selected direct TYPE_VALUE constant presences; not occurrence counts, full transitive graph, shared registry or chapter/source theorem denominator.',
    '31 prescient parent/source declarations plus 13 generic FTL declarations from their actual compiled module union. Direct TYPE_VALUE constant presences only; not occurrence counts, a complete transitive graph, a root gate, shared registry update or independent source-result denominator.')
assert 'Tests.OnlinePrescientBregmanSourceCanary }]' not in script
write(RUN / 'ExportReconciliationValuesV1.lean', script)
capture('reconciliation-selected-values-v1', 'lake', 'env', 'lean', '--run',
    RUN / 'ExportReconciliationValuesV1.lean', RUN / 'reconciliation-selected-value-graph-v1.json')
graph = load(RUN / 'reconciliation-selected-value-graph-v1.json')
nodes = {node['name']: node for node in graph['nodes']}
assert len(nodes) == len(selected) == 44
assert set(selected) == set(nodes) and all(nodes[n]['has_value'] for n in selected)
parent_edges = []
for name in names:
    for parent in nodes[name]['value_dependencies']:
        if parent in names:
            parent_edges.append(dict(child=name, parent=parent, evidence='actual compiled VALUE direct constant presence'))
assert parent_edges
write(CONTRACT / 'prescient-complete-chain-bindings-draft-v1.json', dict(
    packages=bindings, total_selected_parent_source_declarations=31,
    actual_compiled_graph=rows([RUN / 'reconciliation-selected-value-graph-v1.json', RUN / 'reconciliation-selected-values-v1.json']),
    direct_VALUE_edges_within_selected_chain=parent_edges,
    boundary='Imports are not proof dependencies. Only extracted direct VALUE presences are formal edges; staged source/semantic ownership is a distinct overlay. No fresh proof productivity claimed for historical parents.',
    linear_auxiliary='OnlinePrescientLinear is a separately reviewed constrained linear/canary instantiation, not an asserted generic formal parent.',
    R3_bounded_source_model_reviewer_verdict='pending', chapter_complete=False, whole_Goal='ACTIVE'))
write(RUN / 'generic-ftl-production-value-inspection-v1.json', dict(
    module=rows([MODULE]), graph=rows([RUN / 'reconciliation-selected-value-graph-v1.json']),
    selected_nodes=[nodes[n] for n in ftl_names], exact_count=13,
    standard_axioms_receipt=rows([RUN / 'generic-ftl-public-and-axioms-v1.json']),
    semantic_BODY_review='pending', public_Test_canaries='not yet authored', combined_gate=False))
fixed()
print('Actual VALUE extraction: 44 selected production values; 31-declaration six-package prescient chain bound, reconciliation review pending.', flush=True)
