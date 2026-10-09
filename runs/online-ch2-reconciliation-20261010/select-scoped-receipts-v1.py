from common import *

fixed()
catalog = load(RUN / 'appropriate-scope-evidence-discovery-v1.json')['rows']
variants = {
    'ONLINE-OGD-MIGRATION-20261005': (2, 2, 2),
    'ONLINE-OSD-PUBLIC-20261007': (2, 2, 2),
    'ONLINE-LINEARIZATION-PUBLIC-20261007': (2, 2, 1),
    'ONLINE-CONVEX-NONDIFFERENTIABILITY-20261007': (2, 1, 1),
    'ONLINE-CONVEX-UNCOUNTABILITY-20261007': (3, 4, 4),
    'ONLINE-SUBGRADIENT-ABSOLUTE-MIGRATION-20261007': (1, 1, 2),
    'ONLINE-NORMAL-CONE-MIGRATION-20261007': (1, 2, 1),
}
special = {
    'ONLINE-CH2-NONSMOOTH-20261009': ['source-contract-repair-review-v1.json', 'nonsmooth-production-BODY-review-v1.json', 'nonsmooth-FINAL-review-v1.json', 'nonsmooth-post-native-review-v1.json', 'nonsmooth-delivery-review-v1.json'],
    'ONLINE-CH2-PRESCIENT-SOURCE-20261010': ['contract-source-review-v1.json', 'six-BODY-review-v1.json', 'FINAL-review-v1.json', 'post-native-review-v1.json', 'actual-delivery-review-v1.json'],
    'ONLINE-CH2-UNBOUNDED-OSD-20261010': ['contract-source-review-v1.json', 'full-body-canary-review-v1.json', 'FINAL-review-v1.json', 'post-native-review-v1.json', 'actual-delivery-review-v1.json'],
}
out = []
bound_files = []
for g in catalog:
    ident = g['package_id']
    run = Path(g['proposed_run'])
    s, b, f = variants.get(ident, (1, 1, 1))
    names = special.get(ident, ['source-contract-receipt-v%d.json' % s, 'public-body-receipt-v%d.json' % b, 'final-reader-receipt-v%d.json' % f])
    receipts = []
    for name in names:
        p = run / name
        data = load(p)
        assert str(data.get('verdict', '')).startswith('accepted'), p
        assert not data.get('required_repairs'), p
        discovery = next((r for r in g['candidate_scoped_receipts'] if r['path'] == p.as_posix()), None)
        assert discovery is not None, p
        report = data.get('report')
        report_row = None
        if isinstance(report, str):
            report_file = Path(report) if Path(report).is_absolute() else ROOT / report
            if report_file.is_file():
                report_row = dict(path=report_file.as_posix(), sha256=sha(report_file), recorded_report_sha256=data.get('report_sha256'))
                if data.get('report_sha256'):
                    assert report_row['sha256'] == data['report_sha256'], report_file
                bound_files.append(report_file)
        receipts.append(dict(path=p.as_posix(), sha256=sha(p), verdict=data['verdict'],
            report=report_row, exact_current_module_rows=discovery['exact_current_module_rows'],
            semantic_scope=discovery['selected_semantic_fields'],
            acceptance_boundary='Explicitly selected relevant staged receipt; old SHA mismatch and definition scope remain review questions, not automatic branch closure.'))
        bound_files.append(p)
    finals = [r for r in receipts if 'final-reader' in Path(r['path']).name or 'FINAL-review' in Path(r['path']).name]
    assert len(finals) == 1, ident
    modules = {b['module'] for b in g['exact_bound_declarations']}
    current_final = {r['module'] for r in finals[0]['exact_current_module_rows'] if r['current_complete_module_exact']}
    assert modules <= current_final, (ident, modules - current_final)
    out.append(dict(package_id=ident, manifest_path=g['manifest_path'], manifest_sha256=g['manifest_sha256'],
        source=g['source'], exact_bound_declarations=g['exact_bound_declarations'], selected_staged_receipts=receipts,
        selected_FINAL_covers_current_complete_modules=True,
        exact_definition_scope_questions=[b['declaration'] for b in g['exact_bound_declarations'] if not b['manifest_contains_declaration']],
        new_source_branch_accepted=False))
    bound_files.extend(ROOT / m for m in modules)
write(CONTRACT / 'appropriate-scope-receipt-selection-draft-v1.json', dict(rows=out,
    scope='Explicit per-package staged receipt versions; full relevant semantic judgment and historical SHA resolution pending.',
    source_inventory_changed=False, chapter_complete=False, new_mathematical_proofs=0, whole_Goal='ACTIVE'))
inputs = [CONTRACT / 'source-model-proposal-v1.md', CONTRACT / 'appropriate-scope-receipt-selection-draft-v1.json',
    CONTRACT / 'domain-structure-signature-repair-v1.json', CONTRACT / 'ancillary-signature-adapter-v1.json',
    CONTRACT / 'additional-source-bindings-draft-v1.json', CONTRACT / 'source-fingerprint-v1.json',
    RUN / 'current-online-declarations-v1.json', RUN / 'inventory-current-native-join-v1.json',
    RUN / 'appropriate-scope-evidence-discovery-v1.json', ROOT / 'AGENTS.md',
    ROOT / '.agents/skills/bandit-semantic-roundtrip/SKILL.md', PDF,
    ROOT / 'docs/contracts/online-ch2-chapter-audit-v1/complete-source-reconciliation-draft-v3.json',
    ROOT / 'runs/online-ch2-chapter-audit-20261009/source-enumeration-review-v1.md',
    ROOT / 'runs/online-ch2-chapter-audit-20261009/source-contract-repair-review-v1.md',
    ROOT / 'runs/online-ch2-chapter-audit-20261009/source-contract-repair-review-v1.json',
    ROOT / 'docs/contracts/online-book-v1/coverage.json']
inputs.extend(Path(r['path']) for r in load(CONTRACT / 'source-fingerprint-v1.json')['current_source_page_checks'])
inputs.extend(bound_files)
write(RUN / 'source-model-review-inputs-v1.json', dict(rows=rows(inputs),
    scope='Draft source model/current statement/evidence reconciliation only; no BODY changes, chapter gate or publication authorization requested.',
    output_paths=['source-model-review-v1.md', 'source-model-review-v1.json']))
fixed()
print('Explicit relevant staged receipts selected for', len(out), 'package scopes; all scoped FINAL complete-module bindings exact. Source-model review still pending.', flush=True)
