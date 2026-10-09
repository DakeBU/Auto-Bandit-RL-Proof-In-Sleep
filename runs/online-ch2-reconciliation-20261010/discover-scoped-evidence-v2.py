from common import *
from collections import defaultdict
import re

fixed()
inv = load(ROOT / 'docs/contracts/online-ch2-chapter-audit-v1/complete-source-reconciliation-draft-v3.json')
manifests = load(RUN / 'current-online-manifest-candidates-v1.json')['rows']
by_name = defaultdict(list)
for m in manifests:
    for n in m['declarations']:
        by_name[n].append(m)
public_overrides = {
    'BanditRL.OnlineSubgradientDescent.': 'ONLINE-OSD-PUBLIC-20261007',
    'BanditRL.OnlineSubgradientPolicy.': 'ONLINE-OSD-POLICY-PUBLIC-20261007',
    'BanditRL.OnlineGuessingSubgradient.': 'ONLINE-GUESSING-PUBLIC-20261007',
    'BanditRL.OnlineUnitScaling.': 'ONLINE-UNIT-SCALING-PUBLIC-20261007',
    'BanditRL.OnlineLinearization.': 'ONLINE-LINEARIZATION-PUBLIC-20261007',
    'BanditRL.OnlineOptimalStep.': 'ONLINE-OPTIMAL-STEP-PUBLIC-20261007',
}
groups = {}
for r in inv['rows']:
    for b in r.get('exact_current_terminal_bindings', []):
        name = b['declaration']
        candidates = by_name[name]
        override = next((v for k, v in public_overrides.items() if name.startswith(k)), None)
        if override:
            selected = next(m for m in manifests if m['id'] == override)
            reason = 'Explicit current public-reuse package for this canonical namespace; old implementation manifest alone is not its later source review. Definitions omitted from the proof-only manifest remain explicit whole-module scope questions, not silently accepted.'
        elif name == 'BanditRL.OnlineLearning.ftlPredict':
            selected = next(m for m in manifests if m['id'] == 'ONLINE-FTL-STATE-20261007')
            reason = 'Definition in complete OnlineLearningFTLState module, together with source-mapped ftlState_eq_predict. Manifest does not list this definition; exact definition/whole-module semantic scope must be reviewed explicitly.'
        else:
            choices = [m for m in candidates if m['path'].replace(ROOT.as_posix() + '/', '') in b.get('contribution_manifests', [])]
            assert choices, name
            migration = [m for m in choices if 'MIGRATION' in m['id']]
            selected = migration[-1] if migration else choices[-1]
            reason = 'Source inventory named this package; prefer the explicit later migration where present. Selection remains a proposed appropriate scope, not acceptance from metadata.'
        ident = selected['id']
        if ident not in groups:
            groups[ident] = dict(manifest=selected, bindings={})
        if name not in groups[ident]['bindings']:
            groups[ident]['bindings'][name] = dict(declaration=name, module=b['module'],
                current_complete_module_sha256=b['complete_scope_and_BODY_sha256'],
                historical_native_statement_hash=b['native_statement_hash'],
                manifest_contains_declaration=name in selected['declarations'], selection_reason=reason,
                source_containers=[])
        groups[ident]['bindings'][name]['source_containers'].append(r['source_id'])

for source_id, extra in load(CONTRACT / 'additional-source-bindings-draft-v1.json')['rows'].items():
    m = next(m for m in manifests if m['path'] == extra['manifest_path'])
    ident = m['id']
    assert ident not in groups
    groups[ident] = dict(manifest=m, bindings={})
    for b in extra['current_targets']:
        groups[ident]['bindings'][b['full_name']] = dict(declaration=b['full_name'], module=b['file'],
            current_complete_module_sha256=b['source_file_sha256'], historical_native_statement_hash=b['native_statement_hash'],
            manifest_contains_declaration=True, selection_reason='New source-container binding candidate; package-specific actual later review/delivery must be joined.', source_containers=[source_id])

catalog = []
for ident, group in sorted(groups.items()):
    run = ROOT / 'runs' / ident.lower()
    if ident == 'ONLINE-CH2-NONSMOOTH-20261009':
        run = ROOT / 'runs/online-ch2-chapter-audit-20261009'
    assert run.is_dir(), run
    relevant = []
    for p in sorted(run.glob('*.json')):
        if ident == 'ONLINE-CH2-NONSMOOTH-20261009' and not (p.name.startswith('nonsmooth-') or p.name == 'source-contract-repair-review-v1.json'):
            continue
        if not any(s in p.name.lower() for s in ['receipt', 'review', 'decision', 'delivery', 'acceptance', 'accepted-binding']):
            continue
        data = load(p)
        if not isinstance(data, dict):
            continue
        if not any(k in data for k in ['verdict', 'scope', 'reviewer', 'accepted', 'delivery']):
            continue
        selected_fields = {k: v for k, v in data.items() if k in [
            'schema', 'scope', 'verdict', 'decision', 'actor', 'reviewer', 'required_repairs', 'required_mathematical_repairs',
            'required_reader_corrections', 'explicit_deltas', 'remaining_gaps', 'remaining_gates', 'boundary', 'chapter_complete',
            'remaining_boundary', 'target_verdicts', 'body_accepted', 'raw_drift', 'fixed_input_rows', 'report', 'report_sha256',
            'source_inventory_sha256', 'publication_scope', 'accepted_source_commit', 'accepted_head', 'pr_url']}
        current_modules = []
        module_checks = data.get('reviewed_files', [])
        if isinstance(module_checks, list):
            for row in module_checks:
                if not isinstance(row, dict) or not isinstance(row.get('path'), str):
                    continue
                path = row['path'].replace('\\', '/')
                if path.startswith(ROOT.as_posix() + '/'):
                    path = path[len(ROOT.as_posix()) + 1:]
                wanted = [b for b in group['bindings'].values() if b['module'] == path]
                if wanted:
                    current_modules.append(dict(module=path, review_sha256=row.get('sha256'),
                        current_sha256=sha(ROOT / path), current_complete_module_exact=row.get('sha256') == sha(ROOT / path)))
        relevant.append(dict(path=p.as_posix(), sha256=sha(p), selected_semantic_fields=selected_fields,
            exact_current_module_rows=current_modules,
            boundary='Integrity/appropriate-scope discovery only. Empty module rows are unresolved, not acceptance; historical mismatch may be explained by staged edits but cannot silently pass.'))
    catalog.append(dict(package_id=ident, proposed_run=run.as_posix(), manifest_path=group['manifest']['path'],
        manifest_sha256=group['manifest']['sha256'], source=group['manifest']['source'],
        exact_bound_declarations=list(group['bindings'].values()), candidate_scoped_receipts=relevant,
        proposed_scope_only=True, accepted_source_branches=[]))
write(RUN / 'appropriate-scope-evidence-discovery-v1.json', dict(rows=catalog,
    source_inventory_unchanged=True, production_or_reader_edited=False,
    boundary='Selection of candidate relevant package scopes and receipts. No automatic selection by accepted status, no source/chapter acceptance, no new mathematics.'))
summary = [dict(package_id=g['package_id'], bound_declarations=len(g['exact_bound_declarations']),
    receipts=[dict(name=Path(r['path']).name, verdict=r['selected_semantic_fields'].get('verdict'),
        scope=r['selected_semantic_fields'].get('scope'), exact_current_modules=sum(x['current_complete_module_exact'] for x in r['exact_current_module_rows']),
        mismatched_modules=sum(not x['current_complete_module_exact'] for x in r['exact_current_module_rows'])) for r in g['candidate_scoped_receipts']]) for g in catalog]
write(RUN / 'appropriate-scope-discovery-summary-v1.json', summary)
fixed()
print('Candidate appropriate package scopes:', len(catalog), 'distinct bound names:', len({b['declaration'] for g in catalog for b in g['exact_bound_declarations']}), flush=True)
for g in summary:
    print(g['package_id'], g['bound_declarations'], 'candidate receipts', len(g['receipts']), flush=True)
