from common import *
sys.path.insert(0, str(ROOT))
from tools.abrl_lifecycle import _strip_lean_comments, lean_declaration_header, statement_hash
import difflib

fixed()
prior = load(RUN / 'staged-module-delta-resolution-v1.json')
assert len(prior['resolved_comment_only_rows']) == 40 and len(prior['unresolved_rows']) == 2
supplements = []
for row in prior['unresolved_rows']:
    module = ROOT / row['module']
    if row['package_id'] == 'ONLINE-REGRET-DOMAINS-20261007':
        provenance = ROOT / 'runs/online-regret-domains-20261007/body-reviewed-source-resolution-v1.json'
        recorded = load(provenance)
        snapshot = Path(recorded['immutable_snapshot'])
        assert sha(snapshot) == row['staged_complete_module_sha256'] == recorded['reviewed_sha256']
        normalize = lambda s: '\n'.join(line.strip() for line in _strip_lean_comments(s).splitlines() if line.strip())
        a = normalize(snapshot.read_text(encoding='utf8'))
        b = normalize(module.read_text(encoding='utf8'))
        assert a == b
        supplements.append(dict(original_unresolved_row=row, resolution='actual RAW snapshot plus exact complete visible code equality',
            snapshot=dict(path=snapshot.as_posix(), sha256=sha(snapshot)),
            original_resolution=dict(path=provenance.as_posix(), sha256=sha(provenance)),
            visible_code_sha256=hashlib.sha256(a.encode('utf8')).hexdigest(), mathematical_code_delta=False,
            boundary='Documentation insertion only, not a fresh semantic review. Appropriate original BODY and exact current scoped FINAL remain required.'))
    else:
        assert row['package_id'] == 'ONLINE-SUBGRADIENT-INTERIOR-MIGRATION-20261006'
        run = ROOT / 'runs/online-subgradient-interior-migration-20261006'
        source_receipt = run / 'source-contract-receipt-v1.json'
        body_receipt = run / 'public-body-receipt-v1.json'
        final_receipt = run / 'final-reader-receipt-v1.json'
        actual_binding = run / 'public-actual-bindings-v1.json'
        src, body, final, binding = [load(p) for p in [source_receipt, body_receipt, final_receipt, actual_binding]]
        names = ['BanditRL.OnlineConvex.' + n for n in binding['frozen_headers']]
        assert len(names) == 3
        for name in names:
            assert name in src['target_verdicts'] and name in body['target_verdicts'] and name in final['target_verdicts']
            assert statement_hash(lean_declaration_header(module, name)) == binding['frozen_headers'][name.rsplit('.', 1)[1]], name
        snapshot = Path(row['matching_retained_snapshots'][0]['path'])
        a = _strip_lean_comments(snapshot.read_text(encoding='utf8'))
        b = _strip_lean_comments(module.read_text(encoding='utf8'))
        a_lines = [x.strip() for x in a.splitlines() if x.strip()]
        b_lines = [x.strip() for x in b.splitlines() if x.strip()]
        assert b_lines[:len(a_lines)] == a_lines
        assert all('theorem ' + n.rsplit('.', 1)[1] not in a for n in names if 'relative' in n)
        added_names = [n for n in names if 'relative' in n]
        assert len(added_names) == 2
        diff_text = '\n'.join(difflib.unified_diff(a_lines, b_lines,
            fromfile='exact staged original visible code', tofile='current visible code'))
        write(RUN / 'interior-staged-visible-code-delta-v1.diff', diff_text)
        body_module = [r for r in body['reviewed_files'] if r.get('path') == row['module']]
        final_module = [r for r in final['reviewed_files'] if r.get('path') == row['module']]
        assert len(body_module) == len(final_module) == 1
        assert body_module[0]['sha256'] == final_module[0]['sha256'] == sha(module)
        supplements.append(dict(original_unresolved_row=row,
            resolution='Expected proving-stage addition of two separately CONTRACT/BODY/FINAL-reviewed relative-interior producers; not comment-only preservation',
            retained_original_visible_code_is_current_prefix=True, added_proof_terminals=added_names,
            source_contract_scope=src['scope'], exact_frozen_headers=binding['frozen_headers'],
            actual_current_BODY_complete_module_sha256=body_module[0]['sha256'],
            actual_current_FINAL_complete_module_sha256=final_module[0]['sha256'],
            proof_stage_receipts=rows([source_receipt, body_receipt, final_receipt, actual_binding, snapshot]),
            target_semantic_source_verdicts=src['target_verdicts'], target_actual_BODY_verdicts=body['target_verdicts'],
            mathematical_code_delta=True, newly_authored_this_run=False,
            boundary='Two real proof additions were planned and independently reviewed in their own historical package; keep the source-stage full-module mismatch rather than mislabel it comment-only. Exact three frozen headers and current BODY/FINAL bytes now joined.'))
write(RUN / 'staged-module-delta-supplement-v1.json', dict(rows=supplements,
    original_unresolved_rows_preserved=True, total_original_mismatch_rows=42,
    comment_only_rows=41, distinct_proving_stage_added_module_rows=1,
    semantic_disposition='pending bounded review of the explicit provenance resolution; no chapter acceptance'))
fixed()
print('Both residual staged module rows resolved with explicit different reasons; original mismatches retained.', flush=True)
