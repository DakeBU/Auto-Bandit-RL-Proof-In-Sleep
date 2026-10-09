from common import *
sys.path.insert(0, str(ROOT))
from tools.abrl_lifecycle import _strip_lean_comments

fixed()
selected = load(CONTRACT / 'appropriate-scope-receipt-selection-draft-v1.json')['rows']
resolved = []
unresolved = []
for group in selected:
    run = Path(group['selected_staged_receipts'][0]['path']).parent
    candidate_files = set(run.glob('*.txt')) | set(run.glob('*.lean'))
    for receipt in group['selected_staged_receipts']:
        data = load(receipt['path'])
        for row in data.get('reviewed_files', []):
            if not isinstance(row, dict) or not isinstance(row.get('path'), str):
                continue
            p = Path(row['path'])
            p = p if p.is_absolute() else ROOT / p
            if p.is_file() and (p.name.endswith('.lean.txt') or p.name.endswith('.lean')):
                candidate_files.add(p)
    hashes = {}
    for p in candidate_files:
        hashes.setdefault(sha(p), []).append(p)
    for receipt in group['selected_staged_receipts']:
        for module in receipt['exact_current_module_rows']:
            if module['current_complete_module_exact']:
                continue
            wanted = module['review_sha256']
            source = ROOT / module['module']
            snapshots = hashes.get(wanted, [])
            result = dict(package_id=group['package_id'], staged_receipt=receipt['path'], staged_receipt_sha256=receipt['sha256'],
                module=module['module'], staged_complete_module_sha256=wanted, current_complete_module_sha256=sha(source),
                matching_retained_snapshots=[dict(path=p.as_posix(), sha256=sha(p)) for p in snapshots])
            if snapshots:
                original = snapshots[0].read_text(encoding='utf8')
                current = source.read_text(encoding='utf8')
                normalize = lambda s: '\n'.join(line.strip() for line in _strip_lean_comments(s).splitlines() if line.strip())
                a, b = normalize(original), normalize(current)
                result.update(comment_stripped_nonempty_trimmed_lines_equal=a == b,
                    staged_visible_code_sha256=hashlib.sha256(a.encode('utf8')).hexdigest(),
                    current_visible_code_sha256=hashlib.sha256(b.encode('utf8')).hexdigest(),
                    normalization_authority='Existing tools.abrl_lifecycle._strip_lean_comments plus only per-line outer whitespace/empty-line removal. String contents and internal whitespace are retained.',
                    boundary='Mechanical preservation of complete visible Lean code between actual retained staged bytes and current module; source semantics and receipt scope still need explicit review.')
                if a == b:
                    resolved.append(result)
                else:
                    result['unresolved_reason'] = 'Visible complete code differs; cannot reuse staged BODY merely by later FINAL hash.'
                    unresolved.append(result)
            else:
                result['unresolved_reason'] = 'No actual retained source snapshot with this staged RAW hash found among the bounded package files/reviewed Lean snapshots.'
                unresolved.append(result)
write(RUN / 'staged-module-delta-resolution-v1.json', dict(resolved_comment_only_rows=resolved,
    unresolved_rows=unresolved, old_receipts_or_sources_modified=False,
    comparison_helper=dict(path=(ROOT / 'tools/abrl_lifecycle.py').as_posix(), sha256=sha(ROOT / 'tools/abrl_lifecycle.py')),
    chapter_complete=False, mathematical_new_proofs=0))
fixed()
print('Staged module differences: resolved exact visible code', len(resolved), 'unresolved', len(unresolved), flush=True)
for r in unresolved:
    print(r['package_id'], Path(r['staged_receipt']).name, r['module'], r['unresolved_reason'], flush=True)
