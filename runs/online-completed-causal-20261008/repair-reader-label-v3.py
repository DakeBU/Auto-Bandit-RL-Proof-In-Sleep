from common_reader_v2 import *
from commit_owned_v1 import commit_owned

fixed_integrated()
assert load(RUN / 'formula-render-v2-node-exit.json')['actual_exit'] == 1
diagnostic = load(RUN / 'overflow-source-card-diagnostic-v3.json')
assert diagnostic['diagnosticOnly'] and not diagnostic['renderingPassClaim']
assert diagnostic['geometry']['box']['right'] > 1440
proposal = load(RUN / 'reader-proposal-v2.json')
old_label = proposal['card']['local_status']['label']
new_label = 'Four public proofs + 11 canaries compiled locally; package gates pending'
proposal['card']['local_status']['label'] = new_label
write(RUN / 'reader-proposal-v3.json', proposal)
p = ROOT / 'website/content/readings.json'
write(RUN / 'snapshots/reader-label-before-v3.raw', p.read_bytes())
data = load(p); row = next(x for x in data['readings'] if x['slug'] == ROUTE)
assert row['source_theorems'][-1] == load(RUN / 'reader-proposal-v2.json')['card']
row['source_theorems'][-1]['local_status']['label'] = new_label
p.write_bytes((json.dumps(data, ensure_ascii=False, indent=2) + '\n').encode('utf8'))
source = (RUN / 'common_reader_v2.py').read_text(encoding='utf8')
write(RUN / 'common_reader_v3.py', source.replace('reader-proposal-v2.json', 'reader-proposal-v3.json'))
write(RUN / 'reader-label-repair-v3.json', dict(
    actual_failed_capture_receipt='formula-render-v2-node-exit.json',
    diagnostic_geometry_sha256=sha(RUN / 'overflow-source-card-diagnostic-v3.json'),
    diagnostic_original_pixel_personally_viewed_by_formalizer=True,
    cause='Long nowrap status badge expands the source card grid beyond the viewport; formula itself fits after v2 line breaks.',
    old_label=old_label, new_label=new_label,
    exact_only_local_status_label_changed=True,
    full_assumptions_conclusions_source_delta_boundary_and_every_old_entry_preserved=True,
    no_global_CSS_generator_or_generated_site_edit=True,
    previous_two_failures_and_original_diagnostic_retained=True))
for filename in ['build-clean-site-v2.py', 'verify-registry-v2.py', 'capture-reader-v2.py']:
    source = (RUN / filename).read_text(encoding='utf8')
    source = source.replace('common_reader_v2', 'common_reader_v3')
    for prefix in ['online-completed-causal-site', 'online-completed-causal-site-build',
        'online-completed-causal-playwright', 'site-build', 'site-check', 'registry-check',
        'verify-registry', 'registry', 'capture-reader', 'formula-render', 'reader-proposal']:
        source = source.replace(prefix + '-v2', prefix + '-v3')
    write(RUN / filename.replace('-v2.py', '-v3.py'), source)
source = (RUN / 'capture-reader-v2.cjs').read_text(encoding='utf8')
write(RUN / 'capture-reader-v3.cjs', source.replace('-v2.', '-v3.').replace('-v2.png', '-v3.png'))
source = (RUN / 'common_accepted_v2.py').read_text(encoding='utf8')
write(RUN / 'common_accepted_v3.py', source.replace('common_reader_v2', 'common_reader_v3')
      .replace('formula-render-v2.json', 'formula-render-v3.json'))
for filename in ['record-acceptance-v2.py', 'prepare-post-native-review-v2.py',
                 'prepare-reviewed-commit-v2.py', 'deliver-reviewed-draft-v2.py']:
    source = (RUN / filename).read_text(encoding='utf8')
    source = source.replace('common_accepted_v2', 'common_accepted_v3').replace('registry-v2.json', 'registry-v3.json')
    source = source.replace('genuine v2 browser/DOM/capture evidence; actual v1 overflow retained',
                            'genuine v3 browser/DOM/capture evidence; actual v1/v2 overflow and v3 diagnostic retained')
    write(RUN / filename.replace('-v2.py', '-v3.py'), source)
source = (RUN / 'prepare-FINAL-review-v2.py').read_text(encoding='utf8')
source = source.replace('common_reader_v2', 'common_reader_v3')
for prefix in ['pixel-review', 'registry', 'site-build', 'site-check', 'registry-check',
               'formula-render', 'online-completed-causal-site', 'contributor-current-stacked',
               'contributor-current-origin-main']:
    source = source.replace(prefix + '-v2', prefix + '-v3')
source = source.replace('source-card aligned line-break repair',
                        'source-card aligned line-break/shorter truthful badge repair and actual two overflow failures')
write(RUN / 'prepare-FINAL-review-v3.py', source)
from common_reader_v3 import fixed_integrated as fixed_repaired
fixed_repaired()
commit_owned('Shorten own status badge after measured source card overflow')
command = [sys.executable, '-B', '-X', 'utf8', str(RUN / 'build-clean-site-v3.py')]
child = subprocess.run(command)
write(RUN / 'clean-local-site-workflow-v3-exit.json', dict(command=command,
    actual_exit=child.returncode, outer_stdout_inherited=True,
    combined_Lean_gate_applicable_without_new_proof_change=True, rendering_FINAL_pending=True))
assert child.returncode == 0
