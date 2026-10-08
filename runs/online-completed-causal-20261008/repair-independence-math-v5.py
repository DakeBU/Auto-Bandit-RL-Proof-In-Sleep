from common_reader_v3 import *
from commit_owned_v1 import commit_owned

fixed_integrated()
proposal = load(RUN / 'reader-proposal-v3.json')
old = proposal['notes'][2]['math']; needle = r'\\(Y_t)'
assert old.count(needle) == 1
new = old.replace(needle, r'\\ {}(Y_t)')
assert r'\(' not in new
proposal['notes'][2]['math'] = new
write(RUN / 'reader-proposal-v5.json', proposal)
p = ROOT / 'website/content/highlights.json'
write(RUN / 'snapshots/independence-math-before-v5.raw', p.read_bytes())
data = load(p)
row = next(x for x in data['highlights'] if x['full_name'] == proposal['notes'][2]['full_name'])
assert row == load(RUN / 'reader-proposal-v3.json')['notes'][2]
row['math'] = new
p.write_bytes((json.dumps(data, ensure_ascii=False, indent=2) + '\n').encode('utf8'))
write(RUN / 'common_reader_v5.py', (RUN / 'common_reader_v3.py').read_text(encoding='utf8')
    .replace('reader-proposal-v3.json', 'reader-proposal-v5.json'))
write(RUN / 'independence-math-repair-v5.json', dict(
    actual_original_pixel='public-note-3-v3.png', original_sha256=sha(RUN / 'public-note-3-v3.png'),
    formalizer_personally_viewed_original=True, incorrect_red_command=r'\Y',
    actual_DOM_sha256=sha(RUN / 'formula-render-v1-dom.html'),
    cause='normalize_math_source treats the second slash in a TeX rowbreak immediately followed by left parenthesis as an unmatched inline opener; delimiter stripping creates an unknown command.',
    old_math=old, new_math=new, exact_only_empty_group_space_at_rowbreak=True,
    mathematical_statement_unchanged=True, previous_successful_Node_mjx_merror_check_missed_red_unknown_command=True,
    prior_browser_pass_not_pixel_acceptance=True, no_global_generator_CSS_or_old_entry_edit=True))
for filename in ['build-clean-site-v3.py', 'verify-registry-v3.py', 'capture-reader-v3.py']:
    source = (RUN / filename).read_text(encoding='utf8').replace('common_reader_v3', 'common_reader_v5')
    for prefix in ['online-completed-causal-site', 'online-completed-causal-site-build',
        'online-completed-causal-playwright', 'site-build', 'site-check', 'registry-check',
        'verify-registry', 'registry', 'capture-reader', 'formula-render', 'reader-proposal']:
        source = source.replace(prefix + '-v3', prefix + '-v5')
    write(RUN / filename.replace('-v3.py', '-v5.py'), source)
source = (RUN / 'capture-reader-v3.cjs').read_text(encoding='utf8')
source = source.replace('-v3.png', '-v5.png')
source = source.replace('formula-render-v1-dom.html', 'formula-render-v5-dom.html')
source = source.replace('formula-render-v1-browser.json', 'formula-render-v5-browser.json')
source = source.replace("el.querySelectorAll('mjx-merror').length",
    "el.querySelectorAll('mjx-merror, [mathcolor=\"red\"], [data-mjx-error]').length")
assert 'formula-render-v1-' not in source
write(RUN / 'capture-reader-v5.cjs', source)
source = (RUN / 'common_accepted_v4.py').read_text(encoding='utf8')
write(RUN / 'common_accepted_v5.py', source.replace('common_reader_v3', 'common_reader_v5')
    .replace('formula-render-v4.json', 'formula-render-v5.json'))
for filename in ['record-acceptance-v4.py', 'prepare-post-native-review-v4.py',
                 'prepare-reviewed-commit-v4.py', 'deliver-reviewed-draft-v4.py']:
    source = (RUN / filename).read_text(encoding='utf8').replace('common_accepted_v4', 'common_accepted_v5')
    source = source.replace('registry-v3.json', 'registry-v5.json')
    source = source.replace('actual v3 capture/v1-named browser outputs bound by audit-v4; two overflow failures/diagnostic/filename failure retained',
        'actual v5 original captures/browser/DOM, including red math-error check; overflow/filename/red-command failures retained')
    write(RUN / filename.replace('-v4.py', '-v5.py'), source)
source = (RUN / 'prepare-FINAL-review-v4.py').read_text(encoding='utf8').replace('common_reader_v3', 'common_reader_v5')
for old, new in [('pixel-review-v4', 'pixel-review-v5'), ('formula-render-v4', 'formula-render-v5'),
    ('registry-v3', 'registry-v5'), ('site-build-v3', 'site-build-v5'), ('site-check-v3', 'site-check-v5'),
    ('registry-check-v3', 'registry-check-v5'), ('online-completed-causal-site-v3', 'online-completed-causal-site-v5'),
    ('contributor-current-stacked-v3', 'contributor-current-stacked-v5'),
    ('contributor-current-origin-main-v3', 'contributor-current-origin-main-v5')]:
    source = source.replace(old, new)
source = source.replace('actual v3 browser math/geometry/wrap checks, genuine v1-named browser/DOM outputs, failed Python-v3 filename lookup and exact audit-v4 binding without rerender/rename',
    'actual v5 browser math/geometry/wrap checks including red unknown-command detection and v5-named outputs; preserve actual v3 success/v1-named output audit-v4 and its failed outer filename lookup. Formalizer original pixel review found red unknown command missed by mjx-merror alone, exact empty-group repair-v5 changes no mathematics')
source = source.replace('receipt-reader/capture-output filename failures',
    'receipt-reader/capture-output filename/red-command rendering failures')
write(RUN / 'prepare-FINAL-review-v5.py', source)
from common_reader_v5 import fixed_integrated as fixed_repaired
fixed_repaired()
commit_owned('Repair new independence formula after original pixel inspection')
command = [sys.executable, '-B', '-X', 'utf8', str(RUN / 'build-clean-site-v5.py')]
child = subprocess.run(command)
write(RUN / 'clean-local-site-workflow-v5-exit.json', dict(command=command,
    actual_exit=child.returncode, outer_stdout_inherited=True,
    combined_Lean_gate_applicable_without_proof_changes=True, fresh_v5_capture_FINAL_pending=True))
assert child.returncode == 0
