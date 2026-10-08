from common_integrated_v2 import *

fixed_integrated()
r = load(RUN/'final-reader-receipt-v2.json')
assert r['actor']['task'] == '/root/source_reviewer' and r['verdict'] == 'rejected'
assert r['fixed_input_count'] == 778
for row in load(RUN/'final-reader-inputs-v2.json')['rows']:
    assert sha(row['path']) == row['sha256'], row['path']
path = Path('website/content/highlights.json')
write(RUN/'reader-before-semantic-repair-v6.json.raw', path.read_bytes())
before = load(path)
data = load(path)
production = load(MANIFEST)['reuse_plan']['new_shared_declarations']
notes = [x for x in data['highlights'] if x['full_name'] in production]
assert len(notes) == 8
for note in notes:
    assert note['intuition'] == 'Keep expectation outside the comparator minimum and derive the actual strict-past information condition.'
    note['intuition'] = 'Minimize expected cumulative loss over one fixed comparator; expectation stays inside that minimization. For causal predictions, derive current-target independence from the strict past.'
mean_note = next(x for x in notes if x['full_name'] == PRE+'meanPredict_expectedFixed_excess')
old_math = mean_note['math']
assert old_math.endswith(r'x_t=t^{-1}\sum_{i<t}Y_i.')
mean_note['math'] = old_math[:-1]+r'\quad(t>0).'
for old, new in zip(before['highlights'], data['highlights']):
    allowed = {'intuition'} if old['full_name'] in production else set()
    if old['full_name'] == PRE+'meanPredict_expectedFixed_excess':
        allowed.add('math')
    assert {k:v for k,v in old.items() if k not in allowed} == {k:v for k,v in new.items() if k not in allowed}
assert {k:v for k,v in before.items() if k != 'highlights'} == {k:v for k,v in data.items() if k != 'highlights'}
path.write_bytes((json.dumps(data, ensure_ascii=False, indent=2)+'\n').encode('utf8'))
write(RUN/'reader-semantic-repair-v9.json', dict(status='Actual reader-only repair; fresh site/pixels/distinct FINAL required.',
    rejected_FINAL_report_sha256=sha(RUN/'final-reader-review-v2.md'), rejected_FINAL_receipt_sha256=sha(RUN/'final-reader-receipt-v2.json'),
    original_FINAL_inputs_778_unchanged_at_rejection=True,
    findings=['F1 all eight Intuition fields reversed min E wording', 'F2 meanPredict positive-time averaging formula lacked t>0'],
    repair='Only eight new note intuition fields and explicit t>0 qualifier of note6 averaging formula changed.',
    unchanged='All old notes/cards, source text, Lean statements/bodies/canaries/root/pins/CONTRACT/BODY raw bindings.',
    formalizer_original_pixel_review_missed_semantic_contradiction=True,
    no_mathematical_repair_or_terminal_weakening=True, FINAL_pending=True, package_accepted=False, chapter_complete=False, goal_complete=False))
for name in ['verify-registry', 'capture-reader']:
    for suffix in (['.py', '.cjs'] if name == 'capture-reader' else ['.py']):
        text = (RUN/(name+'-v6'+suffix)).read_text(encoding='utf8')
        text = text.replace('-site-v6', '-site-v9').replace('registry-v6', 'registry-v9').replace('capture-reader-v6', 'capture-reader-v9')
        text = text.replace('formula-render-v6', 'formula-render-v9').replace('-viewport-v6', '-viewport-v9')
        text = text.replace('source-card-v6', 'source-card-v9').replace('note-${i+1}-v6', 'note-${i+1}-v9').replace('declaration-${i+1}-v6', 'declaration-${i+1}-v9')
        if name == 'verify-registry':
            text = text.replace("for phrase in ['not eight", "for phrase in ['expectation stays inside that minimization', 'not eight")
        write(RUN/(name+'-v9'+suffix), text)
text = (RUN/'build-clean-site-v6.py').read_text(encoding='utf8')
text = text.replace('-site-v6', '-site-v9').replace('site-build-v6', 'site-build-v9').replace('site-check-v6', 'site-check-v9')
text = text.replace('registry-check-v6', 'registry-check-v9').replace('verify-registry-v6', 'verify-registry-v9').replace('current-reader-capture-v6', 'current-reader-capture-v9').replace('capture-reader-v6', 'capture-reader-v9')
text = text.replace('only two newest reader presentation labels repaired after the gate, exact equations/semantics unchanged.',
    'reader-only corrections after rejected FINAL: comparator/expectation wording and meanPredict t>0, with all Lean/source hashes unchanged; page/status label repairs retained.')
write(RUN/'build-clean-site-v9.py', text)
fixed_integrated()
print('Actual rejected FINAL reader-only repair recorded; no mathematical target changed.')
