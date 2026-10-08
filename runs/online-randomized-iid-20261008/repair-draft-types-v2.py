from common_v1 import *

fixed()
write(RUN / 'draft-type-repair-v2.json', dict(stage='draft', prior_version=1, active_version=2,
    actual_failure_receipt='draft-types-and-API-v1-exit.json',
    issues=['Greek capital Sigma is reserved Lean syntax, cannot be a type binder',
        'map_measurableEquiv_injective belongs to MeasurableEquiv namespace'],
    repair='Rename only seed-space binder to Seed; correct actual API namespace. All original draft files retained; no stabilized contract or theorem body existed.',
    mathematical_assumptions_changed=False, conclusion_changed=False))
for old in sorted(CONTRACT.glob('*-v1.*')):
    text = old.read_text(encoding='utf8').replace('Σ', 'Seed')
    new = old.with_name(old.name.replace('-v1.', '-v2.'))
    if old.suffix == '.json':
        value = json.loads(text)
        if isinstance(value, dict) and 'version' in value:
            value['version'] = 2
        if old.name == 'targets-v1.json':
            for row in value['rows']:
                row['header_sha256'] = hashlib.sha256(row['header'].encode()).hexdigest()
        if old.name == 'initial-DAG-v1.json':
            for row in value['nodes']:
                row['header_sha256'] = hashlib.sha256(row['header'].encode()).hexdigest()
        write(new, value)
    else:
        write(new, text.replace('Draft v1:', 'Draft v2:'))
targets = load(CONTRACT / 'targets-v2.json')
fingerprint = load(CONTRACT / 'source-fingerprint-v2.json')
fingerprint['target_hashes'] = {r['id']:r['header_sha256'] for r in targets['rows']}
fingerprint['context_sha256'] = sha(CONTRACT / 'public-context-v2.lean')
fingerprint['definition_sha256'] = hashlib.sha256((CONTRACT / 'public-context-v2.lean').read_text(encoding='utf8')
    .split('namespace BanditRL.OnlineLearning\n',1)[1].split('end BanditRL.OnlineLearning',1)[0].strip().encode()).hexdigest()
write(RUN / 'active-source-statement-fingerprint-v2.json', fingerprint)
write(RUN / 'neutral-packet-v2.md', (RUN / 'neutral-packet-v1.md').read_text(encoding='utf8')
    .replace('Σ', 'Seed').replace('neutral-context-v1.lean', 'neutral-context-v2.lean'))
write(RUN / 'neutral-inputs-v2.json', dict(rows=[dict(path=p.resolve().as_posix(),sha256=sha(p)) for p in
    [RUN / 'neutral-packet-v2.md', CONTRACT / 'neutral-context-v2.lean']], terminal_count=7, complete_definitions=3))
write(RUN / 'draft-types-and-API-v2.lean', (RUN / 'draft-types-and-API-v1.lean').read_text(encoding='utf8')
    .replace('Σ', 'Seed').replace('MeasureTheory.Measure.map_measurableEquiv_injective', 'MeasurableEquiv.map_measurableEquiv_injective'))
gate('draft-types-and-API-v2', 'lake', 'env', 'lean', RUN / 'draft-types-and-API-v2.lean')
gate('neutral-types-v2', 'lake', 'env', 'lean', CONTRACT / 'neutral-context-v2.lean')
native('draft-repair-event-v2', 'lifecycle-event', '--session', TASK, '--event', 'draft-type-repair',
    '--payload-json', json.dumps(dict(contract_version=2, hypotheses_changed=False,
        old_failure_retained=True, compiled_definitions_not_proofs=True)))
fixed()
print('Actual draft/neutral compilation passed; seven propositions/three neutral definitions, bodies unproved.')
