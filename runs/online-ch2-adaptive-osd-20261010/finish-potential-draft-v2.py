from common import *
sys.path.insert(0, str(ROOT))
from tools import abrl_lifecycle as lifecycle

assert not PUBLIC.exists()
documents = [ROOT/x/(TASK+'.md') for x in ['tasks','conversion-windows','proof-obligations']]
observed = []
for path in documents:
    raw = path.read_bytes()
    assert b'\r\n' not in raw and raw.count(b'## Current exact draft contract') == 1
    observed.append(dict(path=path.as_posix(), sha256=sha(path),
        RAW_base64=base64.b64encode(raw).decode('ascii')))
write(RUN/'draft-bootstrap-failure-v1.json', dict(command='python -B -X utf8 '+str(RUN/'prepare-potential-draft-v1.py'),
    actual_exit=1, diagnostic='FileNotFoundError: research-wiki/retrieval-index/'+TASK+'.md',
    stage='After all draft headers/intent/source/DAG/neutral files and first three native scaffold docs; before draft event.',
    cause='new-task creates three scaffold docs, not the fourth retrieval-index doc.',
    production_or_algorithm_created=False, initial_three_scaffold_RAW_durably_preserved=False,
    observed_current_after_failure=observed,
    boundary='First three scaffold initial RAW were read but not durably written before process exit. These are actual observed post-edit bytes, not reconstructed original bytes. No frozen contract or user file was changed.',
    recovery='Do not replay new-task or append the three suffixes again. Create the missing NEW retrieval index explicitly and continue once.'))
write(ROOT/'research-wiki/retrieval-index'/(TASK+'.md'), '# Adaptive OSD retrieval index\n\n'
    'Task: `'+TASK+'`\n\nActual weighted-memory-v1/weighted-declarations-v1, subgradient-policy-declarations-v1, '
    'energy-declarations-v1 and mathlib-card-retrieval-v1 are in runs/online-ch2-adaptive-osd-20261010/. '
    'The pinned existing weighted potential requires strict-positive eta and does not cover leading zero energy. '
    'Selected adapter route: Mathlib Finset.sum_range_by_parts and range telescoping; mathlib-candidate. '
    'Prior actual typed API original is retained through readonly-API-v1.json base64, not relabeled as fresh proof. '
    'Only the one potential header is draft; parent causal adaptive OSD and all chapter targets remain required/open.\n')
write(RUN/'.gitattributes', '* -text\nown-artifact-journal.md whitespace=cr-at-eol\nlifecycle-state.json whitespace=cr-at-eol\nlifecycle-sessions.jsonl whitespace=cr-at-eol\n')
write(CONTRACT/'.gitattributes', '* -text\n')
output = ROOT/'tmp/online-adaptive-OSD-retrieval-native-v1.jsonl'
assert not output.exists()
capture('potential-retrieval-record-v1', sys.executable, '-B', '-X', 'utf8', RUN/'native-scoped.py',
    'retrieval-record', '--task', TASK, '--query', 'Nonnegative nondecreasing weighted potential including zero weights',
    '--candidate', 'Mathlib.Finset.sum_range_by_parts',
    '--candidate', 'BanditRL.OnlineGradientDescent.weighted_potential_sum',
    '--rejection', 'BanditRL.OnlineGradientDescent.weighted_potential_sum=Requires every eta strictly positive; no leading zero-energy interface',
    '--compiled-scratch', 'tmp/online-adaptive-OSD-readonly-API-v1/Probe.lean',
    '--provenance', 'Actual pinned project declaration/memory/card retrieval and prior actual typed API receipt; source-blind reconstruction pending',
    '--output', output)
write(RUN/'potential-retrieval-native-RAW-v1.json', dict(path=output.as_posix(), sha256=sha(output),
    RAW_base64=base64.b64encode(output.read_bytes()).decode('ascii')))
write(RUN/'potential-retrieval-parsed-v1.json', [json.loads(x) for x in output.read_text(encoding='utf8').splitlines()])
header = (CONTRACT/'potential-header-draft-v1.lean.txt').read_text(encoding='utf8')
binders, conclusion = header.split('theorem weighted_potential_sum ', 1)[1].rsplit(' :\n', 1)
conclusion = conclusion.rsplit(' := by', 1)[0]
probe = ('import Mathlib.Algebra.BigOperators.Module\nimport Mathlib.Tactic\nopen Finset\n\n'
    '#check (∀ '+binders+',\n'+conclusion+')\n\n'
    '#check Finset.sum_range_by_parts\n#check Finset.sum_range_sub\n#check Finset.sum_range_sub\'\n')
write(RUN/'PotentialTypeAPIProbeV1.lean', probe)
capture('potential-type-API-probe-v1', 'lake', 'env', 'lean', RUN/'PotentialTypeAPIProbeV1.lean')
statement = load(CONTRACT/'potential-fingerprint-draft-v1.json')
event('potential-draft-event-v1', 'draft', dict(current_leaf='weighted_potential_sum',
    source_sha256=PDF_SHA, statement_hash=statement['statement_hash'],
    parent_algorithm_status='required-draft', source_proof_display_delta='half-factor requires independent review',
    whole_Goal='active', chapter_complete=False))
write(RUN/'draft-obligations-v1.md', '# Current required obligations\n\n'
    'Potential contract/neutral/source correction review pending; no theorem BODY. '
    'Once stabilized: actual potential proof, full public canary and axioms/BODY review. '
    'Then freeze actual causal-history/energy/skip definitions and same-trajectory performance endpoints. '
    'The general-alpha/zeroD/zeroenergy/T0/source-min correction and combined Book gates remain required. '
    'No new source-proof denominator is known; all Chapter2 forward targets remain open; wholeGoalACTIVE.\n')
print('Draft continuation completed without replay; no mathematical BODY created.', flush=True)
