from publication_guard_v1 import *
fixed()
assert load(RUN / 'full-harness-inspected-v1.json')['actual_check_passed']
own = [ROOT / d / (TASK + '.md') for d in ['tasks', 'proof-obligations', 'research-wiki/retrieval-index']]
write(RUN / 'pre-combined-own-metadata-v1.json', dict(rows=[dict(path=p.as_posix(), sha256=sha(p),
    raw_base64=base64.b64encode(p.read_bytes()).decode('ascii')) for p in [CONTRIBUTION, *own]]))
full = load(RUN / 'full-harness-inspected-v1.json')
combined = load(RUN / 'combined-root-Tests-inspected-v1.json')
summary = ('Eight frozen production proofs/two exact partial definitions and four full public canaries compiled and BODY accepted. '
    'Actual combined root/Tests/full harness inspected at SHA-bound source; counts in full-harness-inspected-v1.json and combined-root-Tests-inspected-v1.json. '
    'Twelve complete public proof VALUEs,26standard-only axiom outputs including2definitions,12frozen headers; selected14nodes/2027directpresences/12canaryVALUEpairs,6productionpairs; two selected numeric tails Eq.mp retain actual iterate_one_step. '
    'All failed proofs and API/audit/discovery repairs retained without frozen-terminal weakening. '
    'Exact five-path reader plan-v2 materialized with every old field/link/ID preserved; source/BODY/canary/neutral context reviews distinct and staged. '
    'Locality and actual current-loss partial recursion lower a required Chapter2 prescient dependency. Source X/interior transport into a valid generated run, source interior conditions and sharp same-run fixed/variable telescopes including main-text fixed-step exercise REQUIRED/OPEN. '
    'All8Chapter2forwards OPEN; chapter partial/proofdenominatornull, whole16GoalACTIVE. Complete registry/site/DOM/pixels/FINAL/native/delivery pending. No merge/deploy/main/live/CI claim.')
for p in own:
    p.write_bytes(p.read_bytes() + ('\nCombined candidate: ' + summary + '\n').encode('utf8'))
c = load(CONTRIBUTION)
c['verification']['bandit_check'] = 'Actual root/Tests/full tools/bandit.py check passed, source/receipt hashes and observed counts in RUN combined-root-Tests-inspected-v1.json/full-harness-inspected-v1.json. Compiler/unittest/exporter/check markers inspected. No rule/source/toolchain weakening.'
CONTRIBUTION.write_bytes((json.dumps(c, ensure_ascii=False, indent=2) + '\n').encode('utf8'))
write(RUN / 'memory-digest-v2.md', '# ' + TASK + '\n\n' + summary + '\n')
write(RUN / 'proof-obligations-candidate-v1.json', dict(
    stage='integrated-candidate', production=[dict(declaration=t['declaration'], statement_hash=t['statement_hash'],
        status='focused-and-combined-compiled; public-VALUE/standard-axioms/fence-backed; BODY-accepted; FINAL-pending')
        for t in load(CONTRACT / 'stabilized-v1.json')['targets']],
    definitions=load(CONTRACT / 'stabilized-v1.json')['definitions'],
    canaries=[dict(declaration=t['declaration'], statement_hash=t['statement_hash'],
        status='full-conjunction-public-VALUE; standard-axioms; frozen; BODY-accepted; FINAL-pending')
        for t in load(CONTRACT / 'canary-stabilized-v1.json')['targets']],
    observed_combined=combined, observed_full_harness=full,
    remaining_required=['Source X/interior regularity transport into valid generated run and interior conditions',
        'Sharp same-run fixed-step cumulative bound including main-text exercise',
        'Sharp same-run variable-step cumulative bound', 'All eight Chapter2 forward source containers'],
    source_container_closed=False, chapter_proof_total=None, chapter_complete=False, whole_Goal_status='ACTIVE'))
capture('frontier-refresh-help-v1', sys.executable, '-B', '-X', 'utf8', 'tools/bandit.py', 'frontier-refresh', '--help')
capture('current-frontier-refresh-v1', sys.executable, '-B', '-X', 'utf8', RUN / 'native-scoped.py',
    'frontier-refresh', '--root-objective', 'Persistent Orabona Chapters1-16; bounded causal partial Bregman foundation only',
    '--leaf', TASK, '--kind', 'review', '--statement',
    'Eight frozen proofs/two partial definitions/four full canaries compiled and BODY accepted. Combined root Tests fullharness passed; fullsource Chapter2 incomplete. Registry/site/pixels FINAL native delivery pending.',
    '--file', RUN / 'canary-BODY-publication-review-v1.md', '--source-status', 'source-reviewed',
    '--leaf-status', 'gate-pending', '--dependency', 'review:production-BODY:accepted',
    '--dependency', 'review:canary-BODY:accepted', '--dependency', 'lean:BanditRL.OnlinePrescientBregman.iterate_one_step:compiled',
    '--trials', RUN / 'trials.jsonl', '--output', RUN / 'current-frontier-v1.json', '--shadow-status', 'pending')
_, out = capture('current-frontier-shadow-v1', sys.executable, '-B', '-X', 'utf8', RUN / 'native-scoped.py',
    'frontier-shadow', '--trials', RUN / 'trials.jsonl', '--memory-digest', RUN / 'memory-digest-v2.md',
    '--frontier', RUN / 'current-frontier-v1.json')
s = json.loads(out)
assert s['mismatches'] == [] and not s['would_mutate']
write(RUN / 'shadow-inspected-v1.json', dict(actual_report=s, global_SGB_unchanged=True,
    scope='Own8proofs/2partialdefs/4fullcanaries and retained failure history; not source/chapter denominator.',
    chapter_proof_total=None, chapter_complete=False, whole_Goal_status='ACTIVE'))
fixed()
print('Actual OWN frontier shadow mismatches[]/would_mutatefalse; globalSGB unchanged.')
