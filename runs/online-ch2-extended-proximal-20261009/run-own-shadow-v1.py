from publication_guard_v1 import *
fixed()
assert load(RUN / 'full-harness-inspected-v1.json')['actual_check_passed']
write(RUN / 'memory-digest-v2.md', '# ' + TASK + '\n\n'
    'Three exact extended-loss bridge proofs and two complete infinity canaries compiled; five full public VALUEs/ten standard-only axiom outputs/frozen guards. '
    'Both truly selected numeric branches retain the public extended one-step helper via Eq.mp. Selected six-node graph includes one compiler-generated Test auxiliary; not a source denominator. '
    'Distinct staged source/CONTRACT/BODY/canary/reader-v3/exact five paths accepted; two rejected reader versions and proof/selector failures retained. '
    'Actual combined root/Tests/full harness markers inspected. Feasible finite-part and actual EReal minimum bridges lower the required prescient frontier. '
    'Source X/interior/ambient extension locality, attained current-loss causal recursion/interiority and sharp fixed/variable same-run telescopes remain REQUIRED/OPEN; all eight Chapter2 forwards open, chapter proof total null, whole16Goal ACTIVE. '
    'Complete shared registry/site/DOM/pixels/FINAL/native/delivery pending.\n')
capture('frontier-refresh-help-v1', sys.executable, '-B', '-X', 'utf8', 'tools/bandit.py', 'frontier-refresh', '--help')
capture('current-frontier-refresh-v1', sys.executable, '-B', '-X', 'utf8', RUN / 'native-scoped.py',
    'frontier-refresh', '--root-objective', 'Persistent Orabona Chapters1-16; bounded extended-loss proximal bridge only',
    '--leaf', TASK, '--kind', 'review', '--statement',
    'Three exact extended-loss bridge proofs/two infinity canaries compiled and source/BODY/reader accepted. Combined root Tests fullharness passed; full source and Chapter2 incomplete, site registry pixels FINAL native delivery pending.',
    '--file', RUN / 'canary-BODY-publication-review-v3.md', '--source-status', 'source-reviewed',
    '--leaf-status', 'gate-pending', '--dependency', 'review:production-BODY:accepted',
    '--dependency', 'review:canary-BODY:accepted', '--dependency', 'lean:BanditRL.OnlineBregman.proximal_one_step_extended:compiled',
    '--trials', RUN / 'trials.jsonl', '--output', RUN / 'current-frontier-v1.json', '--shadow-status', 'pending')
_, out = capture('current-frontier-shadow-v1', sys.executable, '-B', '-X', 'utf8', RUN / 'native-scoped.py',
    'frontier-shadow', '--trials', RUN / 'trials.jsonl', '--memory-digest', RUN / 'memory-digest-v2.md',
    '--frontier', RUN / 'current-frontier-v1.json')
s = json.loads(out)
assert s['mismatches'] == [] and not s['would_mutate']
write(RUN / 'shadow-inspected-v1.json', dict(actual_report=s, global_SGB_unchanged=True,
    scope='Own three compiled bridge proofs, two full canaries and diagnostic failure history, not a source/chapter denominator.',
    chapter_proof_total=None, chapter_complete=False, whole_Goal_status='ACTIVE'))
fixed()
print('Actual OWN frontier shadow mismatches[]/would_mutatefalse; globalSGB unchanged.')
