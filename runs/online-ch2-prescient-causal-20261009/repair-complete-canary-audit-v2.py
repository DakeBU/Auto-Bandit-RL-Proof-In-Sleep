from common import *
fixed()
assert load(RUN / 'complete-canary-public-VALUE-v1.json')['actual_exit'] == 0
assert load(RUN / 'complete-canary-public-lookup-v1.json')['actual_exit'] == 0
assert not (RUN / 'complete-candidate-inspected-v1.json').exists()
old = (RUN / 'audit-complete-canaries-v1.py').read_text(encoding='utf8')
start = old.index('probe = ')
end = old.index('for i, t in enumerate(d[\u0027targets\u0027][:2]):')
prefix = old[:start]
replacement = '''receipt = load(RUN / 'complete-canary-public-VALUE-v1.json')
out = base64.b64decode(receipt['stdout_base64']).decode('utf8')
axioms = re.findall(r'depends on axioms:\\s*\\[([^]]*)\\]', out)
assert len(axioms) == 8 and 'sorryAx' not in out
assert all(set(x.strip() for x in a.split(',') if x.strip()) <= {'propext', 'Classical.choice', 'Quot.sound'} for a in axioms)
capture('complete-canary-lookup-help-v2', sys.executable, '-B', '-X', 'utf8', 'tools/bandit.py', 'list-lean-decls', '--help')
_, out = capture('complete-canary-public-lookup-v2', sys.executable, '-B', '-X', 'utf8', 'tools/bandit.py', 'list-lean-decls', 'OnlinePrescientBregmanCanary', '--include-tests', '--statement')
for t in d['targets']:
    assert t['declaration'] in out
    assert statement_hash(lean_declaration_header(TEST, t['declaration'])) == t['statement_hash']
'''
write(RUN / 'complete-canary-audit-v2.py', prefix + replacement + old[end:])
write(RUN / 'complete-canary-audit-repair-v2.json', dict(
    actual_failed_audit_helper='audit-complete-canaries-v1.py', actual_helper_exit=1,
    failure_after='Public full4VALUE/8standard-onlyaxioms command actually passed; declaration lookup command returned0 but excluded Test declarations by default, then inspection assertion failed.',
    diagnosis='Actual CLI uses scan_lean_declarations(include_tests=args.include_tests); --include-tests is required. Zero command exit did not mean target lookup succeeded.',
    unchanged_Test_sha256=sha(ROOT / 'Tests/OnlinePrescientBregmanCanary.lean'),
    unchanged_production_sha256=sha(PUBLIC), code_or_statement_changes=False,
    preserved_passed_public_VALUE_receipt='complete-canary-public-VALUE-v1.json',
    remaining_audit_pending=True, chapter_complete=False, whole_Goal_status='ACTIVE'))
event('complete-canary-audit-repair-native-v2', 'repair', dict(category='evidence-tool-configuration', statement_changes=False,
    diagnosis='Default declaration lookup excludes Tests; add actual supported --include-tests, preserve prior successful exact public kernel receipt.',
    canary_BODY_PENDING=True, package_accepted=False, source_container_closed=False))
capture('complete-canary-audit-resume-v2', sys.executable, '-B', '-X', 'utf8', RUN / 'complete-canary-audit-v2.py')
fixed()
