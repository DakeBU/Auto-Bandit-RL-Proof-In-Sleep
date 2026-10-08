from common_integrated_v1 import *

fixed_integrated()
expected = ['BanditRLProof/OnlineLearningFoundations.lean', 'BanditRLProof/OnlineLearningHistory.lean',
    'BanditRLProof/OnlineLearningIID.lean', 'BanditRLProof/OnlineLearningInformation.lean',
    'BanditRLProof/OnlineLearningStochastic.lean']
command = [sys.executable, '-B', '-X', 'utf8', 'tools/check_contributor_contract.py', '--base', 'origin/main']
start = time.monotonic()
child = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
write(RUN / 'inherited-main-relative-contributor-v1.log', child.stdout)
text = child.stdout.decode('utf8', errors='replace')
assert child.returncode != 0, 'Do not silently erase inherited mandatory source/integration audits.'
assert all(p in text for p in expected), text
write(RUN / 'inherited-main-relative-contributor-v1.json', dict(command=command, cwd=ROOT.as_posix(),
    actual_exit_code=child.returncode, seconds=time.monotonic()-start,
    log_sha256=sha(RUN / 'inherited-main-relative-contributor-v1.log'), expected_unwaived_modules=expected,
    status='Actual main-relative rejection retained; five inherited mandatory audits remain REQUIRED, not accepted by this package.',
    does_not_replace_exact_stacked_base_gate=True, no_merge_or_main_claim=True, chapter_complete=False, goal_complete=False))
print('Actual main-relative contributor exit', child.returncode, '; all five inherited module audits remain unwaived.')
