from common import *

assert Path.cwd() == ROOT and sha(PDF) == PDF_SHA
assert subprocess.check_output(['git', 'branch', '--show-current'], encoding='utf8').strip() == BRANCH
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], encoding='utf8').strip() == BASE
assert subprocess.check_output(['git', 'diff', '--name-only', 'HEAD'], encoding='utf8') == ''
untracked = subprocess.check_output(['git', 'ls-files', '--others', '--exclude-standard'], encoding='utf8').splitlines()
assert all(x.startswith(RUN.relative_to(ROOT).as_posix()+'/') for x in untracked)
capture('start-worktrees-v1', 'git', 'worktree', 'list', '--porcelain')
capture('start-git-common-v1', 'git', 'rev-parse', '--git-common-dir')
for command in ['new-task', 'search-memory', 'list-lean-decls', 'retrieval-record',
        'lifecycle-event', 'trial-log', 'statement-fence', 'safe-verify']:
    capture(command+'-help-v1', sys.executable, '-B', '-X', 'utf8', RUN/'native-scoped.py', command, '--help')
relevant = [ROOT/x for x in ['AGENTS.md', 'CONTRIBUTING.md', 'docs/contributor-codex-contract.md',
    'docs/theorem-publication-protocol.md', 'docs/hierarchical_harness.md',
    'docs/lifecycle_and_proof_frontier_hardening.md', 'lean-toolchain', 'lakefile.lean', 'lake-manifest.json',
    'tools/bandit.py', 'tools/abrl_lifecycle.py', 'BanditRLProof.lean', 'Tests.lean',
    'BanditRLProof/OnlineGradientDescentVariable.lean', 'BanditRLProof/OnlineSubgradientPolicy.lean',
    'BanditRLProof/OnlineSubgradientDescent.lean', 'BanditRLProof/OnlineAdaptiveEnergy.lean',
    '.lake/packages/mathlib/Mathlib/Algebra/BigOperators/Module.lean',
    'docs/contracts/online-book-v1/coverage.json', 'research-wiki/mathlib/theorem-cards.md']]
relevant += [Path('E:/ABRL/AGENTS.md'), Path('E:/ABRL/README.md'),
    Path('E:/ABRL/maintenance/STATUS-20260910-CLOSURE.md'),
    Path('E:/ABRL/maintenance/DIRECTION-REVIEW-20260913.md'), Path('E:/ABRL/papers/long/main/harness.tex'), PDF]
write(RUN/'baseline-v1.json', dict(base=BASE, branch=BRANCH,
    git_tree=subprocess.check_output(['git', 'rev-parse', 'HEAD^{tree}'], encoding='utf8').strip(),
    initial_tracked_diff_empty=True, initial_untracked_scope='Only new OWN bootstrap files', rows=rows(relevant),
    protocol='Relevant RAW + exact Git tree and clean tracked status. Not a fresh 35,392-file RAW scan.',
    stacked_PR=217, main_or_live_updated=False, chapter_complete=False, whole_Goal='active'))
for label, source in [('readonly-API-v1', ROOT/'tmp/online-adaptive-OSD-readonly-API-v1/actual.json'),
        ('parent-delivery-review-v1', ROOT/'tmp/online-ch2-adaptive-energy-delivery-v1/actual-delivery-review-v1.json')]:
    write(RUN/(label+'.json'), dict(original_path=source.as_posix(), sha256=sha(source),
        RAW_base64=base64.b64encode(source.read_bytes()).decode('ascii'),
        boundary='Exact earlier local original; not relabeled as fresh compilation or committed parent delivery evidence.'))
print('Actual audit complete; contract and first dependency are still draft.', flush=True)
