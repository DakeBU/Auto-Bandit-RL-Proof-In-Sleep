from common_accepted_v1 import *
from commit_owned_v2 import stage_owned, commit_owned
import re

accepted_fixed()
review = load(RUN / 'delivery-receipt-v1.json')
assert review['verdict'] in ['accepted', 'accepted-with-explicit-delta'] and review['inputs_unchanged']
assert not review['required_blocking_repairs']
assert review['report_sha256'] == sha(RUN / 'delivery-review-v1.md')
rows = load(RUN / 'delivery-review-inputs-v1.json')['rows']
assert review['fixed_input_count'] == len(rows)
assert all(sha(r['path']) == r['sha256'] for r in rows)
changed = subprocess.check_output(['git', 'diff', 'HEAD', '--name-only', '-z']).decode('utf8').split('\0')
untracked = subprocess.check_output(['git', 'ls-files', '--others', '--exclude-standard', '-z']).decode('utf8').split('\0')
assert all(p.startswith(RUN.relative_to(ROOT).as_posix() + '/') for p in changed + untracked if p)
stage_owned()
cmd = ['git', '-c', 'core.whitespace=blank-at-eol,blank-at-eof,space-before-tab,cr-at-eol',
       'diff', '--cached', '--check', 'HEAD']
gate('delivery-evidence-full-diff-v1', *cmd, required=False)
code = load(RUN / 'delivery-evidence-full-diff-v1-exit.json')['actual_exit']
assert code in [0, 2]
bad = set(re.findall(r'^([^\r\n]+?):\d+: (?:trailing whitespace|new blank line at EOF|space before tab)',
                    (RUN / 'delivery-evidence-full-diff-v1.log').read_text(encoding='utf8'), re.M))
bound = {r['sha256'] for r in rows}
exceptions = []
for rel in sorted(bad):
    p = ROOT / rel
    assert rel.startswith(RUN.relative_to(ROOT).as_posix() + '/'), rel
    assert p.suffix == '.log' and sha(p) in bound and list(RUN.glob(p.stem + '*exit.json')), rel
    exceptions.append(dict(path=rel, sha256=sha(p), reason='Exact delivery-reviewed actual RAW command output only'))
if code:
    assert bad
    exceptions.append(dict(path=(RUN / 'delivery-evidence-full-diff-v1.log').relative_to(ROOT).as_posix(),
                           sha256=sha(RUN / 'delivery-evidence-full-diff-v1.log'), reason='Actual RAW whitespace diagnostic'))
write(RUN / 'delivery-evidence-raw-exceptions-v1.json', dict(exceptions=exceptions,
      full_unexcluded_actual_exit=code, full_unexcluded_passed=code == 0, source_and_executable_exceptions=0))
stage_owned()
gate('delivery-evidence-scoped-diff-v1', *cmd, '--', '.', *[':(exclude)' + r['path'] for r in exceptions])
assert all(sha(r['path']) == r['sha256'] for r in rows)
delivery = load(RUN/'actual-draft-delivery-v1.json')
pr = delivery['PR']
assert delivery['exact_base'] == BASE and delivery['basePR'] == 199
commit_owned('Record reviewed causal-kernel draft creation, official attachment and delivery evidence')
head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], encoding='utf8').strip()
tmp = ROOT / 'tmp'
tmp.mkdir(exist_ok=True)

def remote(label, args):
    out = tmp / (label + '.log')
    receipt = tmp / (label + '-exit.json')
    assert not out.exists() and not receipt.exists()
    start = time.monotonic()
    with out.open('wb') as stream:
        result = subprocess.run(args, stdout=stream, stderr=subprocess.STDOUT)
    write(receipt, dict(command=args, cwd=ROOT.as_posix(), actual_exit=result.returncode,
          seconds=time.monotonic() - start, log_sha256=sha(out)))
    assert result.returncode == 0, label
    return out

remote('online-kernel-causal-final-push-v1', ['git', '-c', 'credential.helper=',
       '-c', 'credential.helper=!gh auth git-credential', 'push', 'origin', BRANCH])
for attempt in range(3):
    p = remote('online-kernel-causal-final-PR'+str(pr)+'-v'+str(attempt+1), ['gh','pr','view',str(pr),'--json',
        'number,url,title,body,state,isDraft,headRefOid,baseRefName,headRefName,mergedAt,statusCheckRollup'])
    r = load(p)
    if r['headRefOid'] == head: break
    assert r['headRefName'] == BRANCH
    time.sleep(2)
assert r['headRefOid'] == head and r['headRefName'] == BRANCH
assert r['baseRefName'] == 'codex/research-online-completed-causal'
assert r['state'] == 'OPEN' and r['isDraft'] and r['mergedAt'] is None
assert r['title'] == (RUN / 'prospective-PR-title-v1.txt').read_text(encoding='utf8').strip()
assert r['body'].replace('\r\n', '\n').rstrip('\n') == (RUN / 'prospective-PR-body-v1.md').read_text(encoding='utf8').replace('\r\n', '\n').rstrip('\n')
assert not subprocess.check_output(['git', 'status', '--porcelain', '--untracked-files=all'], encoding='utf8').strip()
write(tmp / 'online-kernel-causal-final-ready-v1.json', dict(
    actual_final_head=head, branch=BRANCH, PR=pr, url=r['url'], exact_stacked_base=BASE, basePR=199,
    state='OPEN', draft=True, merged=False, live=False, worktree_clean=True,
    official_attachment_committed=True, remote_checks_capture=r['statusCheckRollup'],
    remote_all_required_passed=False,
    note='Actual final remote snapshot; unfinished checks are not certified. Five current proof bodies/local gates unchanged.',
    worktree_retained_for_next_required_source_obligation=ROOT.as_posix(), chapter_complete=False, goal_complete=False))
print('Actual final OPENdraft head', head, 'clean worktree; whole Goal active.', flush=True)
