import sys
from pathlib import Path
sys.path.insert(0, str(Path.cwd() / 'runs/online-completed-causal-20261008'))
from common_accepted_v5 import *

accepted_fixed()
review = load(RUN / 'delivery-receipt-v1.json')
assert review['inputs_unchanged'] and not review['required_blocking_repairs']
assert review['verdict'] in ['accepted', 'accepted-with-explicit-delta']
assert sha(RUN / 'delivery-review-v1.md') == review['report_sha256']
assert all(sha(r['path']) == r['sha256'] for r in load(RUN / 'delivery-review-inputs-v1.json')['rows'])
head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], encoding='utf8').strip()
assert head == '4db37e090143760d99b9aedd026a72fa0f1f09ac'
tmp = ROOT / 'tmp'
assert load(tmp / 'online-completed-causal-final-push-v1-exit.json')['actual_exit'] == 0
first = load(tmp / 'online-completed-causal-final-PR199-v1.log')
assert first['headRefOid'] == load(RUN / 'actual-draft-delivery-v1.json')['verified_delivery_head']

def read_remote(label, args):
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

branch = read_remote('online-completed-causal-final-branch-v2',
                     ['git', 'ls-remote', 'origin', 'refs/heads/' + BRANCH])
assert branch.read_text(encoding='utf8').split()[0] == head
p = read_remote('online-completed-causal-final-PR199-v2', ['gh', 'pr', 'view', '199', '--json',
                'number,url,title,body,state,isDraft,headRefOid,baseRefName,headRefName,mergedAt,statusCheckRollup'])
r = load(p)
assert r['headRefOid'] == head and r['headRefName'] == BRANCH
assert r['baseRefName'] == 'codex/research-online-ae-causal'
assert r['state'] == 'OPEN' and r['isDraft'] and r['mergedAt'] is None
assert r['title'] == (RUN / 'prospective-PR-title-v1.txt').read_text(encoding='utf8').strip()
assert r['body'].replace('\r\n', '\n').rstrip('\n') == (RUN / 'prospective-PR-body-v1.md').read_text(encoding='utf8').replace('\r\n', '\n').rstrip('\n')
assert not subprocess.check_output(['git', 'status', '--porcelain', '--untracked-files=all'], encoding='utf8').strip()
write(tmp / 'online-completed-causal-final-ready-v2.json', dict(
    actual_final_head=head, branch=BRANCH, PR=199, url=r['url'], exact_stacked_base=BASE, basePR=198,
    state='OPEN', draft=True, merged=False, live=False, worktree_clean=True, official_attachment_committed=True,
    remote_checks_capture=r['statusCheckRollup'], remote_all_required_passed=False,
    original_finish_helper_observed_exit=1, original_push_actual_exit=0, original_remote_capture_actual_exit=0,
    original_finish_failure='Immediate PR read still exposed creation head, so final head assertion correctly failed.',
    retained_original_remote_snapshot_sha256=sha(tmp / 'online-completed-causal-final-PR199-v1.log'),
    actual_readonly_resume=True, retry_push_performed=False,
    note='Read-only branch and PR captures now agree exactly with evidence HEAD; unfinished CI is not certified.',
    worktree_retained_for_next_required_kernel_bridge=ROOT.as_posix(), chapter_complete=False, goal_complete=False))
print('Actual branch and OPENdraft199 exact final head:', head, 'clean; Goal active.', flush=True)
