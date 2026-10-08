from common_accepted_v1 import *

def current_owned_paths():
    singletons = {'MANIFEST.md', 'runs/trials.jsonl', 'runs/lifecycle_sessions.jsonl', 'runs/lifecycle_memory.jsonl',
        MANIFEST.as_posix(), PUBLIC.as_posix(), CANARY.as_posix(), 'BanditRLProof.lean', 'Tests.lean',
        'website/content/readings.json', 'website/content/highlights.json', 'website/content/chapters.json'}
    singletons.update(folder + '/' + TASK + '.md' for folder in
        ['tasks', 'conversion-windows', 'proof-obligations', 'proof-blueprints', 'research-wiki/retrieval-index'])
    paths = [s[3:] for s in subprocess.check_output(['git', 'status', '--porcelain', '--untracked-files=all'], encoding='utf8').splitlines()]
    for p in paths:
        assert p in singletons or p.startswith(RUN.relative_to(ROOT).as_posix() + '/') or p.startswith(CONTRACT.as_posix() + '/'), p
    return paths

def commit_owned(message):
    paths = current_owned_paths()
    globals_ = {'MANIFEST.md', 'runs/trials.jsonl', 'runs/lifecycle_sessions.jsonl', 'runs/lifecycle_memory.jsonl'}
    raw_paths = [p for p in paths if p not in globals_]
    for start in range(0, len(raw_paths), 48):
        r = subprocess.run(['git', '-c', 'core.autocrlf=false', 'add', '--', *raw_paths[start:start+48]], stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        assert r.returncode == 0, r.stdout.decode('utf8', errors='replace')
    changed_globals = [p for p in paths if p in globals_]
    if changed_globals:
        r = subprocess.run(['git', 'add', '--', *changed_globals], stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        assert r.returncode == 0
    for p in raw_paths:
        assert subprocess.check_output(['git', 'show', ':' + p]) == Path(p).read_bytes(), p
    for p in changed_globals:
        assert subprocess.check_output(['git', 'show', ':' + p]).startswith(subprocess.check_output(['git', 'show', BASE + ':' + p])), p
    r = subprocess.run(['git', 'commit', '-m', message], stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    sys.stdout.write('\n'.join(r.stdout.decode('utf8', errors='replace').splitlines()[:4]) + '\n')
    assert r.returncode == 0
    assert not current_owned_paths(), 'New uncommitted files must be preserved and explicitly committed.'

if __name__ == '__main__':
    accepted_fixed()
    assert load(RUN / 'native-acceptance-overlay-v1.json')['status'] == 'passed'
    final = load(RUN / 'final-reader-receipt-v1.json')
    assert not final['required_repairs'] and not final['required_blocking_reader_repairs']
    assert subprocess.check_output(['git', 'branch', '--show-current'], encoding='utf8').strip() == BRANCH
    prior = json.loads(subprocess.check_output(['gh', 'api', 'repos/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/pulls/192']))
    assert prior['head']['sha'] == BASE and prior['state'] == 'open' and prior['draft'] and not prior['merged']
    assert not json.loads(subprocess.check_output(['gh', 'pr', 'list', '--state', 'all', '--head', BRANCH, '--json', 'number,url,state']))
    gate('source-scope-pre-publication-v1', sys.executable, '-B', '-X', 'utf8', RUN / 'audit-scope-v2.py', 'pre-publication-v1')
    gate('scoped-diff-pre-publication-v2', sys.executable, '-B', '-X', 'utf8', RUN / 'check-scoped-diff-v2.py', 'pre-publication-v2')
    payload = dict(title=(RUN / 'prospective-pr-title-v1.txt').read_text(encoding='utf8').strip(),
        body_file=(RUN / 'prospective-pr-body-v1.md').as_posix(), body_sha256=sha(RUN / 'prospective-pr-body-v1.md'),
        draft=True, base=BASE_BRANCH, head=BRANCH, exact_base_head=BASE, source_package_only=True,
        native_acceptance_completed=True, chapter_complete=False, goal_complete=False,
        final_receipt_sha256=sha(RUN / 'final-reader-receipt-v1.json'))
    write(RUN / 'PR-payload-v1.json', payload)
    commit_owned('Accept reviewed square-minimum package and preserve local reader evidence')
    gate('contributor-pre-publication-v2', sys.executable, '-B', '-X', 'utf8', 'tools/check_contributor_contract.py', '--base', BASE)
    text = (RUN / 'contributor-pre-publication-v2.log').read_text(encoding='utf8')
    assert 'affected production paths: 5' in text and 'changed contribution contracts: 1' in text, text
    commit_owned('Record the final nonvacuous square-minimum contributor gate')
    accepted_fixed()
    head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], encoding='utf8').strip()
    gate('branch-push-v1', 'git', '-c', 'credential.helper=', '-c', 'credential.helper=!gh auth git-credential', 'push', '--set-upstream', 'origin', BRANCH)
    assert subprocess.check_output(['git', 'ls-remote', 'origin', 'refs/heads/' + BRANCH], encoding='utf8').split()[0] == head
    assert sha(payload['body_file']) == payload['body_sha256']
    gate('draft-PR-create-v1', 'gh', 'pr', 'create', '--draft', '--base', payload['base'], '--head', payload['head'],
        '--title', payload['title'], '--body-file', payload['body_file'])
    prs = json.loads(subprocess.check_output(['gh', 'pr', 'list', '--state', 'open', '--head', BRANCH, '--json', 'number,url,isDraft']))
    assert len(prs) == 1 and prs[0]['isDraft'], prs
    pr = json.loads(subprocess.check_output(['gh', 'api', 'repos/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/pulls/' + str(prs[0]['number'])]))
    assert pr['head']['sha'] == head and pr['base']['ref'] == BASE_BRANCH and pr['state'] == 'open' and pr['draft'] and not pr['merged']
    assert pr['body'].replace('\r\n', '\n').strip() == Path(payload['body_file']).read_text(encoding='utf8').strip()
    write(RUN / 'created-PR-v1.json', pr)
    print(json.dumps(dict(PR=pr['html_url'], number=pr['number'], head=head, state='OPEN-DRAFT-unmerged', attachment_required=True, goal_complete=False)), flush=True)
