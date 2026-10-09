from pathlib import Path
import subprocess, json, hashlib, sys

ROOT = Path.cwd()
RUN = ROOT / 'runs/online-ch2-reconciliation-20261010'
CONTRACT = ROOT / 'docs/contracts/online-ch2-reconciliation-v1'
BASE = '2e06e21d2acb0bf41142b19266d66d89364e17a0'
BRANCH = 'codex/research-online-ch2-reconciliation'
TASK = 'ONLINE-CH2-RECONCILIATION-20261010'
assert ROOT.as_posix() == 'E:/ABRL/worktrees/research-online-book'
assert subprocess.check_output(['git', 'branch', '--show-current'], encoding='utf8').strip() == BRANCH
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], encoding='utf8').strip() == BASE
status = subprocess.check_output(['git', 'status', '--porcelain', '--untracked-files=all'], encoding='utf8').splitlines()
assert len(status) == 1 and status[0][3:] == 'runs/online-ch2-reconciliation-20261010/bootstrap-v1.py', status

old = ROOT / 'runs/online-ch2-unbounded-osd-20261010'
common = (old / 'common.py').read_text(encoding='utf8')
for a, b in [
    ('online-ch2-unbounded-osd-v1', 'online-ch2-reconciliation-v1'),
    ("BASE='2f039d55ad2f9a9f9b97027287709804689cf46d'", "BASE='" + BASE + "'"),
    ('codex/research-online-ch2-unbounded-osd', BRANCH),
    ('ONLINE-CH2-UNBOUNDED-OSD-20261010', TASK),
    ("PUBLIC=ROOT/'BanditRLProof/OnlineUnboundedOSD.lean'", "PUBLIC=ROOT/'BanditRLProof.lean'"),
]:
    assert a in common, a
    common = common.replace(a, b)
assert not (RUN / 'common.py').exists()
(RUN / 'common.py').write_bytes(common.encode('utf8'))
sys.path.insert(0, str(RUN))
from common import *

tracked = subprocess.check_output(['git', 'ls-files', '-z']).decode('utf8').split('\0')
tracked = [ROOT / p for p in tracked if p]
write(RUN / 'baseline-v1.json', dict(base=BASE, branch=BRANCH, rows=rows(tracked),
    boundary='All previously tracked RAW files frozen. Draft work creates only OWN files; no old production/Test/source/contracts/reader/coverage/global frontier mutation.'))
write(RUN / 'native-scoped.py', (old / 'native-scoped.py').read_bytes())
fixed()
for label, args in [
    ('fresh-parent-PR214-v1', ['gh', 'pr', 'view', '214', '--json', 'number,url,state,isDraft,headRefName,headRefOid,baseRefName,mergedAt']),
    ('canonical-status-v1', ['git', '-C', 'E:/ABRL/research', 'status', '--porcelain=v1', '-z']),
    ('canonical-head-v1', ['git', '-C', 'E:/ABRL/research', 'rev-parse', 'HEAD']),
    ('fresh-main-v1', ['git', 'rev-parse', 'origin/main']),
    ('common-git-store-v1', ['git', 'rev-parse', '--git-common-dir']),
    ('worktrees-v1', ['git', 'worktree', 'list', '--porcelain']),
    ('native-new-task-help-v1', [sys.executable, '-B', '-X', 'utf8', RUN / 'native-scoped.py', 'new-task', '--help']),
    ('native-event-help-v1', [sys.executable, '-B', '-X', 'utf8', RUN / 'native-scoped.py', 'lifecycle-event', '--help']),
    ('native-declaration-help-v1', [sys.executable, '-B', '-X', 'utf8', RUN / 'native-scoped.py', 'list-lean-decls', '--help']),
]:
    _, out = capture(label, *args)
    if label == 'fresh-parent-PR214-v1':
        pr = json.loads(out)
        assert pr['state'] == 'OPEN' and pr['isDraft'] and pr['mergedAt'] is None and pr['headRefOid'] == BASE

capture('native-new-task-v1', sys.executable, '-B', '-X', 'utf8', RUN / 'native-scoped.py', 'new-task', TASK,
    '--kind', 'chapter-audit', '--title', 'Reconcile exact Chapter2 source branches, current proof contracts and required whole-book dependencies')
write(RUN / 'task-templates-exact-v1.json', dict(rows=[dict(path=p.as_posix(), sha256=sha(p), raw_base64=base64.b64encode(p.read_bytes()).decode('ascii'))
    for p in [ROOT / 'tasks' / (TASK + '.md'), ROOT / 'conversion-windows' / (TASK + '.md'), ROOT / 'proof-obligations' / (TASK + '.md')]]))

prior = ROOT / 'docs/contracts/online-ch2-chapter-audit-v1'
source = load(prior / 'source-fingerprint-v1.json')
assert sha(PDF) == PDF_SHA
source_checks = []
for row in source['source_pages']:
    for kind in ['text', 'image']:
        p = Path(row[kind + '_path'])
        assert sha(p) == row[kind + '_sha256'], p
        source_checks.append(dict(path=p.as_posix(), sha256=sha(p), pdf_page=row['pdf_page'], kind=kind))
write(CONTRACT / 'source-fingerprint-v1.json', dict(pdf=PDF.as_posix(), pdf_sha256=PDF_SHA,
    source_version='arXiv:1912.13213v10, 2026-06-21',
    prior_source_inventory=dict(path=(prior / 'complete-source-reconciliation-draft-v3.json').as_posix(), sha256=sha(prior / 'complete-source-reconciliation-draft-v3.json')),
    prior_source_inventory_review=dict(path=(ROOT / 'runs/online-ch2-chapter-audit-20261009/source-contract-repair-review-v1.json').as_posix(), sha256=sha(ROOT / 'runs/online-ch2-chapter-audit-20261009/source-contract-repair-review-v1.json')),
    current_source_page_checks=source_checks,
    pixel_boundary='Exact previously read/reviewed original page assets checked; no new personal pixel-view claim in bootstrap.'))

scope = ('Reconcile the frozen65 overlapping Chapter2 source containers with exact current source-qualified statements, complete module bytes, applicable distinct semantic/BODY/FINAL/delivery evidence and the shared declaration registry. '
    'Add explicit current bindings for separately delivered nonsmooth examples, prescient source and Theorem5.4 packages; no source claim is marked closed by declaration counts or a hash-only unrelated receipt. '
    'All8 forward containers currently remain required/open. Propose their exact chapter-local versus whole-book dependency treatment for separate review; no deletion or silent exclusion. '
    'Chapter2 remains partial/null, Chapters3-16 unenumerated/null, Chapters1-16 Goal ACTIVE. Discovering a true missing mathematical terminal enters versioned repair and a fresh typed contract before proof work. No old mathematical terminal may weaken.')
write(RUN / '00_context.md', '# ' + TASK + '\n\n' + scope + '\n\nStacked on OPEN draft unmerged PR214 exact ' + BASE +
    '. Current canonical main=origin/main6847b678a73db68dee5101d6f05c2453c1405afc clean, freshly checked; shared Git E:/ABRL/research/.git and .lake/packages junction preserved. Same existing checkout retained active; prior branch/history/ignored evidence preserved. Requested GPT-6 Astra/medium, not runtime attestation; no new agents.\n\n'
    'ABRL: A Target-Faithful Autoformalization Harness and Lean 4 Library for Bandit and Reinforcement Learning Theory. Actual harness.tex read and compared with current docs/CLI. Method roles/file scope/semantic review are conventions plus particular command gates, not one runtime-enforced lifecycle. Current global SGB frontier/journals must not change. No Lean or reader edit before scoped review.\n')
write(RUN / '10_director-draft-v1.md', '# Director draft\n\n' + scope + '\n\nOne lower route: audit existing exact terminal bindings and their true receipt scope before proposing new coverage. No parallel chapter proof writing; only read-only future dependency lookup. Chapter completion is not a numeric counter over65 containers.\n')
write(RUN / '20_architect-draft-v1.md', '# Architect draft\n\n'
    'Dependency DAG: pinned PDF/pages -> accepted inventoryv3 -> current exact native headers/full modules -> matching scoped blind/source/BODY/FINAL records -> branch-by-branch coverage review -> candidate current public canary/axiom/root/Tests/full harness/fences -> reader/shared registry/site -> FINAL/native/post-native/delivery. '
    'Existing acceptance is reusable only with exact source/statement/body and relevant review scope. Mechanical SHA matches and source navigation overlap do not prove completeness. '
    'First finite leaf is a current declaration/provenance join. Draft creation changes only NEW OWN metadata; no mathematical theorem is newly proved by that join. Source references remain required and chapter-local treatment needs explicit reviewer judgment.\n')
write(RUN / 'memory_digest.md', '# Current draft memory\n\n' + scope + '\n\nCurrent prior mathematical milestone: PR214 ' + BASE +
    ',11 frozen production proof terminals/four definitions/two full canaries for one source theorem plus phi supplements. Actual combined gate/site/axiom/independent reviews and delivery evidence remain bound under prior RUN; site only99ee7910126db6014e565535252360dc45eb4b80, not a fresh site here.\n')
for folder, text in [
    ('tasks', '# ' + TASK + '\n\nKind: chapter audit; state: draft.\n\n' + scope),
    ('conversion-windows', '# Conversion window: ' + TASK + '\n\n' + scope + '\n\nFrozen Lean edits: NONE. NEW OWN contract/run/task/obligation/retrieval files only in draft; source mapping/reader updates require exact separate review.'),
    ('proof-obligations', '# Obligations: ' + TASK + '\n\n' + scope + '\n\n- [ ] Current exact declaration/type/BODY and appropriately scoped semantic receipt join.\n- [ ] Named source branches and overlap/forward classification review.\n- [ ] Any genuine new typed gap returned to contract repair.\n- [ ] Current chapter-wide Lean/public/canary/axiom/harness and reader/site/registry gates.\n- [ ] Distinct FINAL/native/post-native/scoped PR delivery.\n\nRequired proof total remains null; no counter closure claimed.'),
    ('research-wiki/retrieval-index', '# Retrieval: ' + TASK + '\n\nExisting accepted inventoryv3 and all scoped current Chapter2 module/contribution/semantic records are candidate retrieval substrates. Fresh actual list-lean-decls and native header retrieval next; no global reference-index overwrite.\n\n' + scope),
]:
    p = ROOT / folder / (TASK + '.md')
    if p.exists():
        assert folder != 'research-wiki/retrieval-index'
        p.write_bytes((text.rstrip('\n') + '\n').encode('utf8'))
    else:
        write(p, text)
event('native-draft-v1', 'draft', dict(scope=scope, source_fingerprint=sha(CONTRACT / 'source-fingerprint-v1.json'),
    stacked_base=BASE, lean_edit_scope=[], chapter_complete=False, whole_Goal='ACTIVE'))
fixed()
print('Actual OWN native draft, exact source checks and strict old-file baseline recorded; no theorem/chapter acceptance.', flush=True)
