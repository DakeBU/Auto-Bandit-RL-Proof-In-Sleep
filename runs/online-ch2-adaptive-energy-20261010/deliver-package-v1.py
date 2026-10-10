from native_acceptance_guard_v1 import *

review = RUN/'post-native-review-v1.json'
r = load(review)
assert r['verdict'] in ['accepted', 'accepted-with-explicit-delta'] and not r['required_repairs']
assert sha(Path(__file__)) == r['approved_delivery_helper_sha256']
assert sha(r['report']) == r['report_sha256']
assert sha(r['input_manifest']) == r['input_manifest_sha256']
for row in load(r['input_manifest'])['rows']:
    assert sha(row['path']) == row['sha256'], row['path']
final_fixed(after=True)
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], encoding='utf8').strip() == '3e5669e4b4e73a01d5c301e37aaa2eef07bd289b'

allowed = {PUBLIC.relative_to(ROOT).as_posix(), 'Tests/OnlineAdaptiveEnergyCanary.lean',
    'BanditRLProof.lean', 'Tests.lean', 'website/content/chapters.json',
    'website/content/readings.json', 'website/content/highlights.json',
    'docs/contracts/online-book-v1/coverage.json'} | set(load(NATIVE_PLAN)['mutable_paths'])
def owned(rel):
    return rel in allowed or rel.startswith(RUN.relative_to(ROOT).as_posix()+'/') or rel.startswith(CONTRACT.relative_to(ROOT).as_posix()+'/')

paths = subprocess.check_output(['git', 'diff', '--name-only', BASE], encoding='utf8').splitlines()
paths += subprocess.check_output(['git', 'ls-files', '--others', '--exclude-standard'], encoding='utf8').splitlines()
assert all(owned(x) for x in paths), [x for x in paths if not owned(x)]
capture('delivery-scoped-stage-v1', 'git', 'add', '--', *sorted(set(paths)))
capture('delivery-fullBASE-whitespace-v1', 'git', 'diff', '--cached', '--check', BASE)
staged = subprocess.check_output(['git', 'diff', '--cached', '--name-only'], encoding='utf8').splitlines()
assert staged and all(owned(x) for x in staged)
index = []
for rel in staged:
    raw = subprocess.check_output(['git', 'show', ':'+rel])
    assert raw == (ROOT/rel).read_bytes(), rel
    index.append(dict(path=rel, sha256=sha(ROOT/rel), bytes=len(raw), index_equals_RAW=True))
write(RUN/'delivery-staged-RAW-v1.json', dict(rows=index,
    scope='All staged paths before the evidence commit; this receipt is added separately below.'))
subprocess.run(['git', 'add', '--', RUN.relative_to(ROOT).as_posix()], check=True)
staged = subprocess.check_output(['git', 'diff', '--cached', '--name-only'], encoding='utf8').splitlines()
assert all(owned(x) for x in staged)
for rel in staged:
    assert subprocess.check_output(['git', 'show', ':'+rel]) == (ROOT/rel).read_bytes(), rel
subprocess.run(['git', 'diff', '--cached', '--check', BASE], check=True)
final_fixed(after=True)

outdir = ROOT/'tmp/online-ch2-adaptive-energy-delivery-v1'
assert not outdir.exists()
outdir.mkdir()
def receipt(label, *args):
    start = time.monotonic()
    process = subprocess.run(list(map(str, args)), cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    write(outdir/(label+'.json'), dict(command=list(map(str, args)), actual_exit=process.returncode,
        cwd=ROOT.as_posix(), seconds=time.monotonic()-start,
        stdout_sha256=hashlib.sha256(process.stdout).hexdigest(),
        stdout_base64=base64.b64encode(process.stdout).decode('ascii')))
    print(label, 'actual exit', process.returncode, flush=True)
    assert process.returncode == 0, process.stdout.decode('utf8', errors='replace')
    return process.stdout.decode('utf8', errors='replace')

receipt('evidence-commit', 'git', 'commit', '-m', 'Record reviewed adaptive energy prerequisite validation')
head = receipt('actual-head', 'git', 'rev-parse', 'HEAD').strip()
assert receipt('clean-after-commit', 'git', 'status', '--porcelain=v1') == ''
for label, base in [('contributor-stack', BASE), ('contributor-main', 'origin/main')]:
    output = receipt(label, sys.executable, '-B', '-X', 'utf8', 'tools/check_contributor_contract.py', '--base', base)
    assert 'Contributor contract: N/A' not in output and 'BanditRLProof/OnlineAdaptiveEnergy.lean' in output
receipt('ordinary-fullBASE-whitespace', 'git', 'diff', '--check', BASE)
receipt('nonforce-push', 'git', 'push', '-u', 'origin', BRANCH)
remote = receipt('remote-exact-head', 'git', 'ls-remote', '--heads', 'origin', BRANCH).split()[0]
assert remote == head
body = ('This stacked package proves the cumulative-energy inequality used by the required Chapter2 adaptive-rate '
    'forward claim, with leading/interior zero feedback, T=0 and D=0. Three shared production propositions '
    '(scalar, norm, scale) represent one unnumbered source display after Lemma4.13 and before Eq4.4 '
    '(Orabona arXiv:1912.13213v10, printed40/PDF52). The scalar proof reuses the existing Tsallis square-root '
    'supporting line and telescopes; zero prefixes are handled algebraically.\n\n'
    'Two complete public canaries retain all8/3conjuncts; actual compiled VALUE checks trace all five selected '
    'inequalities to the public source bound. Distinct staged semantic/source and original-pixel reviews, '
    'standard-only axiom audits, frozen statements and failed attempts are retained in '
    '`runs/online-ch2-adaptive-energy-20261010/` and `docs/contracts/online-ch2-adaptive-energy-v1/`.\n\n'
    'Validation: combined Lean root0 (9117 cached inclusive jobs), Tests0 (9294), full harness0 '
    '(472tests/7skips), actual ProofGraphExport/check passed; focused/public/fence/OWNshadow and nonempty '
    'contributor gates0. Clean local lean-verified site source is3e5669e4b4e73a01d5c301e37aaa2eef07bd289b; '
    'complete11055oldregistryobjects retained+3canonical proofs=11058. Six original images were reviewed. '
    'The evidence commit is distinct from that site source.\n\n'
    'Stacked on OPEN draft unmerged #216 exact873039ee2d3247eacaa9b3c95d765954e6453611, '
    'base `codex/research-online-ch2-adaptive-summation`. '+load(NATIVE_PLAN)['boundary']+'\n')
bodyfile = outdir/'PR-body.md'
write(bodyfile, body)
existing = json.loads(receipt('existing-PR-query', 'gh', 'pr', 'list', '--head', BRANCH,
    '--state', 'all', '--json', 'number,url,state'))
assert existing == [], existing
url = receipt('draft-PR-create', 'gh', 'pr', 'create', '--draft', '--head', BRANCH,
    '--base', 'codex/research-online-ch2-adaptive-summation',
    '--title', 'Prove the zero-prefix adaptive energy bound', '--body-file', bodyfile).strip()
write(outdir/'delivery-binding.json', dict(head=head, branch=BRANCH, stacked_base=BASE,
    PR_url=url, PR_body_sha256=sha(bodyfile), local_site_source='3e5669e4b4e73a01d5c301e37aaa2eef07bd289b',
    official_attachment='pending; call the app tool immediately', actual_delivery_review='pending',
    deployed=False, merged=False, chapter_complete=False, whole_Goal='active'))
print('ATTACH_REQUIRED '+url, flush=True)
