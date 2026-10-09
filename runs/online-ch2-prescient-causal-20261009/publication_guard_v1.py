from common import *
CANARY = ROOT / 'Tests/OnlinePrescientBregmanCanary.lean'
CONTRIBUTION = ROOT / 'research-wiki/contribution-contracts' / (TASK + '.json')
SITE = ROOT / 'tmp/online-ch2-prescient-causal-site-v1'
sys.path.insert(0, str(ROOT))
from tools.abrl_lifecycle import statement_hash, lean_declaration_header

def fixed():
    assert Path.cwd() == ROOT and sha(PDF) == PDF_SHA
    assert subprocess.check_output(['git', 'branch', '--show-current'], encoding='utf8').strip() == BRANCH
    binding = load(RUN / 'publication-review-binding-v1.json')
    rp = RUN / 'canary-BODY-publication-review-v1.json'
    r = load(rp)
    assert sha(rp) == binding['review_sha256']
    assert r['BODY_verdict'] in ['accepted', 'accepted-with-explicit-delta']
    assert r['materialization_verdict'] in ['accepted', 'accepted-with-explicit-delta']
    assert not r['required_repairs']
    plan = CONTRACT / 'exact-publication-plan-v2.json'
    assert sha(plan) == binding['plan_sha256']
    allowed = {row['path']: row for row in load(plan)['rows']}
    assert set(allowed) == {(ROOT / p).as_posix() for p in [
        'BanditRLProof.lean', 'Tests.lean', 'website/content/chapters.json',
        'website/content/readings.json', 'website/content/highlights.json']}
    for row in load(RUN / 'baseline-v1.json')['rows']:
        if row['path'] not in allowed:
            assert sha(row['path']) == row['sha256'], row['path']
        else:
            a = allowed[row['path']]
            assert a['before_sha256'] == row['sha256']
            assert sha(a['before_snapshot']) == a['before_sha256']
            assert sha(a['after_snapshot']) == sha(a['path']) == a['after_sha256']
            assert Path(a['path']).read_bytes() == Path(a['after_snapshot']).read_bytes()
    c = load(RUN / 'complete-candidate-inspected-v1.json')
    assert sha(PUBLIC) == c['production_sha256'] and sha(CANARY) == c['test_sha256']
    for p, cp in [(PUBLIC, CONTRACT / 'stabilized-v1.json'), (CANARY, CONTRACT / 'canary-stabilized-v1.json')]:
        for t in load(cp)['targets']:
            assert statement_hash(lean_declaration_header(p, t['declaration'])) == t['statement_hash']
    source = PUBLIC.read_text(encoding='utf8')
    for d in load(CONTRACT / 'stabilized-v1.json')['definitions']:
        assert d['exact_definition'] in source
        assert hashlib.sha256(d['exact_definition'].encode('utf8')).hexdigest() == d['exact_definition_UTF8_sha256']
    assert sha(RUN / 'selected-dependency-data-v1.json') == c['graph_sha256']
