from common_v1 import *
from lower_common_v1 import capture,event
sys.path.insert(0,str(ROOT))
from tools.abrl_lifecycle import lean_declaration_header,statement_hash

PUBLIC=ROOT/'BanditRLProof/OnlineNonsmoothExamples.lean'
CANARY=ROOT/'Tests/OnlineNonsmoothExamplesCanary.lean'

def fixed():
    """New root-integration stage; the original baseline guard is unchanged."""
    assert Path.cwd()==ROOT and sha(PDF)==PDF_SHA
    assert subprocess.check_output(['git','branch','--show-current'],encoding='utf8').strip()==BRANCH
    review=RUN/'nonsmooth-canary-publication-review-v1.json'
    assert sha(review)=='ac12e81d5ea3299b941237589ebad74fd7d0ea6ca0a58ae78069fdb1f66b590c'
    r=load(review)
    assert r['canary_contract_verdict']==r['canary_body_verdict']=='accepted'
    plan=load(CONTRACT/'nonsmooth-exact-import-plan-v1.json')
    assert r['approved_future_exact_scope']['exact_root_and_Test_imports_only']==plan
    roots={Path(p['path']).resolve().as_posix():p for p in plan['rows']}
    for row in load(RUN/'baseline-v1.json')['rows']:
        key=Path(row['path']).resolve().as_posix()
        if key not in roots:
            assert sha(row['path'])==row['sha256'],row['path']
        else:
            p=roots[key];before=Path(p['snapshot']).read_bytes()
            assert hashlib.sha256(before).hexdigest()==row['sha256']==p['baseline_sha256']
            assert Path(p['path']).read_bytes()==before+p['append_exact_utf8'].encode('utf8')
            assert sha(p['path'])==p['permitted_result_sha256']
    assert sha(PUBLIC)==load(CONTRACT/'nonsmooth-current-candidate-v1.json')['current_production_file_sha256']
    assert sha(CANARY)==load(RUN/'nonsmooth-canaries-candidate-v1.json')['test_module_sha256']
    for t in load(CONTRACT/'nonsmooth-targets-draft-v1.json')['targets']:
        assert statement_hash(lean_declaration_header(PUBLIC,t['declaration']))==t['statement_hash']
    for t in load(CONTRACT/'nonsmooth-canary-contracts-v2.json')['targets']:
        assert statement_hash(lean_declaration_header(CANARY,t['declaration']))==t['statement_hash']
    # Frozen source/contract inputs are still unchanged; only exact reviewed
    # root appends differ from baseline. Wrong reader-v1 remains unapplied.
    for row in load(RUN/'source-contract-repair-review-v1.json')['raw_input_checks']:
        assert sha(row['path'])==row['before_sha256']==row['after_sha256']
