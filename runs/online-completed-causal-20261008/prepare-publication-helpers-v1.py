from common_body_v2 import *

fixed_integrated()
prior = ROOT / 'runs/online-ae-causal-20261008'
source = (prior / 'commit_owned_v1.py').read_bytes()
assert source.count(b'from common_body_v1 import *') == 1
write(RUN / 'commit_owned_v1.py', source.replace(
    b'from common_body_v1 import *', b'from common_body_v2 import *'))
source = (prior / 'prepare-candidate-commit-v1.py').read_text(encoding='utf8')
source = source.replace("load(RUN/'BODY-mutable-integration-bindings-v1.json')['rows']",
    "load(RUN/'draft-baseline-v1.json')['rows']")
source = source.replace("rel.startswith(RUN.relative_to(ROOT).as_posix()+'/prior-PR197-')",
    "rel.startswith(RUN.relative_to(ROOT).as_posix()+'/stacked-base-current-')")
source = source.replace('Online Learning C1: prove AE causal versions and original IID excess',
    'Online Learning C1: construct completed-information real versions')
source = source.replace('basePR=197', 'basePR=198')
write(RUN / 'prepare-candidate-commit-v1.py', source)
source = (prior / 'build-clean-site-v4.py').read_text(encoding='utf8')
source = source.replace('from common_reader_v4 import *', 'from common_body_v2 import *')
source = source.replace('online-ae-causal-site-v4', 'online-completed-causal-site-v1')
source = source.replace('online-ae-causal-site-build-v4.log', 'online-completed-causal-site-build-v1.log')
source = source.replace('site-build-v4', 'site-build-v1').replace('site-check-v4', 'site-check-v1')
source = source.replace('registry-check-v4', 'registry-check-v1').replace('verify-registry-v4.py', 'verify-registry-v1.py')
write(RUN / 'build-clean-site-v1.py', source)
old = ROOT / 'tmp/online-ae-causal-site-v4/books/registry.json'
assert old.is_file()
import gzip
old_data = load(old)
assert old_data['lean_verified'] and len(old_data['nodes']) == 10938
write(RUN / 'registry-base-snapshot-v1.json.gz', gzip.compress(old.read_bytes(), mtime=0))
source = (prior / 'verify-registry-v4.py').read_text(encoding='utf8')
source = source.replace('from common_reader_v4 import *', 'from common_body_v2 import *')
source = source.replace('online-ae-causal-site-v4', 'online-completed-causal-site-v1')
source = source.replace('OnlineGuessingAECausal', 'OnlineGuessingCompletedCausal')
source = source.replace('reader-proposal-v3.json', 'reader-proposal-v1.json')
source = source.replace('registry-v4.json', 'registry-v1.json').replace('new_notes=3', 'new_notes=4')
source = source.replace('three_complete_headers_present', 'four_complete_headers_present')
source = source.replace('three public proofs', 'four public proofs')
write(RUN / 'verify-registry-v1.py', source)
source = (prior / 'capture-reader-v4.cjs').read_text(encoding='utf8')
source = source.replace('!==3', '!==4').replace('three new public nodes', 'four new public nodes')
source = source.replace('ae-causal-source-card', 'completed-causal-source-card')
source = source.replace('-v4.', '-v1.').replace('-v4.png', '-v1.png')
source = source.replace('actual-three-new-proof-notes', 'actual-four-new-proof-notes')
write(RUN / 'capture-reader-v1.cjs', source)
write(RUN / 'publication-helper-adaptation-v1.json', dict(
    source_package='online-ae-causal-20261008',
    source_helper_bytes_retained=True, current_guard='common_body_v2.py',
    stacked_base_PR=198, old_registry_nodes=10938,
    reader_and_module_capture_counts=4, current_browser_and_DOM_names='formula-render-v1-*',
    all_acceptance_or_rendering_evidence_pending=True))
