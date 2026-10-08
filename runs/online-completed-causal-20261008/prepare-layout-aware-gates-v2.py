from common_reader_v2 import *

fixed_integrated()
source = (RUN / 'prepare-FINAL-review-v1.py').read_text(encoding='utf8')
source = source.replace('from common_body_v2 import *', 'from common_reader_v2 import *')
for prefix in ['pixel-review', 'registry', 'site-build', 'site-check', 'registry-check',
               'formula-render', 'online-completed-causal-site']:
    source = source.replace(prefix + '-v1', prefix + '-v2')
source = source.replace('contributor-candidate-stacked-v1', 'contributor-current-stacked-v2')
source = source.replace('contributor-candidate-origin-main-v1', 'contributor-current-origin-main-v2')
source = source.replace('receipt-schema failure versions', 'receipt-schema and actual horizontal-overflow failure versions')
source = source.replace('exact prospective PR title/body', 'exact prospective PR title/body and source-card aligned line-break repair')
write(RUN / 'prepare-FINAL-review-v2.py', source)
source = (RUN / 'common_accepted_v1.py').read_text(encoding='utf8')
source = source.replace('from common_body_v2 import *', 'from common_reader_v2 import *')
source = source.replace('formula-render-v1.json', 'formula-render-v2.json')
write(RUN / 'common_accepted_v2.py', source)
for filename in ['record-acceptance-v1.py', 'prepare-post-native-review-v1.py',
                 'prepare-reviewed-commit-v1.py', 'deliver-reviewed-draft-v1.py']:
    source = (RUN / filename).read_text(encoding='utf8')
    source = source.replace('from common_accepted_v1 import *', 'from common_accepted_v2 import *')
    source = source.replace('registry-v1.json', 'registry-v2.json')
    source = source.replace('genuine v1 browser/DOM/capture evidence', 'genuine v2 browser/DOM/capture evidence; actual v1 overflow retained')
    write(RUN / filename.replace('-v1.py', '-v2.py'), source)
native_labels = [('contributor-current-stacked-v2', BASE),
                 ('contributor-current-origin-main-v2', 'origin/main')]
for label, base in native_labels:
    gate(label, sys.executable, '-B', '-X', 'utf8',
         'tools/check_contributor_contract.py', '--base', base)
