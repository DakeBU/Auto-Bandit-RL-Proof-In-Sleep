from common_v1 import *
import re
fixed()
target=load(CONTRACT/'targets-v1.json');neutral=[]
for t in target['targets']:
    short=t['name'].rsplit('.',1)[-1]
    header=re.sub(r'^(theorem|lemma)\s+'+re.escape(short)+r'\b',r'\1 '+t['id'],t['header'])
    assert header!=t['header']
    neutral.append(header)
write(CONTRACT/'neutral-targets-v1.lean.txt','\n\n'.join(neutral))
write(RUN/'neutral-review-packet-v1.md',
    'Reconstruct EACH selected mathematical target A001 onward from neutral-targets-v1.lean.txt and necessary exact context-v1.lean.txt ONLY. No source identity/anchor/intention/verdict is supplied. Identify objects, quantifier order, assumptions, metric, constants/index/degenerate cases, information/probability and excluded regimes. Separate model definitions from universal performance/conditional characterizations, supplied independence from derived causal independence, fixed expected benchmark from expected hindsight minimum, upper asymptotics from ordinary limits. Definitions are context only, not new theorems. Give natural-language and LaTeX interpretations and ambiguity/required missing context. Do not read source-map/intent/fingerprint/reports or proof bodies/priors beyond supplied definition context. Disclose reused actor history and requested Astra/medium without runtime/absolute-blind/human/external attestation. Outputs ONLY blind-reconstruction-v1.md/blind-receipt-v1.json with twoinput RAW before/after and target_count; hash inputindex separately, no proof/acceptance verdict.')
write(RUN/'blind-inputs-v1.json',dict(rows=rows([CONTRACT/'neutral-targets-v1.lean.txt',CONTRACT/'context-v1.lean.txt']),
    target_count=len(neutral),source_identity_or_prior_verdict_included=False))
fixed()
print('Neutral targets:',len(neutral),'complete two-file context packet prepared, v1 global-name failure retained.',flush=True)
