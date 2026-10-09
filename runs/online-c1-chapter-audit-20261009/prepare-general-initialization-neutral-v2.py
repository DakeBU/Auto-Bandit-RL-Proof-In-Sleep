from common_v1 import *
import re
fixed()
p=CONTRACT/'general-initialization-intent-draft-v2.md'
s=p.read_text(encoding='utf8')
assert 'difference<=1.5 is NOT' in s
write(CONTRACT/'general-initialization-intent-draft-v3.md',s.replace('difference<=1.5 is NOT a printed or sharp coefficient','difference<=1. The additive5 in G2 is NOT a printed or sharp coefficient')+'\nThis v3 clarifies a punctuation typo in retained draft-v2 intent (<=1.5 incorrectly joined the correction bound and additive5). All four draft Lean headers/hashes remain unchanged; no theorem was proved or source contract accepted by this clarification.')
targets=load(CONTRACT/'general-initialization-targets-draft-v2.json')['new_targets']
write(CONTRACT/'general-initialization-neutral-targets-v2.lean.txt','\n\n'.join(re.sub(r'^theorem\s+\w+', 'theorem '+t['id'], t['header']) for t in targets))
needed={'comparatorRegret','NoRegret','empiricalMean','meanPredict','ftlPredict','squaredBestRegret'}
defs=[d for d in load(CONTRACT/'definition-context-v1.json')['definitions'] if d['name'].rsplit('.',1)[-1] in needed]
assert len(defs)==6
write(CONTRACT/'general-initialization-neutral-context-v2.lean.txt','Ambient notation: open Filter BanditRL.OnlineLearning. Exact supporting definitions only, no proof/source identity/verdict.\n\n'+'\n\n'.join('Actual scoped name '+d['name']+'\n'+d['exact_source_block'] for d in defs))
write(RUN/'general-initialization-neutral-inputs-v2.json',dict(rows=rows([CONTRACT/'general-initialization-neutral-targets-v2.lean.txt',CONTRACT/'general-initialization-neutral-context-v2.lean.txt']),target_count=4,context_definitions=6,source_identity_or_proof_or_prior_verdict_included=False))
write(RUN/'general-initialization-neutral-packet-v2.md','''Reconstruct ONLY the four G001-G004 exact neutral draft type headers and six exact context definitions indexed in general-initialization-neutral-inputs-v2.json. Source/proof/identity/intention/prior verdict absent; don't read draft-intent/source maps/current source review. Explain EACH in natural prose and LaTeX/seven slots, distinguishing actual same-run predictor vs arbitrary supplied trace, comparator minimum, arbitrary real vs feasible initial inputs, finite prefix vs all-time support, T0 vs positiveT and constants, upper-epsilon vs ordinary limits and fixed vs true-best metric. Do not infer the truth/proof of a draft type or source acceptance. Only output general-initialization-blind-reconstruction-v2.md/general-initialization-blind-receipt-v2.json in this RUN, binding two raw inputs plus index/packet beforeafter, all4 complete reconstructions and remaining gaps. Reused actor/history/requested Astra medium disclosed, no absolute-blind/human/external/runtime attestation. Old fifty-target decoder files untouched; this is an additional four-target proposed repair type reconstruction only.''')
fixed();print('General-initialization draft blind packet:4 headers,6 actual definitions; v2 intent typo retained/explicitly clarified in v3.')
