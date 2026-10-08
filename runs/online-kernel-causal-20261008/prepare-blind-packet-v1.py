from common_v1 import *
import re

assert load(RUN / 'draft-typecheck-v2-exit.json')['actual_exit'] == 0
context = (CONTRACT / 'context-v2.lean.txt').read_text(encoding='utf8')
assert context.startswith('import BanditRLProof.OnlineGuessingRandomizedIID\n')
context = context.split('\n',1)[1]
context = context.replace('namespace BanditRL.OnlineLearning', 'namespace Neutral')
context = context.rsplit('end BanditRL.OnlineLearning',1)[0]
parent = (ROOT / 'BanditRLProof/OnlineGuessingIIDBenchmark.lean').read_text(encoding='utf8')
minimum = re.search(r'noncomputable def expectedFixedMinimum.*?(?=\nnoncomputable def)',parent,re.S).group(0).strip()
regret = re.search(r'noncomputable def expectedFixedRegret.*?(?=\n/--)',parent,re.S).group(0).strip()
context += '\n\n' + minimum + '\n\n' + regret + '\n'
headers = (CONTRACT / 'targets-v1.lean.txt').read_text(encoding='utf8')
mapping = dict(KernelDecisionHistory='H', KernelDecisionSampler='F', kernelGeneratedActions='A',
    kernelCausalPolicy='B', kernelGeneratedHistory='C', kernelGeneratedPrediction='P',
    kernelUniformTapeLaw='R', kernelGameLaw='M', expectedFixedMinimum='b', expectedFixedRegret='r',
    kernel_sampler_family_exists='q1', kernel_sampler_causal_process='q2',
    kernel_sampler_joint_law='q3', kernel_sampler_conditional_law='q4',
    causal_kernel_realization_and_expectedFixed_excess='q5')
joined = context + '\n' + headers + '\nend Neutral\n'
for old in sorted(mapping,key=len,reverse=True):
    joined = re.sub(r'\b'+re.escape(old)+r'\b',mapping[old],joined)
write(RUN / 'neutral-context-and-statements-v1.lean.txt', joined)
write(RUN / 'neutral-input-instructions-v1.md',
      'Reconstruct only the exact proposed mathematical objects/definitions/statements supplied in neutral-context-and-statements-v1.lean.txt. No source identity or prior verdict is provided. Describe q1-q5 in natural language and LaTeX with all assumptions, quantifiers/order, information timing/initialization, actual recursion consistency, probability mode/measure, and exact benchmark. Differentiate definition/type elaboration from existence/proof evidence. Report interpretations/ambiguities instead of filling hidden hypotheses. Read the definitions of b/r literally. Give no source acceptance verdict. Reused decoder history is disclosed; no absolute blindness or runtime model/effort attestation. Requested GPT-6 Astra/medium. Write ONLY blind-reconstruction-v1.md and blind-receipt-v1.json in this same directory, with input RAW SHA before/after, report SHA and limitations.\n')
write(RUN / 'neutral-renaming-bindings-v1.json', dict(mapping=mapping,
    exact_context_sha256=sha(CONTRACT / 'context-v2.lean.txt'), exact_headers_sha256=sha(CONTRACT / 'targets-v1.lean.txt'),
    exact_benchmark_parent_sha256=sha(ROOT / 'BanditRLProof/OnlineGuessingIIDBenchmark.lean'),
    neutral_input_sha256=sha(RUN / 'neutral-context-and-statements-v1.lean.txt'),
    only_identifier_namespace_renaming_and_exact_benchmark_definition_inclusion=True,
    source_identity_excluded_from_decoder_packet=True, absolute_blindness_claimed=False))
print('Exact neutral two-input packet prepared; no semantic verdict or new proof.',flush=True)
