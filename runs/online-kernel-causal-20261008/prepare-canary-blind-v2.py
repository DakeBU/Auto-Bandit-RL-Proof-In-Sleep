from common_proving_v1 import *
import re

proving_fixed()
frozen = load(RUN/'canary-frozen-targets-v2.json')
assert sha(RUN/'canary-proposal-v2.lean.txt') == frozen['proposal_sha256']
base = (RUN/'neutral-context-and-statements-v1.lean.txt').read_text(encoding='utf8').rsplit('end Neutral',1)[0]
coin = '''
def cLaw : Measure ℝ :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac 0 + (1 / 2 : ℝ≥0∞) • Measure.dirac 1
instance cLaw_probability : IsProbabilityMeasure cLaw
def iLaw : Measure (ℕ → ℝ) := Measure.infinitePi (fun _ : ℕ => cLaw)
instance iLaw_probability : IsProbabilityMeasure iLaw
'''
proposal = (RUN/'canary-proposal-v2.lean.txt').read_text(encoding='utf8')
context = proposal.split('namespace Tests.OnlineGuessingKernelCausal',1)[1].split('private theorem selected_joint_measurable',1)[0]
for name in ['lowLaw_probability','highLaw_probability','switchSet_measurable']:
    # Retain instance/theorem propositions without their proof bodies in the neutral input.
    pattern = r'((?:instance|theorem) '+name+r'.*?) := by.*?(?=\n(?:instance|/--|def |theorem))'
    context, n = re.subn(pattern,r'\1\n',context,count=1,flags=re.S)
    assert n == 1, name
headers = '\n\n'.join(t['header'] for t in frozen['targets'] if not t['name'].endswith('switchSet_measurable'))
mapping = load(RUN/'neutral-renaming-bindings-v1.json')['mapping']
mapping.update(dict(lowLaw='lLaw',highLaw='hLaw',switchSet='sSet',switchSet_measurable='sSet_measurable',
    decisionKernel='k',oneHistory='h1',selectedSampler='fStar',observationLaw='nStar',
    gameLaw='mStar',prediction='pStar',target='yStar',iidLaw='iLaw',
    lowLaw_probability='lLaw_probability',highLaw_probability='hLaw_probability'))
for i,t in enumerate(frozen['targets']):
    name = t['name'].split('.')[-1]
    if name != 'switchSet_measurable':
        mapping[name] = 'c'+str(i+1)
joined = base+'\nopen scoped ENNReal\n'+coin+context+'\n'+headers+'\nend Neutral\n'
for old in sorted(mapping,key=len,reverse=True):
    joined = re.sub(r'\b'+re.escape(old)+r'\b',mapping[old],joined)
write(RUN/'neutral-canary-context-statements-v2.lean.txt',joined)
write(RUN/'neutral-canary-instructions-v2.md',
      'Reconstruct only the supplied neutral context and exact canary propositions. The q1-q5 clauses are the previously supplied base interface; reconstruct the newly supplied c-clauses and explain how ONE fStar is chosen before every law and horizon. Read lLaw/hLaw, sSet, h1 and IID nStar literally. Identify actual action/observation dependence, stochastic support, law-dependent AE statements, fixed-expected benchmark outside expectation, exactT/4, zero and positive two-round/variance values. Decode assumptions and seven semantic slots; distinguish proof/interface invocation from verified implementation. No source identity or previous acceptance verdict supplied. Reused actor history disclosed; no absolute blind/human/external/runtime attestation. Requested Astra/medium. Read ONLY neutral-canary-context-statements-v2.lean.txt and this instruction. Write ONLY canary-blind-reconstruction-v2.md and canary-blind-receipt-v2.json in the same directory, binding both RAW inputs before/after and report SHA. No source/proof/package/chapter/Goal acceptance.\n')
write(RUN/'neutral-canary-bindings-v2.json',dict(mapping=mapping,
      proposal_sha256=frozen['proposal_sha256'],frozen_targets_sha256=sha(RUN/'canary-frozen-targets-v2.json'),
      exact_parent_neutral_sha256=sha(RUN/'neutral-context-and-statements-v1.lean.txt'),
      neutral_sha256=sha(RUN/'neutral-canary-context-statements-v2.lean.txt'),
      source_identity_excluded=True,proof_bodies_excluded=True,base_context_reused=True,
      source_review_pending=True))
print('Neutral canary reconstruction packet frozen; no acceptance.',flush=True)
