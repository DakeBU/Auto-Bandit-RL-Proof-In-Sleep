from common import *
import re
header = '''theorem state_prefix (V : Domain (E := E)) (α D : ℝ) (loss loss' : ℕ → E → EReal)
    (x₁ : E) (p : SupportPolicy (E := E)) (t : ℕ)
    (hloss : ∀ s < t, loss s = loss' s) :
    state V α D loss x₁ p t = state V α D loss' x₁ p t := by
'''
write(CONTRACT/'algorithm-state_prefix-header-draft-v1.lean.txt', header)
context = (CONTRACT/'algorithm-definition-context-draft-v2.lean.txt').read_text(encoding='utf8')
prop = header[len('theorem state_prefix'):].rstrip()[:-len(':= by')]
write(RUN/'AlgorithmPrefixTypeProbeV1.lean', context+'\n#check (∀ '+prop.replace(' :\n', ',\n', 1).lstrip()+')\nend BanditRL.OnlineAdaptiveOSD\n')
renamings = load(CONTRACT/'algorithm-neutral-renaming-v1.json')['renamings'] + [['state_prefix', 'certificate_three']]
packet = context+'\n'+header.replace(' := by', '')+'\nend BanditRL.OnlineAdaptiveOSD\n'
for old, new in renamings:
    packet = re.sub(r'(?<![\w.])'+re.escape(old)+r'(?!\w)', new, packet)
write(CONTRACT/'algorithm-prefix-neutral-v1.lean.txt', packet)
code, out = capture('algorithm-prefix-type-probe-v1', 'lake', 'env', 'lean', RUN/'AlgorithmPrefixTypeProbeV1.lean', required=False)
print(out)
sys.exit(code)
