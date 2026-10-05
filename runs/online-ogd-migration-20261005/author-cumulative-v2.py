"""Adapt true finite telescopes to the new frozen regularity interface."""
from pathlib import Path
import hashlib, json, re
run = Path(__file__).parent
module = Path('BanditRLProof/OnlineGradientDescentSource.lean')
old_fixed = Path('BanditRLProof/OnlineGradientDescent.lean')
old_variable = Path('BanditRLProof/OnlineGradientDescentVariable.lean')
binding = json.loads((run/'body-one-step-v2-01-bindings.json').read_text())
assert hashlib.sha256(module.read_bytes()).hexdigest() == binding['module_sha256']
text = module.read_text(encoding='utf-8').rsplit('end BanditRL.OnlineGradientDescentSource',1)[0]
names = ['theorem_2_13_fixed', 'variable_one_step', 'theorem_2_13_variable_bound',
         'theorem_2_13_variable', 'equation_2_1_distance', 'equation_2_1']
comments = {
    'theorem_2_13_fixed': 'Fixed-step telescope on the actual recurrence; no bounded-domain premise.',
    'variable_one_step': 'The current actual scheduled update supplies the divided one-step inequality.',
    'theorem_2_13_variable_bound': 'The weighted potential telescope retains the negative terminal at the last played step.',
    'theorem_2_13_variable': 'The bounded-set diameter supplies the source finite-diameter bound.',
    'equation_2_1_distance': 'Positive horizon tuning uses gradients of this same tuned trajectory.',
    'equation_2_1': 'One horizon-tuned learner satisfies the bound for every feasible comparator.'}
for name in names:
    original = old_fixed if name.startswith('equation') or name.endswith('_fixed') else old_variable
    match = re.search(r'(?ms)^theorem '+name+r'\b.*? := by\n(.*?)(?=\n(?:/--|theorem |end ))',
                      original.read_text(encoding='utf-8'))
    assert match, name
    header = (Path('docs/contracts/online-ogd-migration-v2')/(name+'-header.txt')).read_text(encoding='utf-8').strip()
    text += '/-- '+comments[name]+' -/\n'+header+' := by\n'+match.group(1).rstrip()+'\n\n'
text += 'end BanditRL.OnlineGradientDescentSource\n'
with module.open('w',encoding='utf-8',newline='\n') as f: f.write(text)
print('Six frozen cumulative targets authored with actual recurrence telescopes; compilation pending.')
