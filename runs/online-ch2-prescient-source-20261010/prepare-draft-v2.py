from common import *
import re
fixed()
old = CONTRACT / 'targets-draft-v1.txt'
text = old.read_text(encoding='utf8')
before = '(η : ℕ → ℝ) (hη : ∀ t < T, 0 < η t)\n    (loss : ℕ → E → EReal) (x0 : E) (x : ℕ → E) (T : ℕ) (hT : 0 < T)'
after = '(η : ℕ → ℝ)\n    (loss : ℕ → E → EReal) (x0 : E) (x : ℕ → E) (T : ℕ) (hT : 0 < T)\n    (hη : ∀ t < T, 0 < η t)'
assert text.count(before) == 1
draft = CONTRACT / 'targets-draft-v2.txt'
write(draft, text.replace(before, after))
write(RUN/'draft-binder-correction-v2.json', dict(before=rows([old]), after=rows([draft]), status='draft-only, before stabilization/proof', reason='Move positivity binder after T; avoid unintended autoimplicit horizon. No source assumption or conclusion changed. v1 retained.'))
headers = []
for part in draft.read_text(encoding='utf8').split('-- TARGET ')[1:]:
    name, header = part.split('\n', 1)
    headers.append(dict(name=name, header=header.strip(), sha256=hashlib.sha256((header.strip()+'\n').encode('utf8')).hexdigest()))
assert len(headers) == 6
prefix = 'import BanditRLProof.OnlinePrescientBregmanRegret\nnoncomputable section\nopen Set Finset\nopen BanditRL.OnlineBregman\n'
contexts = [
    'namespace BanditRL.OnlineConvex\nvariable {E : Type*}\n',
    'namespace BanditRL.OnlinePrescientBregman\nvariable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]\n',
    'namespace BanditRL.OnlinePrescientBregman\nvariable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]\n',
    'namespace BanditRL.OnlinePrescientBregman\nvariable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]\n',
    'namespace BanditRL.OnlinePrescientBregman\nvariable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]\n',
    'namespace BanditRL.OnlinePrescientBregman\nvariable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]\n'
]
probe = prefix + 'set_option autoImplicit false\n'
for row, context in zip(headers, contexts):
    row['context'] = context
    binders = row['header'].split('theorem '+row['name'].rsplit('.',1)[1],1)[1]
    binders, conclusion = binders.rsplit(' :\n',1)
    probe += context + '#check fun '+binders.strip()+' =>\n  ('+conclusion.strip()+' : Prop)\nend\n'
write(CONTRACT/'headers-draft-v2.json',dict(imports=prefix,targets=headers))
write(RUN/'TargetTypesV2.lean',probe)
code, out = capture('draft-type-probe-v2','lake','env','lean',RUN/'TargetTypesV2.lean',required=False)
write(RUN/'draft-type-probe-inspected-v2.json',dict(actual_exit=code, target_count=len(headers), source_files=rows([draft,CONTRACT/'headers-draft-v2.json',RUN/'TargetTypesV2.lean']), actual_stdout=out, inference='Types only; no theorem body/placeholder/axiom and not proof compilation.'))
assert code == 0
