from common_v1 import *
fixed()
prior = (RUN/'neutral-identities-v2.lean').read_text(encoding='utf8')
text = prior[:prior.index('example : S001')]
text += 'set_option pp.universes true\nset_option pp.all true\n'
text += '\n'.join('#print '+n for n in ['S002','Q002','S003','Q003','C0','C1','C2','meanPredict'])+'\n'
write(RUN/'neutral-type-diagnosis-v3.lean',text)
gate('neutral-type-diagnosis-v3','lake','env','lean',RUN/'neutral-type-diagnosis-v3.lean')
