from common_v1 import *
fixed()
gate('focused-existing-public-v1','lake','build','BanditRLProof.OnlineLearningRegret')
names=['comparatorRegret','NoRegret',*load(CONTRACT/'existing-public-headers-v1.json')]
write(RUN/'leaves/existing-kernel-axioms-v1.lean','import BanditRLProof.OnlineLearningRegret\n'+'\n'.join('#check '+PRE+n+'\n#print axioms '+PRE+n for n in names))
gate('existing-kernel-axioms-v1','lake','env','lean',RUN/'leaves/existing-kernel-axioms-v1.lean')
log=(RUN/'existing-kernel-axioms-v1.log').read_text(encoding='utf-8')
assert 'sorryAx' not in log
matches=re.findall(r"(?:^|\n)'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",log)
assert len(matches)==4
axes={n:[a for a in re.sub(r'\s+','',s).split(',') if a] for n,s in matches}
assert all(set(a)<={'propext','Classical.choice','Quot.sound'} for a in axes.values())
write(RUN/'existing-kernel-audit-v1.json',dict(status='actual focused module build and4 named kernel axioms passed',source_module_sha256=sha(PUBLIC),axioms=axes,existing_math_unchanged=True,contract_source_acceptance=False,new_test_body_written=False,chapter_complete=False,goal_complete=False))
fixed()
