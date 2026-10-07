from common_v1 import *
fixed(proving=True);assert load(RUN/'all-exact-types-v1-exit.json')['exit_code']==1
write(RUN/'exact-type-verification-repair-v2.json',dict(failed_gate_sha256=sha(RUN/'all-exact-types-v1-exit.json'),failed_log_sha256=sha(RUN/'all-exact-types-v1.log'),cause='rw closes some proposition identity goals automatically, so following unconditional rfl reports No goals to be solved',repair='Keep exact target propositions and proved whole-function state identity; apply rfl only to remaining goals',all_public_definitions_statements_and_bodies_unchanged=True,all24_named_kernel_axioms_already_passed=True))
text=(RUN/'leaves/all-exact-types-v1.lean').read_text(encoding='utf-8')
bad='  try rw [neutralStateIdentity]\n  rfl\n';assert text.count(bad)==19
write(RUN/'leaves/all-exact-types-v2.lean',text.replace(bad,'  try rw [neutralStateIdentity]\n  all_goals rfl\n'))
gate('all-exact-types-v2','lake','env','lean',RUN/'leaves/all-exact-types-v2.lean')
original=(RUN/'check-bodies-v1.py').read_text(encoding='utf-8');tail=original[original.index('template=Path('):]
prefix='''from common_v1 import *
fixed(proving=True)
old=load(CONTRACT/'existing-Mean-headers-v1.json');new=load(CONTRACT/'new-public-headers-v1.json');tests=load(CONTRACT/'planned-canary-headers-v1.json');defs=load(CONTRACT/'production-definitions-v1.json')
proofnames=[PRE+n for n in [*old,*new]]+[TEST+n for n in tests]
names=proofnames+[PRE+'empiricalMean']+[PRE+n for n in defs]+[TEST+'probeTargets']
axes=(RUN/'all-axioms-v1.log').read_text(encoding='utf-8')
matched=re.findall(r"(?:^|\\n)'([^']+)' (?:depends on axioms: \\[([^\\]]*)\\]|does not depend on any axioms)",axes)
assert len(matched)==24
axioms={n:[a for a in re.sub(r'\\s+','',s).split(',') if a] for n,s in matched}
assert load(RUN/'all-exact-types-v2-exit.json')['exit_code']==0
'''
write(RUN/'continue-body-checks-v2.py',prefix+tail)
fixed(proving=True)
