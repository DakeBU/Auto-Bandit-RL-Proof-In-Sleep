from leaf_driver import *
import re
guard()
script=(RUN/'prepare-full-body-and-canary-v1.py').read_text(encoding='utf8')
exec(compile(script[:script.index("write(RUN/'FullPublicAuditV1.lean'")],str(RUN/'prepare-full-body-and-canary-v1.py')+':preflight','exec'))
prior=load(RUN/'full-public-axiom-v1.json')
code=prior['actual_exit'];out=base64.b64decode(prior['stdout_base64']).decode('utf8')
assert code==0 and 'sorryAx' not in out
matches=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",out,re.S)
assert {n for n,a in matches}=={row['name'] for row in targets.values()}
assert all(set(a.replace('\n',' ').split(', '))=={'propext','Classical.choice','Quot.sound'} for n,a in matches)
lines=[n+': '+', '.join(a.replace('\n',' ').split()) for n,a in matches]
write(RUN/'full-public-audit-wrapper-repair-v2.json',dict(actual_Lean_exit=code,prior_wrapper_failure='Exact line ending parser did not account for prettyprinter linewrap in the longer scalar identity axiom name',repair='Parse full bracketed axiom lists across linewrap from the retained successful Lean receipt; require all11 exact names and only standard axiom set',axioms=matches,production_unchanged=True,compiler_rerun=False))
exec(compile(script[script.index("write(RUN/'full-public-inspected-v1.json'"):],str(RUN/'prepare-full-body-and-canary-v1.py')+':unexecuted-tail','exec'))
