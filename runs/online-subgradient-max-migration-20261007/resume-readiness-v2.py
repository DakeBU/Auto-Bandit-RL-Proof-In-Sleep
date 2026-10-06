from common_v2 import *
fixed();passed('retained-focused-v1-01');passed('actual-types-v1-01');old=RUN/'leaves/pinned-APIs-v1.lean';text=old.read_text(encoding='utf-8')
for n in ['frequently_exists','eventually_all','frequently_iff_neBot']:
 assert '#check @'+n in text;text=text.replace('#check @'+n,'#check @Filter.'+n)
new=RUN/'leaves/pinned-APIs-v2.lean';write(new,text)
write(RUN/'readiness-API-repair-v2.json',dict(failed_attempt='pinned-APIs-v1-01',failed_log_sha256=sha(RUN/'pinned-APIs-v1-01.log'),failed_exit=load(RUN/'pinned-APIs-v1-01-exit.json'),failure_class='Lean API probe namespace lookup, not producer-body failure',exact_failed_names=['frequently_exists','eventually_all','frequently_iff_neBot'],actual_retrieval_files=['.lake/packages/mathlib/Mathlib/Order/Filter/Basic.lean','.lake/packages/mathlib/Mathlib/Order/Filter/Finite.lean'],cause='Probe omitted Filter namespace opened in unchanged real producer module.',repair='Use exact qualified Filter names; preserve v1 probe/raw failed output and rerun only pending readiness gates.',statement_definition_proof_or_canary_changed=False,terminal_weakened=False,focused_and_actualtypes_passed=True))
generated('readiness-repair-generated-before-use-v2.json',[new,RUN/'leaves/export-ready-dependencies-v1.lean'])
gate('pinned-APIs-v2-01','lake','env','lean',new)
gate('compiled-ready-graph-v1-01','lake','env','lean','--run',RUN/'leaves/export-ready-dependencies-v1.lean',RUN/'compiled-ready-graph-v1.json')
for command in ['statement-fence','retrieval-record','lifecycle-event','list-lean-decls','search-memory']:
 native(command+'-help-v1-01',command,'--help')
fixed();print('All20 pinned API checks passed with actual Filter qualifications; compiled19node readiness export passed; earlier failed probe preserved without mathematical change.')
