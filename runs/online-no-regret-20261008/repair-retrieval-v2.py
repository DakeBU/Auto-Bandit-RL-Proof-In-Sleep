from common_v1 import *
fixed()
assert load(RUN/'retrieval-actual-type-check-v1-exit.json')['exit_code']==1
write(RUN/'retrieval-api-check-v2.lean',(RUN/'retrieval-api-check-v1.lean').read_text(encoding='utf8').replace('#check Tendsto.unique\n',''))
write(RUN/'retrieval-repair-v2.json',dict(failed='retrieval-actual-type-check-v1',missing_name='Filter.Tendsto.unique',actual_present_compatible_API='tendsto_nhds_unique',repair='Drop the nonexistent extra check in a versioned retrieval file; use the actual already printed uniqueness theorem. All public headers/source/context unchanged; initial DAG dependency spelling superseded, not silently promoted.',source_statement_fingerprint_unchanged=True))
dag=load(CONTRACT/'initial-DAG-v1.json');dag['import_ready']=[x.replace('Tendsto.unique','tendsto_nhds_unique') for x in dag['import_ready']];dag['supersedes']='initial-DAG-v1.json: retrieval name only; mathematical interfaces unchanged';write(CONTRACT/'initial-DAG-v2.json',dag)
write(RUN/'20_architect-API-repair-v2.md','Actual pinned API check rejects Filter.Tendsto.unique but prints compatible tendsto_nhds_unique. Preserve old draft and failure; initial-DAG-v2 replaces only this dependency name. No theorem signature, source, conclusion or proof route changed.\n')
gate('retrieval-actual-type-check-v2','lake','env','lean',RUN/'retrieval-api-check-v2.lean')
s=(RUN/'retrieve-actual-types-v1.py').read_text(encoding='utf8');exec(compile(s[s.index("write(RUN/'source-pixel-review-v1.json'"):],'retrieve-actual-types-v1-pixel-tail','exec'))
fixed()
