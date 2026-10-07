from common_v1 import *
fixed()
write(RUN/'contract-preparation-failure-v1.json',dict(command=['python','-B','-X','utf8','runs/online-ftl-state-20261007/prepare-contract-v1.py'],exit_code=1,actual_tool_output="Traceback (most recent call last):\n  File \"runs/online-ftl-state-20261007/prepare-contract-v1.py\", line 106, in <module>\n    for row in ledger['items']:\nKeyError: 'items'\n",cause='Inherited ledger schema uses maintext_items, not guessed items',repair='Versioned continuation uses actual key maintext_items; all already-created raw contracts/headers preserved',mathematical_target_change=False))
text=(RUN/'prepare-contract-v1.py').read_text(encoding='utf-8');tail=text[text.index("ledger=load("):]
assert tail.count("ledger['items']")==1
prefix="""from common_v1 import *
fixed()
defs=load(CONTRACT/'production-definitions-v1.json')
new=load(CONTRACT/'new-public-headers-v1.json')
tests=load(CONTRACT/'planned-canary-headers-v1.json')
testdef=load(CONTRACT/'test-definition-v1.json')['probeTargets']
old=load(CONTRACT/'existing-Mean-headers-v1.json')
contract=(CONTRACT/'contract-v1.md').read_text(encoding='utf-8')
"""
write(RUN/'continue-contract-v2.py',prefix+tail.replace("ledger['items']","ledger['maintext_items']"))
write(RUN/'contract-schema-repair-v2.json',dict(original_failure_sha256=sha(RUN/'contract-preparation-failure-v1.json'),actual_schema_key='maintext_items',versioned_continuation_sha256=sha(RUN/'continue-contract-v2.py'),all_prior_created_contract_bytes_retained=True,source_or_statement_change=False))
native('draft-metadata-repair-v2','lifecycle-event','--session',TASK,'--event','repair','--payload-json',json.dumps(dict(run_id=RUN.name,contract_version=1,metadata_repair=(RUN/'contract-schema-repair-v2.json').as_posix(),mathematical_targets_unchanged=True)))
