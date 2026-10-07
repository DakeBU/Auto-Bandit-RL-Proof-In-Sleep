from common_v1 import *
fixed()
write(RUN/'preparation-schema-repair-v2.json',dict(failure='prepare-source-review-v1.py assumed flat input_sha256/report_sha256 and repository-relative paths; actual neutral-decoder receipt uses nested input/report objects with sha256_raw_bytes and run-relative basenames',actual_command=['python','-B','-X','utf8','runs/online-log-lower-20261008/prepare-source-review-v1.py'],actual_exit_code=1,actual_error="KeyError: 'input_sha256'",evidence='Actual functions.exec exec_command response; record is a failure description, not a verbatim full-stdout capture or a passed compiler receipt',repair='Read actual nested raw-byte fields and resolve only explicit run-relative basenames; every input/report/row rehashed; preserve original receipt/report/preparation helper unchanged',source_and_all16_terminal_headers_unchanged=True,mathematical_proof_not_attempted=True,source_package_accepted=False,chapter_complete=False,goal_complete=False))
text=(RUN/'prepare-source-review-v1.py').read_text(encoding='utf-8')
old="assert r['input_sha256']==sha(RUN/'neutral-packet-v1.lean') and sha(r['report'])==r['report_sha256']\nfor row in r['reviewed_files']:assert sha(row['path'])==row['sha256'],row['path']"
new="""def resolved(p):
 p=Path(p);return RUN/p if len(p.parts)==1 else p
report_sha=r['report']['sha256_raw_bytes']
assert r['input']['sha256_raw_bytes']==sha(RUN/'neutral-packet-v1.lean')
assert sha(resolved(r['report']['path']))==report_sha
assert sha(resolved(r['input_manifest']['path']))==r['input_manifest']['sha256_raw_bytes']
for row in r['reviewed_files']:assert sha(resolved(row['path']))==row['sha256_raw_bytes'],row['path']"""
assert text.count(old)==1
text=text.replace(old,new).replace("report_sha256=r['report_sha256']","report_sha256=report_sha")
write(RUN/'prepare-source-review-v2.py',text)
native('preparation-schema-repair-event-v2','lifecycle-event','--session',TASK,'--event','repair','--payload-json',json.dumps(dict(scope='Neutral receipt field/path adaptation only',record=(RUN/'preparation-schema-repair-v2.json').as_posix(),source_contract_version=1,source_and_terminals_unchanged=True,chapter_complete=False,goal_complete=False)))
gate('prepare-source-review-v2',sys.executable,'-B','-X','utf8',RUN/'prepare-source-review-v2.py')
fixed()
