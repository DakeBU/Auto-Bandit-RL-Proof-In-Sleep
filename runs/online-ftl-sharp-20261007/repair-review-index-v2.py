from common_v1 import *
fixed()
old=load(RUN/'source-contract-inputs-v1.json');mismatch=[dict(path=x['path'],recorded=x['sha256'],actual=sha(x['path'])) for x in old['rows'] if x['sha256']!=sha(x['path'])]
assert len(mismatch)==1 and mismatch[0]['path'].endswith('/source-contract-preparation-v2.log'),mismatch
write(RUN/'review-index-self-log-repair-v2.json',dict(status='Pre-review input binding repaired; historical v1 index retained and not accepted',actual_mismatches=mismatch,reason='The v2 preparation parent gate opened a RUN log before the child froze all RUN files; its final stdout changed that one row afterward. Exit0 of preparation did not certify source review or immutable input binding.',repair='Freeze v2 index directly after the logging parent finished; no active own RUN capture is used around this preparation.',all_source_statement_canary_plan_decoder_bytes_unchanged=True,mathematical_contract_version=1,source_review_not_started=True))
packet=(RUN/'source-contract-packet-v1.md').read_text(encoding='utf-8').replace('source-contract-inputs-v1.json','source-contract-inputs-v2.json')
packet+='\nPre-review infrastructure repair: v1 input index has one stale enclosing-preparation-log row and is historical/unaccepted. Current v2 index is frozen directly after parent completion. Rehash every CURRENT v2 row; do not claim historical v1 row passes. No mathematical source/statement/decoder change, contract mathematics remains version1.\n'
write(RUN/'source-contract-packet-v2.md',packet)
paths=[x['path'] for x in old['rows']]
paths.extend(p.as_posix() for p in sorted(RUN.rglob('*')) if p.is_file())
paths=list(dict.fromkeys(paths))
write(RUN/'source-contract-inputs-v2.json',dict(stage='CONTRACT',version=1,binding_index_version=2,rows=[dict(path=p,sha256=sha(p)) for p in paths],fixed_input_count=len(paths),superseded_unaccepted_index='source-contract-inputs-v1.json',all_math_source_decoder_unchanged=True,actual_neutral_closed_Props=13,existing_public_exact_type_identities=5,new_actual_public_and_canary_proofs_pending=True,source_package_accepted=False,chapter_complete=False,goal_complete=False))
for x in load(RUN/'source-contract-inputs-v2.json')['rows']:assert sha(x['path'])==x['sha256']
fixed();print('CURRENT CONTRACT fixed rows',len(paths),'all actual raw hashes match; historical v1 self-log mismatch retained, source targets unchanged.')
