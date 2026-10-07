from common_v1 import *
fixed(integrated=True)
old_source=RUN/'snapshots/BanditRLProof--OnlineLearningRegret.lean.raw';text_copy=CONTRACT/'complete-existing-module-v1.lean.txt'
raw=old_source.read_bytes();text=text_copy.read_bytes()
assert sha(old_source)==load(RUN/'draft-freeze-v1.json')['fixed_files'][PUBLIC.as_posix()]
assert raw.replace(b'\r\n',b'\n')==text and raw.count(b'\r\n')==38 and text.count(b'\r\n')==0
write(RUN/'source-text-lineend-resolution-v4.json',dict(raw_original=dict(path=old_source.as_posix(),sha256=sha(old_source),bytes=len(raw),CRLF_lines=38),LF_text_copy=dict(path=text_copy.as_posix(),sha256=sha(text_copy),bytes=len(text),CRLF_lines=0),original_initializer='initialize-v1.py reads source via read_text and writes complete-existing-module as LF text; separate source snapshot preserves exact raw bytes',comparison='Exact LF-normalized text equality; every receipt still binds each file raw independently. Current public file exact approved doc insertion into original RAW snapshot remains enforced by fixed(integrated=True).',original_failed_verifier_log=dict(path=(RUN/'registry-check-v3.log').as_posix(),sha256=sha(RUN/'registry-check-v3.log')),no_source_or_target_change=True))
v=(RUN/'verify-registry-v3.py').read_text(encoding='utf-8')
old="assert Path('docs/contracts/online-regret-domains-v1/complete-existing-module-v1.lean.txt').read_bytes()==(RUN/'snapshots/BanditRLProof--OnlineLearningRegret.lean.raw').read_bytes()"
new="assert (RUN/'snapshots/BanditRLProof--OnlineLearningRegret.lean.raw').read_bytes().replace(b'\\r\\n',b'\\n')==Path('docs/contracts/online-regret-domains-v1/complete-existing-module-v1.lean.txt').read_bytes()\nassert sha(RUN/'snapshots/BanditRLProof--OnlineLearningRegret.lean.raw')==load(RUN/'draft-freeze-v1.json')['fixed_files'][PUBLIC.as_posix()]"
assert old in v
write(RUN/'verify-registry-v4.py',v.replace(old,new).replace("RUN/'registry-v3.json'","RUN/'registry-v4.json'"))
gate('registry-check-v4',sys.executable,'-B','-X','utf8',RUN/'verify-registry-v4.py')
capture=(RUN/'capture-reader-v1.py').read_text(encoding='utf-8').replace("RUN/'registry-v1.json'","RUN/'registry-v4.json'")
write(RUN/'capture-reader-v4.py',capture)
gate('current-reader-capture-v4',sys.executable,'-B','-X','utf8',RUN/'capture-reader-v4.py')
native('registry-verifier-candidate-event-v4','lifecycle-event','--session',TASK,'--event','candidate','--payload-json',json.dumps(dict(run_id=RUN.name,registry=(RUN/'registry-v4.json').as_posix(),source_lineend_resolution=(RUN/'source-text-lineend-resolution-v4.json').as_posix(),mathematical_target_changed=False,chapter_complete=False,goal_complete=False)))
fixed(integrated=True)
