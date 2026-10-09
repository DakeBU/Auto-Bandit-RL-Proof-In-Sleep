from publication_guard_v1 import *
fixed()
p=ROOT/'website/content/readings.json'
raw=p.read_bytes();before=load(p)
reading=next(x for x in before['readings'] if x['slug']=='online-ogd')
card=reading['source_theorems'][-1]
assert card==load(RUN/'reader-proposal-v1.json')['card']
old=card['local_status']['label']
new='Real comparison and concrete instances compiled; general source open'
assert old=='Real comparison and concrete instances compiled; package gates pending'
assert raw.count(old.encode('utf8'))==1
after=raw.replace(old.encode('utf8'),new.encode('utf8'))
write(RUN/'publication-status-before-v2.raw',raw)
write(RUN/'publication-status-after-v2.raw',after)
eof=[]
for q in RUN.glob('*.md'):
    if q.read_bytes().replace(b'\r\n',b'\n').endswith(b'\n\n'):
        eof.append(dict(path=q.as_posix(),sha256=sha(q)))
write(RUN/'publication-status-proposal-v2.json',dict(path=p.as_posix(),before_sha256=sha(p),after_sha256=hashlib.sha256(after).hexdigest(),before_snapshot=(RUN/'publication-status-before-v2.raw').as_posix(),after_snapshot=(RUN/'publication-status-after-v2.raw').as_posix(),old_label=old,new_label=new,only_one_card_status_label=True,source_statement_proof_boundaries_unchanged=True,proposed_immutable_received_report_EOF_exceptions=eof,scope='Exact transient status label clarification only. Do not modify received semantic decoder reports. No code/Test/reader formula exemption; actual full/scoped diff inspection still required.',chapter_complete=False,whole_Goal_status='ACTIVE'))
write(RUN/'publication-status-review-inputs-v2.json',dict(rows=rows([p,PUBLIC,CANARY,RUN/'publication-status-proposal-v2.json',RUN/'publication-status-before-v2.raw',RUN/'publication-status-after-v2.raw',RUN/'canary-BODY-publication-review-v2.md',RUN/'canary-BODY-publication-review-v2.json',CONTRACT/'exact-publication-plan-v1.json',*[Path(r['path']) for r in eof]]),materialization_pending=True))
print('Exact one-label proposal and immutable EOF candidates ready',len(eof))
