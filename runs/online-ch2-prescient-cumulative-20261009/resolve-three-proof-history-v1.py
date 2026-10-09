from common import *
fixed()
old_rows=load(RUN/'first-leaf-BODY-review-inputs-v1.json')['rows']
changes=[]
for r in old_rows:
    p=Path(r['path'])
    if sha(p)==r['sha256']: continue
    if p==PUBLIC:
        b=(RUN/'pre-fixed-public-v1.lean').read_bytes()
        assert hashlib.sha256(b).hexdigest()==r['sha256']
        assert PUBLIC.read_bytes().startswith(b[:-len('end BanditRL.OnlinePrescientBregman\n'.encode())])
        changes.append(dict(path=p.as_posix(),before_sha256=r['sha256'],after_sha256=sha(p),exact_before_snapshot='pre-fixed-public-v1.lean',permitted_change='append only reviewed frozen fixed/variable sharp bodies; previous complete first proof prefix preserved'))
    elif p==RUN/'lifecycle-sessions.jsonl':
        lines=p.read_bytes().splitlines(keepends=True)
        options=[b''.join(lines[:k]) for k in range(1,len(lines)+1)]
        matches=[b for b in options if hashlib.sha256(b).hexdigest()==r['sha256']]
        assert len(matches)==1
        write(RUN/'recovered-first-BODY-native-sessions-v1.raw',matches[0])
        changes.append(dict(path=p.as_posix(),before_sha256=r['sha256'],after_sha256=sha(p),exact_before_snapshot='recovered-first-BODY-native-sessions-v1.raw',snapshot_provenance='Exact actual append-only prefix recovered now and validated against original pre-proof reviewer input hash; not a freshly captured before-event snapshot.'))
    elif p==RUN/'lifecycle-state.json':
        prior=next(x for x in load(RUN/'pre-first-compiled-native-exact-v2.json')['rows'] if x['path']==p.as_posix())
        state=json.loads(base64.b64decode(prior['raw_base64']).decode('utf8'))
        event=json.loads(base64.b64decode(load(RUN/'native-first-focused-compiled-event-v2.json')['stdout_base64']).decode('utf8'))
        assert state['next_sequence']==event['sequence'] and state['current_entry_id']==event['parent_id']
        state.update(next_sequence=event['sequence']+1,current_entry_id=event['entry_id'])
        s=json.dumps(state,ensure_ascii=False,indent=2)+'\n'
        candidates=[s.encode('utf8'),s.replace('\n','\r\n').encode('utf8')]
        matches=[b for b in candidates if hashlib.sha256(b).hexdigest()==r['sha256']]
        assert len(matches)==1
        write(RUN/'recovered-first-BODY-native-state-v1.raw',matches[0])
        changes.append(dict(path=p.as_posix(),before_sha256=r['sha256'],after_sha256=sha(p),exact_before_snapshot='recovered-first-BODY-native-state-v1.raw',snapshot_provenance='Exact prior state recovered from actual earlier raw snapshot plus actual successful native event and validated against original reviewer input hash; not a contemporaneous pre-fixed event capture.'))
    else: raise AssertionError(('Unpermitted prior review mutation',p))
assert len(changes)==3
write(RUN/'three-proof-historical-binding-resolution-v1.json',dict(changes=changes,metadata_provenance_limitation='Before fixed/variable native events an extra immediate raw state snapshot was not captured. Exact prior hashes/prefix/event reconstruction recover the original reviewed bytes; this limitation is explicit for distinct reviewer. Future phases must snapshot current mutable native bytes before events.',all_other_first_BODY_inputs_unchanged=True,first_BODY_review_sha256=sha(RUN/'first-leaf-BODY-review-v1.json'),whole_Goal_status='ACTIVE'))
write(RUN/'pre-next-phase-native-exact-v1.json',dict(rows=[dict(path=p.as_posix(),sha256=sha(p),raw_base64=base64.b64encode(p.read_bytes()).decode('ascii')) for p in [RUN/'lifecycle-sessions.jsonl',RUN/'lifecycle-state.json',RUN/'trials.jsonl',RUN/'own-artifact-journal.md'] if p.exists()]))
write(RUN/'three-BODY-and-canary-contract-inputs-v1.json',dict(rows=rows(list(CONTRACT.glob('*'))+[PUBLIC]+[p for p in RUN.glob('*') if p.is_file()]),scope='Three production BODYs + two exact canary CONTRACTS only; remaining printed bodies and canary bodies absent',whole_Goal_status='ACTIVE'))
fixed()
print('Exact authorized historical bindings resolved with explicit provenance limitation; combined3BODY/2canaryCONTRACT current inputs pinned.')
