from publication_guard_v3 import *
fixed()
delivery=ROOT/'tmp/online-ch2-prescient-delivery-v3'
actual=load(delivery/'inspected.json')
assert actual['actual_head']=='f6749377f4deb541a0ca5e54b50cc9f4456040fb'
assert actual['actual_remote_head']==actual['actual_head'] and actual['actual_clean']
assert actual['PR']['number']==205 and actual['PR']['state']=='OPEN' and actual['PR']['isDraft'] and actual['PR']['mergedAt'] is None
attach=load(RUN/'official-PR205-attachment-v1.json')
assert not attach['result'].get('isError') and attach['PR']==actual['PR']['url']
copied=[]
for p in sorted(delivery.glob('*.json')):
    target=RUN/('actual-delivery-v3-'+p.name)
    write(target,p.read_bytes());copied.append(dict(original=p.as_posix(),durable=target.as_posix(),sha256=sha(p)))
write(RUN/'actual-delivery-summary-v1.json',dict(actual=actual,official_attachment=rows([RUN/'official-PR205-attachment-v1.json']),copied=copied,distinct_delivery_review='pending',math_changed=False,site_rebuilt_at_delivery_head=False,chapter_complete=False,whole_Goal_status='ACTIVE'))
paths=[ROOT/p for p in subprocess.check_output(['git','ls-files'],encoding='utf8').splitlines()]
paths+=list(RUN.glob('*'))
paths=[p for p in paths if p.is_file()]
write(RUN/'actual-delivery-review-inputs-v1.json',dict(rows=rows(paths),parent=BASE,delivered_head=actual['actual_head'],allowed_new_review_files=['actual-delivery-review-v1.md','actual-delivery-review-v1.json'],no_existing_raw_changes=True))
print('Actual delivery receipts copied exactly; frozen review inputs:',len(set(paths)))
