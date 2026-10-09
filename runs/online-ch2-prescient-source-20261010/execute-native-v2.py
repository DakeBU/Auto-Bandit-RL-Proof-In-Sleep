from publication_guard_v1 import *
fixed()
p=RUN/'native-metadata-repair-review-v2.json';r=load(p)
assert sha(p)=='03873b1d8c78a79132c03f36904fa3b8de90c42a23263748d9dee5ea4feb5792'
assert r['verdict']=='accepted-with-explicit-delta' and not r['required_repairs']
assert sha(r['report'])==r['report_sha256']
assert sha(r['input_manifest'])==r['input_manifest_sha256']
for row in load(r['input_manifest'])['rows']:assert sha(row['path'])==row['sha256']
write(RUN/'native-v2-caller-preflight.json',dict(review_sha256=sha(p),report_sha256=r['report_sha256'],input_manifest_sha256=r['input_manifest_sha256'],all_repair_rows_rehashed=True,external_caller_check=True,self_enforcement_claim=False))
capture('native-v2-command',sys.executable,'-B','-X','utf8',RUN/'record-native-acceptance-v2.py')
fixed()
print('Actual reviewed bounded native step completed; distinct postnative/delivery still pending.')
