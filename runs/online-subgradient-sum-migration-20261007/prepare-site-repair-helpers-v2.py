"""Keep failed site evidence immutable and prepare fresh metadata/site verification."""
from pathlib import Path
import hashlib,json
run=Path(__file__).parent
def write(n,t):
 p=run/n;assert not p.exists(),p;p.write_bytes(t.encode())
t=(run/'verify-registry-v1.py').read_text(encoding='utf-8')
t=t.replace('retained differentiability nodes','retained sum-rule nodes').replace('online-subgradient-sum-migration-site-v1','online-subgradient-sum-migration-site-v2').replace("p=run/'registry-v1.json'","p=run/'registry-v2.json'")
write('verify-registry-v2.py',t)
t=(run/'browser-v1.py').read_text(encoding='utf-8').replace('online-subgradient-sum-migration-site-v1','online-subgradient-sum-migration-site-v2').replace('browser-v1','browser-v2').replace('reader-v1.png','reader-v2.png')
write('browser-v2.py',t)
t=(run/'verify-history-bindings-v1.py').read_text(encoding='utf-8').replace("run/'history-binding-audit-v1.json'","run/'history-binding-audit-v2.json'")
write('verify-history-bindings-v2.py',t)
t=(run/'check-scoped-diff-v1.py').read_text(encoding='utf-8').replace("'/leaves/reader-before-site-route-repair-v2.' in p","'/leaves/reader-before-site-route-repair-v2.' in p or '/leaves/reader-before-primer-repair-' in p")
write('check-scoped-diff-v2.py',t)
t=(run/'prepare-final-reader-v1.py').read_text(encoding='utf-8')
for a,b in [('site-v1','site-v2'),('fullharness-v1-01','fullharness-v2-01'),('contributor-exact-v1-01','contributor-exact-v2-01'),('scoped-diff-v1-01','scoped-diff-v2-01'),('site-build-v1-01','site-build-v2-01'),('site-check-v1-01','site-check-v2-01'),('registry-v1-01','registry-v2-01'),('browser-v1-01','browser-v2-01'),('history-bindings-v1-01','history-bindings-v2-01'),("run/'registry-v1.json'","run/'registry-v2.json'"),("run/'history-binding-audit-v1.json'","run/'history-binding-audit-v2.json'"),('reader-v1.png','reader-v2.png')]:t=t.replace(a,b)
t=t.replace("Existing nonblocking linters retained.","Actual site-check-v1 failed because notation primer requires exactlythree entries. Reader-only repair-v2 merges fourth space entry into first M entry preservingALLfour meanings and originalfour routes; mathematics/generator/checker fixed. Failedsitev1 and its viewed PNG retained; freshfullharness-v2/sitebuild-v2/sitecheck-v2/currentregistry/browser/history independently required. Existing nonblocking linters retained.")
t=t.replace('no site route repair asserted','no curated-route repair asserted; actual notation-primer repair separately recorded')
t=t.replace('Eleven reader requirements:', 'Verify reader-primer-repair-v2.json/before raw snapshot and current three notation entries: ALL four original meanings retained, original four curated links/math unchanged, actual failedcheck rawlog preserved. Current v2 metadata/site artifacts supersede v1 additively; old firstviewport/sourcecommit evidence not rewritten. Eleven reader requirements:')
write('prepare-final-reader-v2.py',t)
t=(run/'prepare-pr-payload-v1.py').read_text(encoding='utf-8').replace('Preparation failures and unused versions retained; no mathematical repair hidden.','Actual first sitecheck failed its exactly-three notation-primer rule. Reader metadata merges the fourth space entry into the existing M entry, retaining all four meanings and original four curated links; mathematics/generator/checker unchanged. Fresh fullharness/sitebuild/sitecheck v2 passed. Raw failure/old site/sourcecommit/screenshot and preparation/unused versions retained; no mathematical repair hidden.')
t=t.replace("run/'registry-v1.json'","run/'registry-v2.json'")
write('prepare-pr-payload-v2.py',t)
t=(run/'prepare-delivery-v1.py').read_text(encoding='utf-8').replace("run/'registry-v1.json'","run/'registry-v2.json'").replace("'registry-v1.json'","'registry-v2.json'")
t=t.replace('Count/path/CLI/helper preparation diagnostics,','Actual firstsitecheck failed exactly-three notation-primer rule; reader-onlyv2 merges space entry into existing M entry retainingALLfour meanings, originalfourcuratedroutes and unchangedmathematics/generator/checker. Freshfullharness/site v2 passed; oldfailure/site/PNG preserved. Count/path/CLI/helper preparation diagnostics,')
write('prepare-delivery-v2.py',t)
files=['verify-registry-v2.py','browser-v2.py','verify-history-bindings-v2.py','check-scoped-diff-v2.py','prepare-final-reader-v2.py','prepare-pr-payload-v2.py','prepare-delivery-v2.py']
write('site-repair-helpers-before-use-v2.json',json.dumps(dict(rows=[dict(path=(run/n).as_posix(),sha256=hashlib.sha256((run/n).read_bytes()).hexdigest()) for n in files],before_first_use=True,v1_files_preserved=True,reader_only_repair=True,mathematics_changed=False),indent=2)+'\n')
print('Failed v1 site/reader evidence retained; v2 helpers prepared and bound before use. New gates pending.')
