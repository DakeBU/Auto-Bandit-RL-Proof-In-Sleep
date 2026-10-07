"""Bind the prospective body audit to the repaired stabilized contract."""
from common_v2 import *
fixed()
text=(RUN/'prepare-body-evidence-v1.py').read_text(encoding='utf-8').replace("passed('stabilize-v1-01')","passed('stabilize-v2-01')")
needle="headers=load(CONTRACT/'headers-v2.json')"
insert="""r=load(RUN/'source-contract-receipt-v2.json');assert sha(r['report'])==r['report_sha256']
for x in load(RUN/'contract-reviewed-bindings-v2.json')['rows']:assert sha(x['path'])==x['sha256'],x['path']
"""
assert needle in text;text=text.replace(needle,insert+needle)
write(RUN/'prepare-body-evidence-v2.py',text)
print('Version2 body adapter created before first body use; outputs v1 are prospective first-use labels, actual source contract2/context2/comparison3 required.')
