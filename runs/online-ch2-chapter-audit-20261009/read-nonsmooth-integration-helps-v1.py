from lower_common_v1 import *

reviewed(); headers(3)
for label,args in [
    ('nonsmooth-contributor-help-v1',[sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--help']),
    ('nonsmooth-sitebuild-help-v1',[sys.executable,'-B','-X','utf8','website/scripts/build_site.py','--help']),
    ('nonsmooth-sitecheck-help-v1',[sys.executable,'-B','-X','utf8','website/scripts/check_site.py','--help'])]:
    capture(label,*args)
reviewed(); headers(3)
print('Existing contributor/site command help captured; no canonical mutation or premature Lean-verified site build.')
