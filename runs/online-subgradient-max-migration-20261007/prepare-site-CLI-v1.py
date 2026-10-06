from common_v2 import *
for label,args in [('contributor-help-v1-01',[sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--help']),('site-build-help-v1-01',[sys.executable,'-B','-X','utf8','website/scripts/build_site.py','--help']),('site-check-help-v1-01',[sys.executable,'-B','-X','utf8','website/scripts/check_site.py','--help'])]:gate(label,*args)
fixed(True)
print('Actual contributor/site CLI help recorded; no site generation before current integrated Lean gates.')
