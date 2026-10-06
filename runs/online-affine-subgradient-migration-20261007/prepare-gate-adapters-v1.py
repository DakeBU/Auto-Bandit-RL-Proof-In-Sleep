"""Prepare scoped actual gate adapters; preserve unused reader v1 before R4 clarification."""
from common_v2 import *
old=Path('runs/online-hinge-migration-20261007')
p=RUN/'integrate-reader-v1.py';text=p.read_text(encoding='utf-8')
before='Borrowed SourceProper is on arbitrary carriers, SourceSubdifferential uses intrinsic norm/inner with no finite-dimension requirement. Borrowed D/Q use arbitrary carriers and C uses AddCommGroup/Module real; none are newly owned definitions.'
after='TWO production borrowed contexts are SourceProper (arbitrary carrier) and SourceSubdifferential (intrinsic norm/inner, no finite dimension). THREE supplementary CANARY borrowed contexts are effectiveDomain/realEpigraph (arbitrary carriers) and IsConvexExtended (AddCommGroup/Module real). All FIVE are shared borrowed definitions, none newly owned.'
assert before in text;write(RUN/'integrate-reader-v2.py',text.replace(before,after))
write(RUN/'reader-pre-use-clarification-v2.json',dict(original=p.as_posix(),original_sha256=sha(p),original_unused=True,new_path=(RUN/'integrate-reader-v2.py').as_posix(),required_reader='CONTRACT R4 full names/two production versus three supplementary canary contexts; added before any reader helper execution',source_or_statement_change=False,actual_failed_reader_attempt=False))
t=(old/'verify-history-bindings-v1.py').read_text(encoding='utf-8')
t=t.replace('hrun=Path(__file__).parent;',"arun=Path(__file__).parent;hrun=Path('runs/online-hinge-migration-20261007');")
t=t.replace("str(hrun/'historical-raw-supersession-body-v1.json')]:","str(hrun/'historical-raw-supersession-body-v1.json'),str(hrun/'historical-raw-supersession-final-v1.json'),str(arun/'historical-raw-supersession-v1.json'),str(arun/'historical-raw-supersession-contract-v1.json'),str(arun/'historical-raw-supersession-body-v1.json')]:")
t=t.replace("receipts=[hrun/", "receipts=[arun/'source-contract-receipt-v1.json',arun/'public-body-receipt-v1.json',hrun/'final-reader-receipt-v1.json',hrun/")
t=t.replace("load(hrun/'historical-raw-supersession-v1.json')","load(arun/'historical-raw-supersession-v1.json')")
t=t.replace("out=hrun/","out=arun/").replace("'online-hinge'","'online-affine-subgradient'").replace('only_online_hinge_subtree_changed','only_online_affine_subgradient_subtree_changed').replace('selected Example2.27 hinge subtree only','selected Theorem2.28 affine subtree only')
assert "hrun=Path('runs/online-hinge-migration-20261007')" in t and 'out=arun/' in t
write(RUN/'verify-history-bindings-v1.py',t)
t=(old/'commit-owned-v1.py').read_text(encoding='utf-8').replace('OnlineHinge','OnlineAffineSubgradient').replace('online-hinge','online-affine-subgradient').replace('ONLINE-HINGE','ONLINE-AFFINE-SUBGRADIENT');write(RUN/'commit-owned-v1.py',t)
t=(old/'check-scoped-diff-v1.py').read_text(encoding='utf-8').replace(BASE,BASE).replace('8375aa0353a4230ec23c0ccbb8f337a16246c134',BASE).replace('manifest-before-hinge-entry','manifest-before-affine-entry');write(RUN/'check-scoped-diff-v1.py',t)
for name in ['browser-v1.py','render-source-card-v1.py','prepare-site-CLI-v1.py']:
 t=(old/name).read_text(encoding='utf-8').replace('online-hinge-migration','online-affine-subgradient-migration').replace('online-hinge','online-affine-subgradient').replace('OnlineHinge','OnlineAffineSubgradient');write(RUN/name,t)
helpers=[RUN/n for n in ['integrate-reader-v2.py','verify-history-bindings-v1.py','commit-owned-v1.py','check-scoped-diff-v1.py','browser-v1.py','render-source-card-v1.py','prepare-site-CLI-v1.py','project-gates-v1.py']]
for p in helpers:compile(p.read_text(encoding='utf-8'),str(p),'exec')
generated('current-gate-adapters-before-use-v1.json',helpers)
print('Actual scoped historical/source/site helpers prepared; original unusedreader preserved with R4 clarification.')
