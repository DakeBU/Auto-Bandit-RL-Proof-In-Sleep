from publication_guard_v1 import *
fixed()
old=(ROOT/'runs/online-ch2-proximal-20261009/capture-proximal-reader-v1.cjs').read_text(encoding='utf8')
old=old.replace('nodes.length!==1','nodes.length!==6').replace('Missing one new public node','Missing six new public nodes').replace('proximal-source-card-v1.png','bregman-source-card-v1.png').replace('actual-real-convex-minimizer-comparison-captured','actual-bregman-proximal-foundation-captured')
write(RUN/'capture-bregman-reader-v1.cjs',old)
d=load(CONTRACT/'stabilized-v1.json')
write(RUN/'browser-production-nodes-v1.json',dict(targets=[dict(declaration=d['definition']['declaration'])]+[dict(declaration=t['declaration']) for t in d['targets']],canonical_nodes=6,proofs=5,definition=1))
write(RUN/'browser-transport-boundary-v1.json',dict(transport='Blocking real Edge browser file URI visit to new isolated generated site, not HTTP/live.',prior_policy_hold='Prior PR208 attempt to start new hidden local HTTP service port62430 was rejected before execution with blocked-by-policy reason. Do not retry service/listener through another helper.',new_HTTP_service_attempted=False,old_62429_service_preserved=True,new_browser_profile='tmp/online-ch2-bregman-browser-v1/capture-profile',no_all_viewports_claim=True))
fixed()
