"""Prepare four-card actual viewport renderer and scoped publication tools before use."""
from common_v2 import *
fixed(True,True);passed('integrate-reader-v1-01')
old=Path('runs/online-convex-nondifferentiability-20261007')
text=(old/'browser-v3.py').read_text(encoding='utf-8').replace('online-convex-nondifferentiability','online-convex-uncountability').replace('-v3','-v1')
compile(text,str(RUN/'browser-v1.py'),'exec');write(RUN/'browser-v1.py',text)
text=(old/'render-source-card-v4.cjs').read_text(encoding='utf-8').replace('length>=3','length>=4').replace('count()!==3','count()!==4').replace('exactly THREE','exactly FOUR').replace('i<3','i<4').replace('actual-three-source-cards-visible-and-rendered','actual-four-source-cards-visible-and-rendered').replace('-v3','-v1')
write(RUN/'render-source-card-v1.cjs',text)
text=(old/'render-source-card-v4.py').read_text(encoding='utf-8').replace('from common_v4','from common_v2').replace('online-convex-nondifferentiability','online-convex-uncountability').replace('render-source-card-v4.cjs','render-source-card-v1.cjs').replace("len(rendered['cards'])==3","len(rendered['cards'])==4").replace('actual-three-source-cards-rendered-awaiting-pixel-review','actual-four-source-cards-rendered-awaiting-pixel-review').replace('for i in [1,2,3]','for i in [1,2,3,4]').replace('THREE actual source cards','FOUR actual source cards').replace('-v3','-v1')
compile(text,str(RUN/'render-source-card-v1.py'),'exec');write(RUN/'render-source-card-v1.py',text)
text=(old/'check-scoped-diff-v2.py').read_text(encoding='utf-8').replace('from common_v4','from common_v2')
write(RUN/'check-scoped-diff-v1.py',text)
paths=[PUBLIC.as_posix(),CANARY.as_posix(),'BanditRLProof.lean','Tests.lean','MANIFEST.md','runs/lifecycle_sessions.jsonl','runs/trials.jsonl',RUN.relative_to(ROOT).as_posix(),CONTRACT.as_posix(),'tasks/'+TASK+'.md','conversion-windows/'+TASK+'.md','proof-obligations/'+TASK+'.md','research-wiki/contribution-contracts/online-convex-uncountability-20261007.json','website/content/readings.json','website/content/highlights.json','website/content/chapters.json']
write(RUN/'owned-commit-paths-v1.json',paths)
write(RUN/'commit-owned-v1.py',"import subprocess,sys,json\nfrom pathlib import Path\npaths=json.loads((Path(__file__).resolve().parent/'owned-commit-paths-v1.json').read_text(encoding='utf-8'))\nassert subprocess.check_output(['git','branch','--show-current'],text=True).strip()=='codex/research-online-convex-uncountability'\nfor cmd in [['git','add','--',*paths],['git','commit','-m',sys.argv[1]]]:\n p=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)\n if p.returncode:print(p.stdout.decode('utf-8',errors='replace'));sys.exit(p.returncode)\nprint(subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())\n")
write(RUN/'site-adapters-before-first-use-v1.json',dict(rows=[dict(path=p.as_posix(),sha256=sha(p)) for p in [RUN/'browser-v1.py',RUN/'render-source-card-v1.cjs',RUN/'render-source-card-v1.py',RUN/'check-scoped-diff-v1.py',RUN/'commit-owned-v1.py']],inherited_actual_viewport_guard=True,four_cards_after_actual_disclosure_open=True,private_runtime_profiles_preserved=True,generated_site_not_hand_edited=True))
print('Four-card viewport renderer and explicit owned-path commit/scoped-diff adapters prepared before use.')
