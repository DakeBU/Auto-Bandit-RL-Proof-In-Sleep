"""Before first use, adapt actual one-card template to both current source cards."""
from common_v2 import *
p=RUN/'render-source-card-v1.py';t=p.read_text(encoding='utf-8')
assert "len(rendered['cards'])==1 and rendered['cards'][0]['mathContainers']==1 and rendered['cards'][0]['mathErrors']==0" in t
t=t.replace("len(rendered['cards'])==1 and rendered['cards'][0]['mathContainers']==1 and rendered['cards'][0]['mathErrors']==0", "len(rendered['cards'])==2 and all(c['mathContainers']==1 and c['mathErrors']==0 for c in rendered['cards'])")
t=t.replace("images=[dict(path=(RUN/'source-card-01-v1.png').as_posix(),sha256=sha(RUN/'source-card-01-v1.png'))]", "images=[dict(path=(RUN/('source-card-%02d-v1.png'%i)).as_posix(),sha256=sha(RUN/('source-card-%02d-v1.png'%i))) for i in [1,2]]")
t=t.replace('actual-one-source-card-rendered-awaiting-pixel-review','actual-two-source-cards-rendered-awaiting-pixel-review').replace('ONE actual source card visible/rendered','TWO actual source cards visible/rendered')
write(RUN/'render-source-card-v2.py',t);compile(t,str(RUN/'render-source-card-v2.py'),'exec')
c=RUN/'render-source-card-v1.cjs';write(c,Path('runs/online-affine-subgradient-migration-20261007/render-source-card-v1.cjs').read_bytes())
write(RUN/'renderer-pre-use-correction-v2.json',dict(original=p.as_posix(),original_sha256=sha(p),original_unused=True,actual_selected_reader_cards=2,correction='Actual reader Definition2.29 and Theorem2.30 have two source cards. General CJS renders both; unused one-card Python assertions/image manifest adapted to exact both cards before firstuse.',executed_failure=False,source_or_math_changed=False,readonly_diagnostic='Guessed source-card-renderer-v1.cjs path absent; actual render-source-card-v1.cjs located from actual Python helper and read. No gate inference.'))
generated('renderer-adapters-before-use-v2.json',[RUN/'render-source-card-v2.py',c])
print('Both actual source cards required/rendered; unused template preserved, no executed rendering failure.')
