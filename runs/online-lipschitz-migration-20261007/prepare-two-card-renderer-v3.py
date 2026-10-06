"""Correct both unused Python AND actual CJS before any browser execution."""
from common_v2 import *
assert not (RUN/'formula-render-v1-01-exit.json').exists()
p=RUN/'render-source-card-v2.py';t=p.read_text(encoding='utf-8');assert "render-source-card-v1.cjs" in t
t=t.replace('render-source-card-v1.cjs','render-source-card-v2.cjs');write(RUN/'render-source-card-v3.py',t);compile(t,str(RUN/'render-source-card-v3.py'),'exec')
write(RUN/'renderer-pre-use-correction-v3.json',dict(original_unused=['render-source-card-v1.py','render-source-card-v2.py','render-source-card-v1.cjs'],actual_selected_reader_cards=2,superseded_record='renderer-pre-use-correction-v2.json wrongly described original CJS as generic; inspecting actual CJS shows it asserts exactlyone and screenshots firstonly.',correction='New CJSv2 actually iterates both cards, opens each source disclosure, checks one MathJax formula/noerrors each and screenshots both. Pythonv3 uses this exact newCJS. All unused versions and their metadata preserved, no browser execution/gate pass claimed for them.',executed_failure=False,source_or_math_changed=False))
generated('renderer-adapters-before-use-v3.json',[RUN/'render-source-card-v3.py',RUN/'render-source-card-v2.cjs'])
print('Actual two-card CJS iteration/Python command prepared and bound before firstuse; unused misclassification preserved and corrected.')
