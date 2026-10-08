from common_body_v1 import *
integrated_fixed()
old=ROOT/'runs/online-kernel-causal-20261008'
cjs=(old/'capture-reader-v1.cjs').read_text(encoding='utf8').replace('kernel-causal-source-card','ftl-limit-source-card')
write(RUN/'capture-reader-v1.cjs',cjs)
py=(old/'capture-reader-v1.py').read_text(encoding='utf8')
py=py.replace('fixed_integrated()','integrated_fixed()').replace('online-kernel-causal','online-ftl-limit')
py=py.replace("ROOT / 'runs/online-completed-causal-20261008/formula-render-v5-browser.json'",
    "ROOT / 'runs/online-kernel-causal-20261008/formula-render-v1-browser.json'")
py=py.replace("'targets-v2.json'","'targets-v1.json'")
py=py.replace('creationflags=subprocess.CREATE_NO_WINDOW, timeout=55)',
    'creationflags=subprocess.CREATE_NO_WINDOW)')
write(RUN/'capture-reader-v1.py',py)
write(RUN/'browser-protocol-bindings-v1.json',dict(old_protocol=rows([old/'capture-reader-v1.cjs',old/'capture-reader-v1.py']),
    new_protocol=rows([RUN/'capture-reader-v1.cjs',RUN/'capture-reader-v1.py']),
    adaptations=['New ownedrun/site/profile/header-file paths','Old actual sourceguide count plusone card',
        'Do not abort whole12-panel process after55seconds; model polls yielded process and sends progress; per-browser operation timeout retained45seconds'],
    actual_capture_run=False,generated_site_mutations=False))
print('Prepared owned12 originalimage capture from existing scoped protocol, not yet run.',flush=True)
