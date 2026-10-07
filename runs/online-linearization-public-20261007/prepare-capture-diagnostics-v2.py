from common_v2 import *
s=(RUN/'capture-reader-v1.py').read_text(encoding='utf-8').replace('capture-reader-v1.cjs','diagnose-capture-v2.cjs').replace('formula-render-v1','capture-diagnostics-v2').replace('online-linearization-public-playwright-v1-profile','online-linearization-public-diagnostics-v2-profile')
s=s[:s.index('assert sha(page)==before')]+"assert sha(page)==before;print('Actual DOM diagnostics only; no image/formula-gate pass claimed.')\n"
write(RUN/'diagnose-capture-v2.py',s)
print('Versioned diagnostics prepared from unchanged capture wrapper; no unsafe nested shell quoting.')
