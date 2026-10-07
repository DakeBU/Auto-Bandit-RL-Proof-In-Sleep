"""Match the existing contributor schema before first reader integration."""
from common_v2 import *
text=(RUN/'integrate-reader-v1.py').read_text(encoding='utf-8');assert "lean_graph='reuse'" in text
text=text.replace("lean_graph='reuse'","lean_graph='reuse-only'")
compile(text,str(RUN/'integrate-reader-v2.py'),'exec');write(RUN/'integrate-reader-v2.py',text)
write(RUN/'integration-adapter-before-use-v2.json',dict(reason='Actual contributor schema LEAN_STATES permits reuse-only, not reuse. Prospective v1 never run; effective v2 corrected before first mutation.',effective_script_sha256=sha(RUN/'integrate-reader-v2.py'),public_and_canary_unchanged=True,mathematical_change=False))
print('Prospective reader adapter conforms to existing reuse-only schema before first use.')
