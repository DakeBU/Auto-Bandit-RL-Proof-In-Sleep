"""Audit copied gate references before first rerender; retain unused adapters."""
from common_v2 import *
fixed(True)
text=(RUN/'verify-registry-v2.py').read_text(encoding='utf-8').replace('registry-base-snapshot-v2.json','registry-base-snapshot-v1.json').replace('native-statement-fingerprints-v2.json','native-statement-fingerprints-v1.json');write(RUN/'verify-registry-v3.py',text)
text=(RUN/'audit-scope-v1.py').read_text(encoding='utf-8').replace('source-scope-audit-v1.json','source-scope-audit-v2.json');write(RUN/'audit-scope-v2.py',text)
text=(RUN/'source-site-gates-v3.py').read_text(encoding='utf-8').replace('verify-registry-v2.py','verify-registry-v3.py').replace("RUN/'audit-scope-v1.py'","RUN/'audit-scope-v2.py'");write(RUN/'source-site-gates-v4.py',text)
text=(RUN/'prepare-final-evidence-v5.py').read_text(encoding='utf-8').replace('source-site-gates-v3-01','source-site-gates-v4-01').replace('full harness2/current contributor2 required','schema repair passed harness2/contributor2; latest reader requires harness3/contributor3')
write(RUN/'prepare-final-evidence-v6.py',text)
write(RUN/'reader-gate-adapters-before-use-v4.json',dict(finding='Broad version copying would rename immutable registry baseline/native fingerprints and reuse a written scope output. Caught before any version2 registry/scope3/site2 gate execution.',effective_registry_probe='verify-registry-v3.py',immutable_baseline='registry-base-snapshot-v1.json',immutable_native_fingerprints='native-statement-fingerprints-v1.json',new_scope_output='source-scope-audit-v2.json',effective_site_controller='source-site-gates-v4.py',original_unused_copied_adapters_preserved=True,public_canary_and_reader_formulas_unchanged=True))
print('Immutable baseline/native versions and unique scope output checked before actual site2 use.')
