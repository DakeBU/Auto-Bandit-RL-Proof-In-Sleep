from publication_guard_v4 import *
fixed()
s = (RUN/'commit-and-build-site-v4.py').read_text(encoding='utf8')
for n in ['candidate-commit', 'contributor-stack', 'contributor-main']:
    s = s.replace(n+'-v3', n+'-v4')
s = s.replace("clean_capture('candidate-commit-v4',", "clean_capture('pre-site-full-diff-v4', ['git','diff','--cached',BASE,'--check'])\nclean_capture('candidate-commit-v4',")
s = s.replace('Bound prescient iterate catalogue to its complete frozen definition', 'Record reviewed source-range ownership and repaired reader evidence')
write(RUN/'commit-and-build-site-v5.py',s)
s = (RUN/'prepare-FINAL-v7.py').read_text(encoding='utf8')
for n in ['contributor-stack', 'contributor-main']:
    s = s.replace(n+'-v3', n+'-v4')
s = s.replace("'catalogue-repair-review-v5.json']:", "'catalogue-repair-review-v5.json', 'contributor-repair-review-v1.json']:")
s = s.replace('Catalogue repair also retained:', 'Contributor gate repair retained: fresh combined v2 passed, clean ff9bc7b candidate committed but contributor-stack-v3 rejected unlisted declaration-boundaries production path, so SITEv3 did not start. Distinct prospective one-field affected_files append reviewed before materialization; all other own fields and frozen mathematics/config/generator unchanged. Current fresh contributor bases separately required.\n\nCatalogue repair also retained:')
s = s.replace("write(RUN / 'FINAL-packet-v1.md',", "write(RUN / 'memory-digest-v5.md', '# Contributor ownership repair\\n\\nFresh full combined v2 passed with exact reviewed boundary config. Candidate ff9bc7b committed but contributor-stack-v3 actual1 rejected missing affected_files ownership for that config; no site ran. Original receipts retained; exact own manifest affected_files append separately reviewed before materialization. Current fresh contributor and cleanSITEv3/browser/FINAL required; no postcorrection fresh fullharness rerun claim for attribution-only metadata.\\n')\nwrite(RUN / 'FINAL-packet-v1.md',")
compile(s, 'prepare-FINAL-v8.py', 'exec')
write(RUN/'prepare-FINAL-v8.py',s)
print('Fresh contributor/site and complete retained-failure FINAL helpers created only.')
