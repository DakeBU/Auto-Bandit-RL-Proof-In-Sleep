from publication_guard_v2 import *
fixed()
s = (RUN / 'prepare-FINAL-v6.py').read_text(encoding='utf8')
old = "*[ROOT / 'website/content' / n for n in ['chapters.json', 'readings.json', 'highlights.json']],"
assert s.count(old) == 1
s = s.replace(old, "*[ROOT / 'website/content' / n for n in ['chapters.json', 'readings.json', 'highlights.json', 'declaration-boundaries.json']],")
s = s.replace("write(RUN / 'FINAL-packet-v1.md',", "write(RUN / 'memory-digest-v4.md', '# Catalogue repair and retained rejection\\n\\nSITEv2 v3-browser actual0 did not establish exact iterate catalogue range: neighboring theorem contamination found by root. Original22pixels/DOM retained. Distinct v4 rejected materialization solely for stale allowed_old_mutations5 vs6rows. Versioned plan-v5 changes only count to6, separately reviewed before config write. Existing schema1/source-bound range preserves frozen Lean and old FTL entry. Fresh combined fullgate, clean SITEv3/registry/browser-v4 and root/distinct22pixels required; no source/chapter/Goal closure.\\n')\nwrite(RUN / 'FINAL-packet-v1.md',")
compile(s, 'prepare-FINAL-v7.py', 'exec')
write(RUN / 'prepare-FINAL-v7.py', s)
print('Prospective FINAL includes exact boundary config RAW pin and retained failure digest.')
