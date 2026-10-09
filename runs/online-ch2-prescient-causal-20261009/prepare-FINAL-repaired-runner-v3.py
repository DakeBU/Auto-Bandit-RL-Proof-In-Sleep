from publication_guard_v2 import *
fixed()
s = (RUN / 'prepare-FINAL-v2.py').read_text(encoding='utf8')
s = s.replace('Actual clean isolated SITEv1 build', 'Actual clean isolated repaired SITEv2 build')
s = s.replace('Actual SITEv1 check/registry', 'Actual repaired SITEv2 check/registry')
s = s.replace('No visible clipping in these captures.', 'The repaired completion formula visibly includes every reached-state attainment premise and its terminal conclusion. Original SITEv1 silent gathered alignment loss is preserved and not accepted. No visible clipping in these captures.')
s = s.replace("    '\\nCurrent-package full whitespace0/no exceptions.",
    "    '\\nOriginal SITEv1 automatic checks passed but root/source reviewer found missing attainment premise in original note7; native repair recorded. Exact one-new-note math bigl/bigr repair-v3 independently accepted, Lean/fullharness inputs unchanged. Clean repaired SITEv2/check/registry and actual stronger MathML/pixels now supplied. Original DOM/images/failed inspections retained.\\nCurrent-package full whitespace0/no exceptions.")
assert 'Actual clean isolated SITEv1 build' not in s
write(RUN / 'prepare-FINAL-v3.py', s)
print('Prepared first actual FINAL for repaired SITEv2; original failed rendering remains explicit.')
