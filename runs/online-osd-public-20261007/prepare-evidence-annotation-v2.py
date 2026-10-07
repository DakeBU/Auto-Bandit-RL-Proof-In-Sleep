"""Correct prospective annotations before use: no TeX escaping edit actually occurred."""
from common_v2 import *
fixed(True);tex=load(RUN/'reader-TeX-escaping-repair-v1.json');assert tex['rows']==[]
before=load(RUN/'snapshots/before-website--content--readings.json.txt');after=load('website/content/readings.json')
a=next(x for x in before['readings'] if x['slug']==ROUTE);b=next(x for x in after['readings'] if x['slug']==ROUTE)
assert [x['math'] for x in a['source_theorems']]==[x['math'] for x in b['source_theorems']]
text=(RUN/'prepare-final-evidence-v1.py').read_text(encoding='utf-8')
text=text.replace('Current source cards show the unchanged exact formulas after TeX escaping repair; direct pixels must confirm it.', 'Current source cards retain the exact original formula strings; the normalization probe changed zero fields. Direct pixels must confirm actual mathematical rendering.')
text=text.replace('Existing TeX source commands de-escaped only on owned reader; same mathematical formulas and source links.', 'Prospective TeX repair annotation corrected before first use: actual normalization changed zero fields, all six source formula strings unchanged.')
write(RUN/'prepare-final-evidence-v2.py',text)
text=(RUN/'prepare-pr-payload-v1.py').read_text(encoding='utf-8').replace('Existing reader TeX escaping corrected on this route without changing mathematical formulas or source links.', 'Actual reader normalization changed zero formula fields; all six original source formula strings and source links remain unchanged. A prospective escaping-repair annotation was corrected before first use, with the unused original script retained.')
write(RUN/'prepare-pr-payload-v2.py',text)
text=(RUN/'complete-delivery-gates-v1.py').read_text(encoding='utf-8').replace("passed('prepare-pr-payload-v1-01')","passed('prepare-pr-payload-v2-01')");write(RUN/'complete-delivery-gates-v2.py',text)
write(RUN/'evidence-annotation-before-first-use-v2.json',dict(finding='Escaped tool JSON output was initially misread as adjacent backslashes in source. Actual source has17 separate backslashes and zero doubles; normalization rows=[] and all six formula strings match their before snapshot. No actual TeX edit occurred. Unused future helper/PR annotation wrongly suggested one; effective helpers v2 correct it before first execution.',original_unused_v1_scripts_preserved=True,production_reader_public_canary_and_actual_math_strings_unchanged=True,actual_current_combined_gate_not_invalidated=True,source_FINAL_review_pending=True,new_proofs=0))
print('Actual zero TeX changes confirmed; prospective evidence/PR annotations corrected before first use, original scripts retained.')
