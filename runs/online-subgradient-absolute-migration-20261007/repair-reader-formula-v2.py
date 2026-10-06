"""Repair only the source-card TeX grouping after the distinct FINAL rejection."""
from common import *
f=fixed(True);r=load(RUN/'final-reader-receipt-v1.json');assert r['verdict']=='rejected' and not r['mathematical_repairs']
assert sha(r['report'])==r['report_sha256'] and len(r['required_repairs'])==1
p=Path('website/content/readings.json');old=load(p);d=load(p);x=next(a for a in d['readings'] if a['slug']==ROUTE)
assert len(x['source_theorems'])==1
before=x['source_theorems'][0]['math'];dest=RUN/'snapshots/reader-before-formula-repair-v2.json.txt';write(dest,p.read_bytes())
formula=r'\partial|\cdot|(x)=\begin{cases}\{1\}&x>0\\{[-1,1]}&x=0\\\{-1\}&x<0\end{cases}'
assert before!=formula and formula.count('\\\\')==2
x['source_theorems'][0]['math']=formula
write(p,d,True)
ox=next(a for a in old['readings'] if a['slug']==ROUTE);ox['source_theorems'][0]['math']=formula
assert old==d,'Only one source-card math field may change'
from website.scripts.build_site import normalize_math_source
assert normalize_math_source(formula)==r'\['+formula+r'\]'
write(RUN/'historical-raw-supersession-reader-v2.json',dict(rows=[dict(path=p.as_posix(),raw_sha256=sha(dest),snapshot=dest.as_posix(),snapshot_sha256=sha(dest),authorized_delta='Source-card TeX interval grouping only, mathematical set equality unchanged; distinct rejected FINAL preserved.')]))
write(RUN/'reader-formula-repair-v2.json',dict(rejected_receipt='final-reader-receipt-v1.json',rejected_report_sha256=r['report_sha256'],before=before,after=formula,actual_normalizer_output=normalize_math_source(formula),all_original_Lean_math_bytes_and_headers_unchanged=True,new_mathproofs=0,source_statement_repair=False,owned_delta='Only online-subgradient-absolute.source_theorems[0].math',existing_applicable_Lean_gate='postcomment root9089/Tests9234/full466tests7skips unchanged Lean sources; no unnecessary repeat solely for reader grouping',read_only_preparation_diagnostics='PowerShell nested-quote read command failed to parse before execution; subsequent here-string corrected it. Guessed website/assets absent; actual renderer paths located by rg before subsequent use. No compiler result or math mutation.'))
event('repair',dict(scope='source-card TeX row/closed interval grouping',source_package_accepted=False,mathematical_statement_repair=False,review_receipt='final-reader-receipt-v1.json',all_four_frozen_headers=f['headers']))
event('candidate',dict(scope='reader-only formula repair, mathematical source unchanged',source_package_accepted=False,remaining_gates=['current site/formula/registry/browser','history/exact contributor/diff','distinct FINALv2/realPR']))
fixed(True)
print('Only source-card TeX grouping repaired; actual normalizer retains both row separators/full [-1,1]. Current site/formula/FINALv2 required.')
