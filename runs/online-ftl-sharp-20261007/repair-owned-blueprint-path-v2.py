from common_v1 import *
fixed();p=RUN/'owned-commit-paths-v1.json';write(RUN/'snapshots/owned-paths-before-blueprint-correction-v1.raw',p.read_bytes())
owned=load(p);incorrect='research-wiki/proof-blueprints/'+TASK+'.md';actual='proof-blueprints/'+TASK+'.md'
assert incorrect in owned and Path(actual).is_file() and not Path(incorrect).exists()
owned[owned.index(incorrect)]=actual;p.write_bytes((json.dumps(owned,indent=2)+'\n').encode('utf-8'))
write(RUN/'owned-blueprint-path-correction-v2.json',dict(status='Actual own task blueprint path corrected before source review',actual_CLI_constant='tools/bandit.py:47 BLUEPRINT_DIR=ROOT/proof-blueprints',old_path=incorrect,actual_path=actual,mathematical_contract_version=1,no_source_statement_or_body_change=True))
write(RUN/'source-pixel-review-v1.json',dict(actor='/root',actual_tool='view_image',actual_viewed=[dict(pdf_page=n,path=(RUN/f'source-pdf{n}-v1.png').as_posix(),sha256=sha(RUN/f'source-pdf{n}-v1.png')) for n in [16,17,18]],observed='Printed4/PDF16 Theorem1.3 initial1/2 and best-fixed interval comparator; printed5/PDF17 first-round0.5^2, later4/t and accumulated0.25+4sum(t=2..T)1/t; printed6/PDF18 harmonic upper bound1+lnT. Actual source pixels reviewed, not only extraction.',chapter_complete=False,goal_complete=False))
fixed();print('Only blueprint ownership metadata corrected to actual CLI path; all source target bytes unchanged.')
