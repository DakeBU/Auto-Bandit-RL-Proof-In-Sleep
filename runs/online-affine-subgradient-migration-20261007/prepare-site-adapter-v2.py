"""Clarify the actual check_site schema before first site helper execution."""
from common_v2 import *
p=RUN/'source-site-gates-v1.py';text=p.read_text(encoding='utf-8');assert "'--site',site" in text
text=text.replace("'--site',site","'--output',site")
text=text.replace("details=raw,remaining_other_Chapter1_contract_gaps_required=True", "details=raw,missing_required_changed_paths=sorted(set(re.findall(r'BanditRLProof/Online\\w+\\.lean',raw))),required_gaps_not_waived=True,remaining_other_Chapter1_contract_gaps_required=True")
text=text.replace("else:raise AssertionError('Historical main-relative boundary changed; audit current result rather than invent expected gaps.')", "else:raise AssertionError('Historical main-relative boundary changed; audit current result rather than invent expected gaps.')\nassert len(load(RUN/'main-relative-required-gaps-v1.json')['missing_required_changed_paths'])==9")
write(RUN/'source-site-gates-v2.py',text)
write(RUN/'site-CLI-pre-use-correction-v2.json',dict(actual_help='site-check-help-v1-01.log',original_helper=p.as_posix(),original_sha256=sha(p),original_unused=True,correction='Actual check_site.py uses --output; original unused v1 --site corrected in v2 before first execution. Actual nine other Chapter1 required main-relative paths will be extracted/asserted, no waiver.',actual_failed_site_attempt=False,source_math_changed=False))
c=RUN/'render-source-card-v1.cjs';write(c,Path('runs/online-hinge-migration-20261007/render-source-card-v1.cjs').read_bytes())
for p in [RUN/'source-site-gates-v2.py',RUN/'render-source-card-v1.py']:compile(p.read_text(encoding='utf-8'),str(p),'exec')
generated('site-adapter-before-use-v2.json',[RUN/'source-site-gates-v2.py',RUN/'render-source-card-v1.py',c,RUN/'verify-registry-v1.py'])
print('Actual site --output schema and copied task-owned renderer bound before first use.')
