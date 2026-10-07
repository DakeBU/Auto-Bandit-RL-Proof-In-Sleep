from common_v1 import *
fixed(proving=True,integrated=True)
old=load(RUN/'publication-tools-before-FINAL-v2.json')
for row in old['rows']:assert sha(row['path'])==row['sha256']
write(RUN/'publication-tools-before-FINAL-v3.json',{**old,'scope':'Active sequence is explicitly v2 acceptance/publication/delivery plus unchanged create-pr-v1/rawaudit-v1. Old v1 plans retained and never executed. Only old v1 DELIVERY has absent registry-v1 prerequisite; v1 acceptance is not claimed technically disabled. The v2 selection is a recorded workflow instruction, not a single runtime enforcement. Current registry-v2/site-v2 binding is explicit. DistinctFINAL stillpending.','clarifies_prior_scope_sha256':sha(RUN/'publication-tools-before-FINAL-v2.json')})
s=(RUN/'prepare-final-review-v2.py').read_text(encoding='utf-8').replace('publication-tools-before-FINAL-v2','publication-tools-before-FINAL-v3').replace('originalv1plans retained/unexecuted/disabled absentregistry-v1','originalv1plans retained/unexecuted; onlyv1delivery hasabsentregistry-v1 prerequisite; activev2selection isrecordedworkflowinstruction, no claimv1acceptance technicallydisabled')
write(RUN/'prepare-final-review-v3.py',s)
