from common import *

branch = subprocess.check_output(['git','branch','--show-current'], encoding='utf8').strip()
head = subprocess.check_output(['git','rev-parse','HEAD'], encoding='utf8').strip()
pr = json.loads(subprocess.check_output(['gh','pr','view','217','--json',
    'url,state,isDraft,headRefName,headRefOid,baseRefName'], encoding='utf8'))
assert branch == BRANCH and head == BASE
assert pr['headRefName'] == 'codex/research-online-ch2-adaptive-energy'
assert pr['headRefOid'] == BASE and pr['state'] == 'OPEN' and pr['isDraft']
write(RUN/'delivery-target-reconciliation-20261011-v1.json', dict(
    local_branch=branch, initial_head=head, prerequisite_pr=pr,
    correction='PR217 is the adaptive-energy prerequisite, not the adaptive-OSD delivery branch. Same initial commit does not mean same PR.',
    intended_delivery='New draft PR from codex/research-online-ch2-adaptive-osd to codex/research-online-ch2-adaptive-energy after candidate gates/review.',
    current_pr_created=False, prerequisite_pr_modified=False, goal='active',
    chapter_complete=False, main_updated=False, live_updated=False))
print('Bound distinct OSD delivery branch and energy prerequisite PR.', flush=True)
