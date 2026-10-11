from common import *
import ast
manifest=load(RUN/'delivery-scripts-prepared-20261011-v1.json')
paths=[]
for row in manifest['scripts']:
    p=Path(row['path']);assert sha(p)==row['sha256']
    text=p.read_text(encoding='utf8')
    name=p.name.replace('_v1.py','_v2.py').replace('-v1.py','-v2.py')
    text=text.replace('from delivery_guard_20261011_v1 import *','from delivery_guard_20261011_v2 import *')
    text=text.replace("r.get('approved_plan_sha256')==sha(PLAN)","r.get('approved_plan_sha256',r.get('approved_plan_raw_sha256'))==sha(PLAN)")
    ast.parse(text,filename=name);write(RUN/name,text);paths.append(RUN/name)
write(RUN/'delivery-scripts-prepared-20261011-v2.json',dict(config=manifest['config'],scripts=rows(paths),ast_parse=True,executed=False,supersedes=rows([RUN/'delivery-scripts-prepared-20261011-v1.json']),repair='Read-only review schema discovery: approved_plan_raw_sha256 is actual field; v2 accepts either explicit approved plan hash spelling, still requires exacthash and favorable verdict/no blocking repairs.',exact_favorable_review=rows([RUN/'fresh-exact-integration-review-20261011-v5.json']),requirements=manifest['requirements']))
print('7preparedv2scripts AST-checked; no gate execution.')
