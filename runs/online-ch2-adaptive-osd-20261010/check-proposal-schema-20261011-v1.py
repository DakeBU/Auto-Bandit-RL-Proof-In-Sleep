from common import *
sys.path.insert(0,str(ROOT))
from tools.check_contributor_contract import validate_contract
path=RUN/'prospective-contribution-20261011-v1.json'
data,errors=validate_contract(path)
write(RUN/'prospective-contribution-schema-check-20261011-v1.json',dict(manifest=rows([path]),errors=errors,scope='Schema/content validator only; no diff-aware full contribution acceptance or semantic status promotion.'))
print(errors)
