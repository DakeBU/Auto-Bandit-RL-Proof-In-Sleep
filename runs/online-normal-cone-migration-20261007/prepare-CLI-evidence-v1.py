from common import *
for command in ['statement-fence','retrieval-record','list-lean-decls','search-memory','trial-log','frontier-refresh','frontier-shadow']:
 native(command+'-help-v1-01',command,'--help')
generated('contract-preparer-before-use-v1.json',[RUN/'prepare-contract-v1.py'])
