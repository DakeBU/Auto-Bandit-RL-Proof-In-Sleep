from common_v1 import *
import ast
fixed(True)
table=load(RUN/'publication-tools-before-FINAL-v3.json')
for x in table['rows']:ast.parse(Path(x['path']).read_text(encoding='utf-8'))
write(RUN/'publication-tools-before-FINAL-v4.json',dict(scope='Actual final current helpers bound before FINAL; historical v1-v3 tables remain historical. Current clean site/captures use v2; five failures retained.',rows=[dict(path=x['path'],sha256=sha(x['path'])) for x in table['rows']],source_math_contract_version=1,new_public_math=0,actual_FINAL_not_executed=True))
subprocess.run([sys.executable,'-B','-X','utf8',str(RUN/'commit-owned-v1.py'),'Preserve current reader pixels and prepared FINAL evidence'],check=True)
gate('contributor-reader-v2',sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',BASE)
gate('scoped-diff-reader-v2',sys.executable,'-B','-X','utf8',RUN/'check-scoped-diff-v1.py','reader-v2')
gate('source-scope-reader-v2',sys.executable,'-B','-X','utf8',RUN/'audit-scope-v1.py','reader-v2')
fixed(True)
