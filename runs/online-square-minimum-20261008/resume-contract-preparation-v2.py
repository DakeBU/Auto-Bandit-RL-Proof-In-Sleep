from common_v1 import *
fixed()
native('actual-blueprint-refresh-v2','blueprint-refresh',TASK)
p=Path('research-wiki/retrieval-index')/(TASK+'.md')
if not p.exists():write(p,'Draft actual square minimum retrieval; source/types not yet accepted. See '+(RUN/'retrieval_index.md').as_posix())
for folder in ['proof-blueprints','research-wiki/retrieval-index']:
    p=Path(folder)/(TASK+'.md')
    p.write_bytes(p.read_bytes()+('\n\n## Draft exact square-minimum contract v1\n\n'+(CONTRACT/'contract-v1.md').read_text(encoding='utf8')+'\nFrozen prospective headers: '+sha(CONTRACT/'targets-v1.json')+'; no source/body acceptance yet.\n').encode('utf8'))
write(RUN/'contract-preparation-repair-v2.json',dict(failed='prepare-contract-v1.py exited1: new-task actual CLI only creates task/conversion/proof-obligation files; proof-blueprint missing.',
    repair='Use actual blueprint-refresh CLI and create own retrieval note; preserve already appended three native task files and all six headers/context/source bytes; resume retrieval/compile tail only.',
    source_and_statement_change=False,new_task_original_stdout='new-task-v1.log'))
source=(RUN/'prepare-contract-v1.py').read_text(encoding='utf8')
tail=source[source.index("write(RUN/'native-reference-index-v1.py'"):]
exec(compile(tail,'prepare-contract-v1-actual-retrieval-tail','exec'))
