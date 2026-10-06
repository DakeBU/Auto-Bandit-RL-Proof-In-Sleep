from common import *
s=(RUN/'audit-committed-raw-v1.py').read_text(encoding='utf-8-sig')
s=s.replace("rows=[];ignored=[]", "rows=[];ignored=[]\nentries=subprocess.check_output(['git','ls-tree','-r','-z',head,'--',RUN.resolve().relative_to(root).as_posix()]).split(b'\\0')\nobjects={e.split(b'\\t',1)[1].decode('utf-8'):e.split(b'\\t',1)[0].split()[2].decode('ascii') for e in entries if e}")
s=s.replace("raw=subprocess.check_output(['git','show',head+':'+rel]);", "assert rel in objects,('File not in audited Git tree',rel);raw=subprocess.check_output(['git','cat-file','blob',objects[rel]]);")
s=s.replace("rows.append(dict(path=rel,raw_sha256=h))", "rows.append(dict(path=rel,git_blob=objects[rel],raw_sha256=h))")
write(RUN/'audit-committed-raw-v2.py',s)
write(RUN/'committed-raw-audit-repair-v2.json',dict(status='read-only-Git-object-repair-before-retry',failure='committed-raw-audit-v2-01 git show HEAD:longpath hit Windows revision/path disambiguation filename limit for an existing exact snapshot.',repair='Read actual HEAD tree with git ls-tree -r -z and git cat-file blob by exact object ID. No paths shortened/renamed/deleted, no raw snapshots changed, no global Git config change.',failed_logs=['committed-raw-audit-v1-01.log','committed-raw-audit-v2-01.log'],retry='committed-raw-audit-v3-01',mathematical_repairs=[]))
generated('raw-audit-helper-before-use-v2.json',[RUN/'audit-committed-raw-v2.py'])
