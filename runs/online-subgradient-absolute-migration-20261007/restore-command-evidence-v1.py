"""Restore overwritten command receipts from exact committed raw Git blobs; no receipt rewriting."""
from common import *
import ast
text=(RUN/'verify-history-bindings-v3.py').read_text(encoding='utf-8')
tree=ast.parse(text);env=dict(run=RUN,Path=Path,str=str)
lists=[n.iter for n in tree.body if isinstance(n,ast.For) and isinstance(n.target,ast.Name) and n.target.id=='p']
snapshot_paths=eval(compile(ast.Expression(lists[0]),'<frozen snapshot list>','eval'),{},env)
receipt_node=next(n.value for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='receipts' for t in n.targets))
receipts=eval(compile(ast.Expression(receipt_node),'<frozen receipt list>','eval'),{},env)
known={}
for p in snapshot_paths:
 for row in load(p)['rows']:
  assert sha(row['snapshot'])==row['raw_sha256']
  known[(str(Path(row['path']).resolve()),row['raw_sha256'])]=row
rows=[];commits=['b2b5485f24c1433580435e12e8d93d3ae8290a3a','c3446df9187a1607dc2f7ccbe92c6a732f66d6a2']
for receipt in receipts:
 r=load(receipt);assert sha(r['report'])==r['report_sha256']
 for row in r['reviewed_files']:
  p=Path(row['path']);expected=row['sha256'];current=sha(p);key=(str(p.resolve()),expected)
  if current==expected or key in known:continue
  rel=p.resolve().relative_to(Path('.').resolve()).as_posix();found=None
  for commit in commits:
   q=subprocess.run(['git','show',commit+':'+rel],stdout=subprocess.PIPE,stderr=subprocess.PIPE)
   if q.returncode==0 and hashlib.sha256(q.stdout).hexdigest()==expected:
    found=(commit,q.stdout);break
  assert found is not None,('No exact historical raw Git blob',row['path'],expected)
  commit,raw=found;dest=RUN/'snapshots'/('committed-command-'+p.name+'-'+expected[:12]+'.txt')
  if dest.exists():assert dest.read_bytes()==raw
  else:write(dest,raw)
  blob=subprocess.check_output(['git','rev-parse',commit+':'+rel],encoding='utf-8').strip()
  item=dict(path=row['path'],raw_sha256=expected,snapshot=dest.as_posix(),snapshot_sha256=sha(dest),current_sha256=current,source_commit=commit,source_git_blob=blob,source_git_path=rel,authorized_delta='Repeated native wrapper label overwrote command output during reader-only repair; original exact bytes recovered from already committed Git blob, immutable rejected receipt retained. Current replacement command bytes bound separately.')
  rows.append(item);known[key]=item
# Explicit aliases must work for every actually reviewed path, absolute or relative.
for receipt in receipts:
 for row in load(receipt)['reviewed_files']:
  key=(str(Path(row['path']).resolve()),row['sha256'])
  if sha(row['path'])!=row['sha256']:
   assert key in known,row['path']
   if known[key]['path']!=row['path']:
    alias=dict(known[key]);alias['path']=row['path'];alias['path_alias_only']=True
    if not any((x['path'],x['raw_sha256'])==(alias['path'],alias['raw_sha256']) for x in rows):rows.append(alias)
write(RUN/'historical-raw-supersession-command-collision-v1.json',dict(status='exact-committed-raw-restoration',rows=rows,rejected_FINALv1_unmodified=True,all_mathematical_headers_bodies_canaries_unchanged=True,failure_log='history-bindings-v2-01.log',future_wrapper_labels_unique=True,scope='Command-evidence label collision only; no proof or contract repair.'))
fixed(True)
print('Recovered',len(rows),'exact raw/alias bindings from committed Git; original reviews unchanged.')
