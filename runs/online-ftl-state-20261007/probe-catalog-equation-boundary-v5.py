from common_v1 import *
import inspect
sys.path.insert(0,str(ROOT/'website/scripts'))
import build_site as site
original=site.compact_statement
src=inspect.getsource(original).replace('def compact_statement(','def compact_statement_equations(')
src=src.replace('    for raw in lines[start : min(len(lines), start + 90)]:','    initial_match = DECL_RE.match(lines[start])\n    is_definition = bool(initial_match and initial_match.group("kind") == "def")\n    equation_style = False\n    for raw in lines[start : min(len(lines), start + 90)]:')
src=src.replace('        if not stripped:\n            continue','        if not stripped:\n            continue\n        if equation_style and delimiter_depth == 0 and not block_comment_depth and not in_string:\n            if DECL_RE.match(raw) or END_RE.match(raw) or NAMESPACE_RE.match(raw) or SECTION_RE.match(raw) or stripped.startswith("/--"):\n                break\n        if is_definition and delimiter_depth == 0 and not block_comment_depth and not in_string and stripped.startswith("| "):\n            equation_style = True')
src=src.replace('and delimiter_depth == 0 and not is_result_let:','and delimiter_depth == 0 and not is_result_let and not equation_style:')
env=dict(site.__dict__);exec('from __future__ import annotations\n'+src,env);updated=env['compact_statement_equations']
write(RUN/'catalog-boundary-proposed-function-v5.py',src)
base={n['id']:n for n in load(RUN/'registry-base-snapshot-v1.json')['nodes']};changes=[]
for path in sorted(Path('BanditRLProof').rglob('*.lean')):
 old=site.scan_module(ROOT/path);site.compact_statement=updated
 new=site.scan_module(ROOT/path);site.compact_statement=original
 a={x['full_name']:x for x in old['declarations']};b={x['full_name']:x for x in new['declarations']};assert set(a)==set(b)
 for name in a:
  if a[name]['statement']!=b[name]['statement']:
   changes.append(dict(name=name,kind=a[name]['kind'],path=path.as_posix(),old_statement=a[name]['statement'],new_statement=b[name]['statement'],old_sha256=hashlib.sha256(a[name]['statement'].encode()).hexdigest(),new_sha256=hashlib.sha256(b[name]['statement'].encode()).hexdigest(),in_inherited_registry='declaration:'+name in base))
write(RUN/'catalog-boundary-impact-probe-v5.json',dict(status='Read-only in-memory proposed parser audit, no repository mutation or acceptance',old_registry_nodes=10823,changes=changes,changed_old=sum(x['in_inherited_registry'] for x in changes),changed_proofs=sum(x['kind'] in ['theorem','lemma'] for x in changes),public_Lean_files_unchanged=True))
print(json.dumps(dict(changed=len(changes),changed_old=sum(x['in_inherited_registry'] for x in changes),changed_proofs=sum(x['kind'] in ['theorem','lemma'] for x in changes),names=[x['name'] for x in changes])))
