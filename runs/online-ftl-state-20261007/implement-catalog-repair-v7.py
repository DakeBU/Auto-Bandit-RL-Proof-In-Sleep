from common_v1 import *
import types
fixed(proving=True,integrated=True)
resolution=load(RUN/'catalog-scope-reviewed-source-resolution-v6.json')
def reviewed_sha(p):
 return sha(resolution['immutable_snapshot']) if Path(p).resolve()==(ROOT/resolution['original_live_path']).resolve() else sha(p)
r=load(RUN/'catalog-scope-receipt-v6.json');assert r['verdict']=='accepted-with-explicit-delta' and sha(r['report'])==r['report_sha256']
reviewed={x['path']:x['sha256'] for x in r['reviewed_files']}
for x in load(RUN/'catalog-scope-review-inputs-v6.json')['rows']:assert reviewed[x['path']]==x['sha256']==reviewed_sha(x['path'])
for p,h in reviewed.items():assert reviewed_sha(p)==h,p
assert load('website/content/declaration-boundaries.json')==load(RUN/'catalog-boundaries-proposed-v6.json')
from website.scripts import build_site as site
old=types.ModuleType('website.scripts.reviewed_previous_scanner');old.__file__=str(ROOT/'website/scripts/build_site.py');old.__package__='website.scripts'
exec(compile(Path(resolution['immutable_snapshot']).read_text(encoding='utf-8'),old.__file__,'exec'),old.__dict__)
before=old.scan_lean_tree();after=site.scan_lean_tree();changes=[]
assert len(before)==len(after)
for left,right in zip(before,after):
 assert {k:v for k,v in left.items() if k!='declarations'}=={k:v for k,v in right.items() if k!='declarations'}
 assert len(left['declarations'])==len(right['declarations'])
 for a,b in zip(left['declarations'],right['declarations']):
  if a==b:continue
  assert {k:v for k,v in a.items() if k!='statement'}=={k:v for k,v in b.items() if k!='statement'}
  assert b['full_name']==PRE+'ftlState' and b['kind']=='def' and 'theorem' not in b['statement']
  changes.append(dict(name=b['full_name'],before=a['statement'],after=b['statement']))
assert len(changes)==1
write(RUN/'catalog-source-comparison-v7.json',dict(status='passed',old_scanner_sha256=sha(resolution['immutable_snapshot']),current_scanner_sha256=sha('website/scripts/build_site.py'),config_sha256=sha('website/content/declaration-boundaries.json'),modules_compared=len(before),source_declarations_compared=sum(len(m['declarations']) for m in before),changes=changes,unchanged_theorems=True,only_one_new_definition_presentation=True,complete_source_pinned=True,no_native_recursive_fence_claim=True))
p=Path('research-wiki/contribution-contracts/online-ftl-state-20261007.json');m=load(p);m['verification']['owned_test_files'].append('tools/test_source_declaration_boundaries.py');p.write_text(json.dumps(m,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
write(RUN/'read-only-retrieval-error-v3.json',dict(actual_command="rg -n ... tools/test_*.py website/scripts -g '*.py'",error='Windows rejects literal glob filename; partial read output retained in tool history.',repair="Actual rg -n ... tools -g 'test_*.py' completed; no source mutation from failed retrieval.",semantic_effect='none'))
scope=(RUN/'audit-scope-v2.py').read_text(encoding='utf-8').replace('owned-commit-paths-v1.json','owned-commit-paths-v2.json')
scope += '''
resolution=load(RUN/'catalog-scope-reviewed-source-resolution-v6.json')
assert sha(resolution['immutable_snapshot'])==resolution['sha256']
r=load(RUN/'catalog-scope-receipt-v6.json');reviewed={x['path']:x['sha256'] for x in r['reviewed_files']}
for x in load(RUN/'catalog-scope-review-inputs-v6.json')['rows']:
 p=x['path'];resolved=resolution['immutable_snapshot'] if Path(p).resolve()==(ROOT/resolution['original_live_path']).resolve() else p
 assert reviewed[p]==x['sha256']==sha(resolved),p
assert load('website/content/declaration-boundaries.json')==load(RUN/'catalog-boundaries-proposed-v6.json')
c=load(RUN/'catalog-source-comparison-v7.json');assert c['current_scanner_sha256']==sha('website/scripts/build_site.py') and len(c['changes'])==1
assert sha('tools/test_source_declaration_boundaries.py')==load(RUN/'catalog-implementation-bindings-v7.json')['regression_tests_sha256']
'''
write(RUN/'audit-scope-v3.py',scope)
write(RUN/'catalog-implementation-bindings-v7.json',dict(status='implemented candidate; gates/FINAL pending',public_math_source_unchanged=True,Mean_sha256=sha(MEAN),public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY),scanner_sha256=sha('website/scripts/build_site.py'),regression_tests_sha256=sha('tools/test_source_declaration_boundaries.py'),approved_scope_receipt_sha256=sha(RUN/'catalog-scope-receipt-v6.json'),comparison_sha256=sha(RUN/'catalog-source-comparison-v7.json'),old100_candidates_migrated=False))
gate('catalog-focused-tests-v7',sys.executable,'-B','-X','utf8','-m','unittest','tools.test_source_declaration_boundaries')
print('Corpus source comparison only ftState presentation; six meaningful regression tests actual PASS.')
