"""Read-only B4 structural QA; create-only ignored result; no builds or source edits."""
import argparse, copy, hashlib, json, subprocess, zipfile, sys, re
from collections import Counter
from pathlib import Path
HEAD=None
BRANCH=None
HELPER='bafe784fad8810f866105ffd19e3504f70ebf1e28949611549d584630a5b7ce8'
NAME='BanditRL.OnlineCumulativePotential.finite_regret_identity'
GROWTH='BanditRL.OnlineConvex.stronglyConvex_minimum_growth'
GOV=['README.md','AGENTS.md','CONTRIBUTING.md','docs/contribution-contract.schema.json','docs/contributor-codex-contract.md','docs/theorem-publication-protocol.md','docs/contracts/online-book-v1/coverage.json','docs/proof-digestion-protocol.md','docs/evidence-routed-memory-protocol.md','docs/openai-math-assimilation-protocol.md','research-wiki/openai-math-2026-intake.json','runs/process_memory.json']
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_bytes())
def need(b,s):
 if not b:raise ValueError(s)
def git(r,*a):return subprocess.check_output(['git','-c','core.longpaths=true',*a],cwd=r)
def state(r):return {'HEAD':git(r,'rev-parse','HEAD').decode().strip(),'branch':git(r,'branch','--show-current').decode().strip(),'status_porcelain_v1_z_hex':git(r,'status','--porcelain=v1','-z').hex()}
def gate_bindings_valid(r,a,spec):
 need(spec['evidence_required']['isolated_site']==str(a.site.resolve()),'specified isolated site')
 for role in ['full_harness','site_build_verified','site_check']:
  binding=spec['evidence_required'][role];need(isinstance(binding,dict),'missing receipt '+role)
  p=Path(binding['path']);need(digest(p)==binding['sha256'],'receipt hash '+role);g=load(p)
  need(g['actual_exit']==0 and g['command_started'] and g['capture_integrity_ok'] and g['complete_source_path_set_and_RAW_unchanged'],'successful immutable receipt '+role)
  for k in ['pre_git','post_git']:need(g[k]==state(r),'exact current state '+role)
  need(Path(g['cwd']).resolve()==r,'same cwd '+role)
  for name in ['pre-source-inputs.json','post-source-inputs.json','pre-selected-ZIP-inputs.json','pre-selected-source-raw.zip','stdout.raw','stderr.raw']:need(digest(p.parent/name)==g[name+'_sha256'],'gate artifact '+role+'/'+name)
  if role=='full_harness':need(p.resolve()==a.gate.resolve(),'one full harness receipt')
  if role in ['site_build_verified','site_check']:
   need('--output' in g['argv'] and (r/g['argv'][g['argv'].index('--output')+1]).resolve()==a.site.resolve(),'same isolated output '+role)
  if role=='site_build_verified':need('--lean-verified' in g['argv'] and any(str(x).replace('\\','/').endswith('website/scripts/build_site.py') for x in g['argv']),'verified site build argv')
  if role=='site_check':need(any(str(x).replace('\\','/').endswith('website/scripts/check_site.py') for x in g['argv']),'site check argv')
 return True

def check(a):
 r=a.root.resolve();spec=load(a.spec);need(digest(a.spec)==a.spec_sha256,'spec SHA');need(spec['ready_for_execution'] is True,'prepared spec is not executable');need(digest(Path(__file__))==spec['checker_sha256'],'checker SHA')
 global HEAD,BRANCH,HELPER
 HEAD=a.head;BRANCH=spec['branch'];HELPER=spec['recorder_sha256']
 need(spec['head']==HEAD,'spec HEAD');need(digest(a.baseline)==spec['baseline_registry_sha256'],'actual baseline registry pin')
 for p,h in spec['bindings'].items():need(digest(r/p)==h,'current source binding '+p)
 import importlib.util
 modspec=importlib.util.spec_from_file_location('support_source_chain',Path(__file__).with_name('check-source-chain-v4.py'));mod=importlib.util.module_from_spec(modspec);modspec.loader.exec_module(mod)
 source_result=mod.check(r,spec)
 need(spec['baseline_head']=='48ca57cd497a3dcebbeedeb2d54ef3bcefdcd937','growth baseline')
 need(gate_bindings_valid(r,a,spec),'three exact-head gate inputs')
 c2=next(x for x in load(r/'docs/contracts/online-book-v1/coverage.json')['chapters'] if x['chapter']==2)
 need(c2['accepted'] is False and c2['mandatory_count'] is None and c2['status'].startswith('partial'),'C2 boundary');need(c2['required_open_forward_containers']==7 and c2['required_future_mathematical_claims_open_unenumerated']==6,'7+6')
 gate=load(a.gate);need(digest(a.gate)==a.gate_sha256,'gate SHA');need(gate['actual_exit']==0 and gate['capture_integrity_ok'] is True and gate['command_started'] is True,'successful actual full gate');need('tools/bandit.py' in gate['argv'] and 'check' in gate['argv'],'full harness argv')
 for k in ['pre_git','post_git']:need(gate[k]['HEAD']==HEAD and gate[k]['branch']==BRANCH and gate[k]['status_porcelain_v1_z_hex']=='','gate clean HEAD')
 need(Path(gate['cwd']).resolve()==r,'gate cwd');namespace=Path(gate['actual_evidence_namespace']).resolve();need(namespace==(r/gate['evidence_namespace_excluded']).resolve() and r in namespace.parents,'namespace')
 d=a.gate.parent
 for name in ['pre-source-inputs.json','post-source-inputs.json','pre-selected-ZIP-inputs.json','pre-selected-source-raw.zip','stdout.raw','stderr.raw']:need(digest(d/name)==gate[name+'_sha256'],'artifact '+name)
 helper=d/'capture-helper.py.txt';need(digest(helper)==HELPER==gate['helper_sha256'],'recorder pin')
 scope={'__name__':'b4_inventory_only','__file__':str(helper)};exec(compile(helper.read_bytes(),str(helper),'exec'),scope)
 current=scope['inventory'](r,namespace,gate['owned_source']);pre=load(d/'pre-source-inputs.json');post=load(d/'post-source-inputs.json');need(current==pre==post,'complete current RAW set/bytes')
 raw={x['path']:x for x in current};need(len(raw)==len(current),'duplicate RAW');sel=load(d/'pre-selected-ZIP-inputs.json');need(sel==[x for x in current if scope['selected_for_zip'](x['path'],gate['leaf_contract_roots'])],'complete selected set');sm={x['path']:x for x in sel};need(len(sm)==len(sel),'duplicate selected')
 need(gate['full_RAW_inventory_files']==len(current) and gate['ZIP_selected_files']==len(sel),'inventory counts')
 with zipfile.ZipFile(d/'pre-selected-source-raw.zip') as z:
  need(len(z.namelist())==len(set(z.namelist())) and set(z.namelist())==set(sm),'ZIP complete member set')
  for p,row in sm.items():
   b=z.read(p);need(hashlib.sha256(b).hexdigest()==row['raw_sha256']==raw[p]['raw_sha256'] and len(b)==row['bytes'],'ZIP member '+p)
  for p in GOV:need(p in raw and p in sm and z.read(p)==(r/p).read_bytes(),'governance RAW ZIP '+p)
 oldreg=load(a.baseline);reg=load(a.site/'books/registry.json');om={x['id']:x for x in oldreg['nodes']};nm={x['id']:x for x in reg['nodes']}
 unique='declaration:BanditRL.OnlineGradientDescent.project_existsUnique'
 need(len(om)==len(oldreg['nodes'])==11107 and len(nm)==len(reg['nodes'])==11108,'registry counts/unique IDs')
 need(all(nm.get(k)==v for k,v in om.items()),'old 11105 registry whole objects changed')
 need(set(nm)-set(om)=={'declaration:BanditRL.OnlineConvex.stronglyConvex_support_growth'},'only main projection and reviewed growth theorem added to baseline')
 graph=load(a.site/'lean-graph/graph.json');search=load(a.site/'lean-graph/search-index.json');need(search['schema_version']==3,'schema3 preserved')
 gn={v['id']:v for v in graph['nodes']};need(len(gn)==len(graph['nodes']),'unique graph IDs');seen=set();shards={}
 for entry in search['entries']:
  need(len(entry) in (4,6) and entry[0] not in seen and entry[0] in gn,'search entry shape/unique ID');seen.add(entry[0]);node=gn[entry[0]]
  need(type(entry[1]) is int and type(entry[2]) is int and type(entry[3]) is int,'dictionary indices')
  need(0<=entry[1]<len(search['kinds']) and 0<=entry[2]<len(search['statuses']) and 0<=entry[3]<len(search['shards']),'dictionary bounds')
  need(search['kinds'][entry[1]]==node['kind'] and search['statuses'][entry[2]]==node['status'],'decoded kind/status')
  shardpath=search['shards'][entry[3]];need(not Path(shardpath).is_absolute() and '..' not in Path(shardpath).parts,'safe shard path')
  if shardpath not in shards:shards[shardpath]={v['id'] for v in load(a.site/'lean-graph'/shardpath)['nodes']}
  need(entry[0] in shards[shardpath] and node['shard']==shardpath,'exact shard resolves node')
 need(seen==set(gn),'search exact complete graph ID set')
 books=load(r/'website/content/books.json')['books'];chapters=load(r/'website/content/chapters.json')['chapters'];owners={}
 for book in books:
  if book['status']=='source-mapped':
   for ref in book['chapter_refs']:
    if ref.startswith('teaching:') and any('teaching:'+c['slug']==ref for c in chapters):owners.setdefault(ref,book['id'])
 need(sum(v=='bandit' for v in owners.values())==10,'Bandit own 10 routes');need(owners.get('teaching:online-ogd')=='online-learning','OGD owned by Online')
 manifest=load(a.site/'site-manifest.json')
 for doc in [manifest,reg]:need(doc['source_commit']==HEAD and doc['lean_verified'] is True,'site HEAD/lean_verified')
 need(manifest['source_dirty'] is False and manifest['declaration_count']==11108,'site clean/count')
 need(nm['declaration:'+NAME]['status']=='compiled','B4 node compiled')
 need(nm[unique]['status']=='compiled','new unique-projection node compiled')
 need(nm['declaration:'+GROWTH]['status']=='compiled','conditional-growth node compiled')
 need(nm['declaration:BanditRL.OnlineConvex.stronglyConvex_support_growth']['status']=='compiled','support node compiled')
 need(r/'tmp' in a.site.resolve().parents,'isolated tmp site')
 html=(a.site/'chapters/online-ogd/index.html').read_text(encoding='utf-8')
 for book_id in ['bandit','reinforcement-learning','online-learning','conformal-prediction']:need('../../books/'+book_id+'/index.html' in html,'four Book landing link '+book_id)
 need(scope['inventory'](r,namespace,gate['owned_source'])==current,'post-QA complete RAW reenumeration')
 return {'status':'passed structural QA only','source_chain':source_result,'old_registry_nodes_preserved':11107,'new_support_ID':'declaration:BanditRL.OnlineConvex.stronglyConvex_support_growth','RAW_rows':len(current),'ZIP_rows':len(sel),'schema3_nodes_decoded':len(seen),'book_ownership':owners,'gate_sha256':digest(a.gate),'site_registry_sha256':digest(a.site/'books/registry.json')}

if __name__=='__main__':
 p=argparse.ArgumentParser()
 for x in ['root','baseline','site','gate','spec','output']:p.add_argument('--'+x,type=Path,required=True)
 for x in ['spec-sha256','gate-sha256','head']:p.add_argument('--'+x,required=True)
 a=p.parse_args();r=a.root.resolve();out=a.output.resolve();allowed=r/'tmp/online-support-reader-tool-preparation-20261012';need(allowed in out.parents,'output confined to QA namespace');need(not out.exists(),'create-only output');pre=state(r);result={'argv':sys.argv,'python':sys.version,'checker_sha256':digest(Path(__file__)),'pre_git':pre};code=1
 try:
  spec=load(a.spec);need(pre=={'HEAD':a.head,'branch':spec['branch'],'status_porcelain_v1_z_hex':''},'current clean target HEAD');result.update(check(a));code=0
 except Exception as e:result.update(status='failed',error=repr(e))
 post=state(r);result['post_git']=post;result['input_git_unchanged']=post==pre
 if post!=pre:result.update(status='failed',error='Git changed during QA');code=1
 result['actual_exit']=code
 with out.open('x',encoding='utf-8',newline='\n') as f:json.dump(result,f,ensure_ascii=False,indent=2);f.write('\n')
 print(json.dumps({'output':str(out),'sha256':digest(out),'actual_exit':code}));sys.exit(code)
