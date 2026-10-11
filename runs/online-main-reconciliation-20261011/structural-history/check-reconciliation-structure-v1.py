"""Read-only B4 structural QA; create-only ignored result; no builds or source edits."""
import argparse, copy, hashlib, json, subprocess, zipfile, sys, re
from pathlib import Path
HEAD=None
BRANCH=None
HELPER='bafe784fad8810f866105ffd19e3504f70ebf1e28949611549d584630a5b7ce8'
NAME='BanditRL.OnlineCumulativePotential.finite_regret_identity'
GOV=['README.md','AGENTS.md','CONTRIBUTING.md','docs/contribution-contract.schema.json','docs/contributor-codex-contract.md','docs/theorem-publication-protocol.md','docs/contracts/online-book-v1/coverage.json','docs/proof-digestion-protocol.md','docs/evidence-routed-memory-protocol.md','docs/openai-math-assimilation-protocol.md','research-wiki/openai-math-2026-intake.json','runs/process_memory.json']
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_bytes())
def need(b,s):
 if not b:raise ValueError(s)
def git(r,*a):return subprocess.check_output(['git',*a],cwd=r)
def state(r):return {'HEAD':git(r,'rev-parse','HEAD').decode().strip(),'branch':git(r,'branch','--show-current').decode().strip(),'status_porcelain_v1_z_hex':git(r,'status','--porcelain=v1','-z').hex()}
def check(a):
 r=a.root.resolve();spec=load(a.spec);need(digest(a.spec)==a.spec_sha256,'spec SHA');need(spec['ready_for_execution'] is True,'prepared spec is not executable');need(digest(Path(__file__))==spec['checker_sha256'],'checker SHA')
 global HEAD,BRANCH,HELPER
 HEAD=a.head;BRANCH=spec['branch'];HELPER=spec['recorder_sha256']
 need(spec['head']==HEAD,'spec HEAD');need(digest(a.baseline)==spec['baseline_registry_sha256'],'actual baseline registry pin')
 for p,h in spec['bindings'].items():need(digest(r/p)==h,'current source binding '+p)
 need(spec['baseline_head']=='7b372d79fcd3228d8d2cece73ad0181f94a70cf1','old reviewed source HEAD')
 oldcore=git(r,'show',spec['baseline_head']+':BanditRLProof/OnlineGradientDescent.lean').decode('utf8')
 core=(r/'BanditRLProof/OnlineGradientDescent.lean').read_text(encoding='utf8')
 start=core.index('/-- Every nonempty closed convex domain has a unique nearest point')
 end=core.index('/-- The unique nearest point',start)
 addition=core[start:end];need(addition.count('\n')==17,'exact 17-line projection addition')
 need((core[:start]+core[end:]).rstrip()==oldcore.rstrip(),'old OGD source altered beyond new exact block')
 maincore=git(r,'show','f07aa9a2a5df241087ffab1c3579d1b59d8bf6f6:BanditRLProof/OnlineGradientDescent.lean').decode('utf8')
 ms=maincore.index('/-- Every nonempty closed convex domain has a unique nearest point');me=maincore.index('/-- The unique nearest point',ms)
 need(addition==maincore[ms:me],'addition exact accepted main code')
 # Old semantic objects may only change through separately approved exact pairs.
 allowed={(x['kind'],x['id']):x for x in spec['allowed_old_object_deltas']};used=set()
 def preserve(kind,key,old,new):
  if old==new:return
  pair=allowed.get((kind,key));need(pair is not None,'unreviewed old object change '+kind+':'+key)
  encode=lambda x:hashlib.sha256(json.dumps(x,sort_keys=True,ensure_ascii=False,separators=(',',':')).encode()).hexdigest()
  need(pair['before_sha256']==encode(old) and pair['after_sha256']==encode(new),'approved exact old object pair');used.add((kind,key))
 for filename,field,key in [('readings.json','readings','slug'),('highlights.json','highlights','full_name')]:
  old=load_json_bytes= json.loads(git(r,'show',spec['baseline_head']+':website/content/'+filename));new=load(r/('website/content/'+filename))
  nm={x[key]:x for x in new[field]};need(len(nm)==len(new[field]),'unique content IDs')
  for row in old[field]:
   need(row[key] in nm,'old reader object dropped')
   if field=='highlights':preserve('highlight',row[key],row,nm[row[key]])
   else:
    for label in ['source_theorem','source_theorems']:
     cards=row.get(label,[]);cards=cards if isinstance(cards,list) else [cards]
     fresh=nm[row[key]].get(label,[]);fresh=fresh if isinstance(fresh,list) else [fresh]
     for card in cards:
      if not card:continue
      matches=[v for v in fresh if v.get('label')==card.get('label')];need(len(matches)==1,'old source card lost/duplicated')
      preserve('card',row[key]+':'+str(card.get('label')),card,matches[0])
 need(used==set(allowed),'unused old-object delta permissions')
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
 need(len(om)==len(oldreg['nodes'])==11105 and len(nm)==len(reg['nodes'])==11106,'registry counts/unique IDs')
 need(all(nm.get(k)==v for k,v in om.items()),'old 11105 registry whole objects changed')
 need(set(nm)-set(om)=={unique},'sole new main projection theorem')
 graph=load(a.site/'lean-graph/graph.json');search=load(a.site/'lean-graph/search-index.json');need(search['schema_version']==3,'schema3 preserved')
 gn={v['id']:v for v in graph['nodes']};seen=set();shards={}
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
 need(manifest['source_dirty'] is False and manifest['declaration_count']==11106,'site clean/count')
 need(nm['declaration:'+NAME]['status']=='compiled','new node status')
 oldlines={m.group(2):oldcore[:m.start()].count('\n')+1 for m in re.finditer(r'^(theorem|def|structure) (\w+)',oldcore,re.M)}
 newlines={m.group(2):core[:m.start()].count('\n')+1 for m in re.finditer(r'^(theorem|def|structure) (\w+)',core,re.M)}
 need(set(newlines)-set(oldlines)=={'project_existsUnique'},'exact unique declaration insertion')
 for name,line in oldlines.items():need(newlines[name]==line+(17 if line>oldcore[:start].count('\n') else 0),'exact old declaration line shift '+name)
 modulehtml=(a.site/'modules/banditrlproof-onlinegradientdescent/index.html').read_text(encoding='utf8')
 for name,line in newlines.items():need(f'/blob/{HEAD}/BanditRLProof/OnlineGradientDescent.lean#L{line}' in modulehtml,'actual generated source link '+name)
 need(scope['inventory'](r,namespace,gate['owned_source'])==current,'post-QA complete RAW reenumeration')
 return {'status':'passed structural QA only' ,'old_registry_nodes_preserved':11105,'new_production_ID':unique,'OGD_inserted_lines':17,'approved_old_object_deltas_used':list(used),'governance_RAW_ZIP_verified':GOV,'RAW_rows':len(current),'ZIP_rows':len(sel),'schema3_nodes_decoded':len(seen),'book_ownership':owners,'chapter2':'partial','open_containers':7,'future_claims':6,'proof_denominator':None,'gate_sha256':digest(a.gate),'site_manifest_sha256':digest(a.site/'site-manifest.json'),'site_registry_sha256':digest(a.site/'books/registry.json')}
if __name__=='__main__':
 p=argparse.ArgumentParser()
 for x in ['root','baseline','site','gate','spec','output']:p.add_argument('--'+x,type=Path,required=True)
 for x in ['spec-sha256','gate-sha256','head']:p.add_argument('--'+x,required=True)
 a=p.parse_args();r=a.root.resolve();out=a.output.resolve();allowed=r/'tmp/online-main-reconciliation-structural-qa-20261011';need(allowed in out.parents,'output confined to QA namespace');need(not out.exists(),'create-only output');pre=state(r);result={'argv':sys.argv,'python':sys.version,'checker_sha256':digest(Path(__file__)),'pre_git':pre};code=1
 try:
  spec=load(a.spec);need(pre=={'HEAD':a.head,'branch':spec['branch'],'status_porcelain_v1_z_hex':''},'current clean target HEAD');result.update(check(a));code=0
 except Exception as e:result.update(status='failed',error=repr(e))
 post=state(r);result['post_git']=post;result['input_git_unchanged']=post==pre
 if post!=pre:result.update(status='failed',error='Git changed during QA');code=1
 result['actual_exit']=code
 with out.open('x',encoding='utf-8',newline='\n') as f:json.dump(result,f,ensure_ascii=False,indent=2);f.write('\n')
 print(json.dumps({'output':str(out),'sha256':digest(out),'actual_exit':code}));sys.exit(code)
