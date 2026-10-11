"""Read-only B4 structural QA; create-only ignored result; no builds or source edits."""
import argparse, copy, hashlib, json, subprocess, zipfile, sys
from pathlib import Path
HEAD='7b372d79fcd3228d8d2cece73ad0181f94a70cf1'
BRANCH='codex/research-online-ch2-b4-finite-identity'
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
 r=a.root.resolve(); need(a.baseline.resolve()==(r/'runs/online-ch2-b4-finite-identity-20261011/integration-baseline').resolve(),'actual baseline must be canonical pinned baseline'); spec=load(a.spec);need(digest(a.spec)==a.spec_sha256,'spec SHA');need(digest(Path(__file__))==spec['checker_sha256'],'checker SHA')
 for p,h in spec['bindings'].items():need(digest(r/p)==h,'input pin '+p)
 for path,imp in [('BanditRLProof.lean','import BanditRLProof.OnlineCumulativePotential'),('Tests.lean','import Tests.OnlineCumulativePotentialCanary')]:need((r/path).read_text(encoding='utf-8').splitlines().count(imp)==1,'exact single import '+path)
 old={k:load(a.baseline/(k+'.json')) for k in ['chapters','readings','highlights']};new={k:load(r/('website/content/'+k+'.json')) for k in old};rest=copy.deepcopy(new)
 ch=next(x for x in rest['chapters']['chapters'] if x['slug']=='online-ogd');need(ch['module_globs'].count('BanditRLProof/OnlineCumulativePotential.lean')==1,'module glob once');ch['module_globs'].remove('BanditRLProof/OnlineCumulativePotential.lean')
 rd=next(x for x in rest['readings']['readings'] if x['slug']=='online-ogd');need(len(rd['source_theorems'])==23,'23 cards');card=rd['source_theorems'].pop();need(card['label']=='Corrected terminal accounting: the finite-real regret identity','new card identity');need(len(rd['source_theorems'])==22,'22 old cards')
 hi=rest['highlights']['highlights'];need(sum(x['full_name']==NAME for x in hi)==1,'one new highlight');lesson=hi.pop();need(lesson['full_name']==NAME,'appended highlight');need(rest==old,'old whole parsed objects changed')
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
 oldreg=load(a.baseline/'previous-registry-v1.json');reg=load(a.site/'books/registry.json');om={x['id']:x for x in oldreg['nodes']};nm={x['id']:x for x in reg['nodes']}
 need(len(om)==len(oldreg['nodes'])==11104 and len(nm)==len(reg['nodes'])==11105,'registry counts/unique IDs');need(all(nm.get(k)==v for k,v in om.items()),'old 11104 whole nodes changed');need(set(nm)-set(om)=={'declaration:'+NAME},'exact sole new production ID')
 manifest=load(a.site/'site-manifest.json')
 for doc in [manifest,reg]:need(doc['source_commit']==HEAD and doc['lean_verified'] is True,'site HEAD/lean_verified')
 need(manifest['source_dirty'] is False and manifest['declaration_count']==11105,'site clean/count')
 need(nm['declaration:'+NAME]['status']=='compiled','new node status')
 return {'status':'passed structural QA only','old_registry_nodes_preserved':11104,'new_production_ID':'declaration:'+NAME,'source_cards':23,'old_cards_preserved':22,'governance_RAW_ZIP_verified':GOV,'RAW_rows':len(current),'ZIP_rows':len(sel),'chapter2':'partial','open_containers':7,'future_claims':6,'proof_denominator':None,'Goal_scope':'Not queried; no Goal completion inferred','gate_sha256':digest(a.gate),'site_manifest_sha256':digest(a.site/'site-manifest.json'),'site_registry_sha256':digest(a.site/'books/registry.json')}
if __name__=='__main__':
 p=argparse.ArgumentParser()
 for x in ['root','baseline','site','gate','spec','output']:p.add_argument('--'+x,type=Path,required=True)
 for x in ['spec-sha256','gate-sha256']:p.add_argument('--'+x,required=True)
 a=p.parse_args();r=a.root.resolve();out=a.output.resolve();allowed=r/'tmp/online-ch2-b4-finite-identity-structural-qa-20261011';need(allowed in out.parents,'output confined to QA namespace');need(not out.exists(),'create-only output');pre=state(r);result={'argv':sys.argv,'python':sys.version,'checker_sha256':digest(Path(__file__)),'pre_git':pre};code=1
 try:
  need(pre=={'HEAD':HEAD,'branch':BRANCH,'status_porcelain_v1_z_hex':''},'current clean target HEAD');result.update(check(a));code=0
 except Exception as e:result.update(status='failed',error=repr(e))
 post=state(r);result['post_git']=post;result['input_git_unchanged']=post==pre
 if post!=pre:result.update(status='failed',error='Git changed during QA');code=1
 result['actual_exit']=code
 with out.open('x',encoding='utf-8',newline='\n') as f:json.dump(result,f,ensure_ascii=False,indent=2);f.write('\n')
 print(json.dumps({'output':str(out),'sha256':digest(out),'actual_exit':code}));sys.exit(code)
