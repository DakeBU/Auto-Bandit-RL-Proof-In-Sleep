from common_v1 import *
from html.parser import HTMLParser
fixed(proving=True,integrated=True)
site=Path('tmp/online-ftl-state-site-v4');r=load(site/'books/registry.json');m=load(site/'site-manifest.json');old=load(RUN/'registry-base-snapshot-v1.json')
assert r['lean_verified'] and m['lean_verified'] and not m['source_dirty'] and r['source_commit']==m['source_commit']
nodes={n['id']:n for n in r['nodes']};base={n['id']:n for n in old['nodes']};proofs=list(load(CONTRACT/'new-public-headers-v1.json'));defs=['ftlPredict','ftlMeanStep','ftlState'];expected={'declaration:'+PRE+n for n in proofs+defs}
assert len(nodes)==10835 and len(base)==10823 and set(nodes)-set(base)==expected and set(base)<=set(nodes) and r['identity']==old['identity']
assert all(nodes[i]['url']==n['url'] and nodes[i].get('statement_sha256')==n.get('statement_sha256') for i,n in base.items())
bindings={x['name']:x for x in load(RUN/'full-fence-bindings-v1.json')};new=[]
for key in sorted(expected):
 node=nodes[key];name=key[len('declaration:'):];assert node['status']=='compiled'
 if name in bindings:assert node['statement_sha256']==bindings[name]['statement_hash']
 assert 'online-learning' in node['books'] and 'teaching:online-foundations' in node['chapters']
 new.append(dict(id=key,url=node['url'],statement_sha256=node['statement_sha256'],native_full_theorem_fence=name in bindings))
x=next(a for a in load('website/content/readings.json')['readings'] if a['slug']=='online-foundations');assert len(x['source_theorems'])==7 and len(x['teaching_route'])==4
class ReaderText(HTMLParser):
 def __init__(self):super().__init__();self.text=[];self.hrefs=[]
 def handle_data(self,data):self.text.append(data)
 def handle_starttag(self,tag,attrs):
  if tag=='a':self.hrefs.extend(v for k,v in attrs if k=='href')
parsed=ReaderText();html=site/'chapters/online-foundations/index.html';parsed.feed(html.read_text(encoding='utf-8'));text=''.join(parsed.text)
for name in x['teaching_route']+[PRE+n for n in proofs]:assert name in text and '../../'+nodes['declaration:'+name]['url'] in parsed.hrefs,name
for phrase in ['Fix initial c before observations','strict-past','printed pp.3,6','noncomputable exact-real','first recursive update cancels c','loss1>1/4','logarithmic lower-bound','Chapter 1 remains open']:assert phrase in text,phrase
module=site/'modules/banditrlproof-onlinelearningftlstate/index.html';q=ReaderText();q.feed(module.read_text(encoding='utf-8'));mt=''.join(q.text)
for n in proofs[1:]+defs:assert PRE+n in mt,n
for phrase in ['| 0 => (0, initial)','| t + 1 => ftlMeanStep (ftlState initial y t) (y t)','(h : ∀ i < t, y i = z i)','(hi : initial ∈ Set.Icc (0 : ℝ) 1)']:assert phrase in mt,phrase
write(RUN/'registry-v4.json',dict(status='passed',source_commit=m['source_commit'],source_dirty=False,lean_verified=True,registry_sha256=sha(site/'books/registry.json'),registry_path=(site/'books/registry.json').as_posix(),identity=r['identity'],preserved_base_node_IDs_URLs_and_hashes=10823,new_registry_nodes=12,total_registry_nodes=10835,new_nodes=new,source_cards=7,new_source_cards=1,new_public_notes=9,curated_links_preserved=4,source_route_HTML_sha256=sha(html),module_HTML_sha256=sha(module),same_shared_registry=True,new_named_validation_proofs=6,new_public_math=9,new_public_definitions=3,source_subobligations=2,recursive_native_fence_claim=False,full_recursive_definition_in_actual_HTML=True,chapter_complete=False,goal_complete=False))
print('Same10823 old IDsURLs/source-presentation-hashes +12new nodes (9proofs3defs), shared10835 PASS.')

current={x['id']:x for x in new};prior={x['id']:x for x in load(RUN/'registry-v3.json')['new_nodes']}
assert set(current)==set(prior)
changed=[k for k in current if current[k]['statement_sha256']!=prior[k]['statement_sha256']]
assert changed==['declaration:'+PRE+'ftlState']
sys.path.insert(0,str(ROOT))
from website.scripts import build_site as scanner
module_current=scanner.scan_module(PUBLIC)
stmt=next(x['statement'] for x in module_current['declarations'] if x['full_name']==PRE+'ftlState')
assert 'theorem' not in stmt and '| 0 => (0, initial)' in stmt and '| t + 1 => ftlMeanStep' in stmt
assert nodes['declaration:'+PRE+'ftlState']['statement_sha256']==hashlib.sha256(stmt.encode()).hexdigest()
write(RUN/'registry-boundary-repair-v4.json',dict(status='passed',changed_new_node=changed,all_other11_new_hashes_unchanged=True,all10823_old_ID_URL_statement_hashes_exact=True,complete_source_definition_presentation=stmt,native_definition_fence=False))
