from common_integrated_v1 import *
from html.parser import HTMLParser
fixed_integrated()
site=Path('tmp/online-log-lower-site-v1');r=load(site/'books/registry.json');m=load(site/'site-manifest.json');old=load(RUN/'registry-base-snapshot-v1.json')
assert r['lean_verified'] and m['lean_verified'] and not m['source_dirty'] and r['source_commit']==m['source_commit']
nodes={n['id']:n for n in r['nodes']};base={n['id']:n for n in old['nodes']}
assert len(base)==10835 and r['identity']==old['identity']
assert all(i in nodes and nodes[i]['url']==n['url'] and nodes[i].get('statement_sha256')==n.get('statement_sha256') for i,n in base.items())
production=load(MANIFEST)['declarations'];added=set(nodes)-set(base)
private_id='declaration:'+PRE+'vectorConsEquiv'
assert added=={'declaration:'+n for n in production}|{private_id},sorted(added)
assert nodes[private_id]['identity_basis']=='source-private-name'
assert len(added)==59 and len(nodes)==10894
bindings={x['name']:x for x in load(RUN/'full-fence-bindings-v1.json')}
for name in production:
 node=nodes['declaration:'+name];assert node['status']=='compiled'
 assert 'online-learning' in node['books'] and 'teaching:online-foundations' in node['chapters'],name
 if name in bindings:assert node['statement_sha256']==bindings[name]['statement_hash'],name
assert not any(TEST in n['id'] for n in r['nodes'])
class ReaderText(HTMLParser):
 def __init__(self):super().__init__();self.text=[];self.hrefs=[]
 def handle_data(self,data):self.text.append(data)
 def handle_starttag(self,tag,attrs):
  if tag=='a':self.hrefs.extend(v for k,v in attrs if k=='href')
reader=site/'chapters/online-foundations/index.html';parsed=ReaderText();parsed.feed(reader.read_text(encoding='utf8'));text=''.join(parsed.text)
reading=next(x for x in load('website/content/readings.json')['readings'] if x['slug']==ROUTE)
assert len(reading['source_theorems'])==9 and len(reading['teaching_route'])==4
notes=[x for x in load('website/content/highlights.json')['highlights'] if x['full_name'] in production];assert len(notes)==7
for name in reading['teaching_route']+[x['full_name'] for x in notes]:
 assert name in text and '../../'+nodes['declaration:'+name]['url'] in parsed.hrefs,name
for phrase in ['no minimax-optimality proof','neither printed nor claimed sharp','newest-first binary lists','neither learner policy nor seed','Source round1 is Lean0','every probability measure','every seed and every history','ONE binary vector','genuinely integrable','absolute value at most T','finite weighted sum/integral interchange','expected optimum is (T-1)/6','T0','signed cumulative regret','no main/live','mandatory proof total unknown(null)','Total Goal ACTIVE']:
 assert phrase in text,phrase
module_path=nodes['declaration:'+PRE+'randomized_log_lower']['url'].split('#')[0];module=site/module_path
parsed=ReaderText();parsed.feed(module.read_text(encoding='utf8'));mt=''.join(parsed.text)
for name in production:assert name in mt,name
sys.path.insert(0,str(ROOT));from tools.abrl_lifecycle import normalize_statement
headers={x['name']:x['header'] for x in load(RUN/'actual-public-canary-headers-v1.json') if x['path']==PUBLIC.as_posix()}
assert len(headers)==48
for name,h in headers.items():assert normalize_statement(h) in ' '.join(mt.split()),name
for name in [PRE+'randomized_harmonic_lower',PRE+'randomized_log_lower']:
 assert normalize_statement(headers[name]) in ' '.join(text.split()),name
source_url='https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/blob/'+m['source_commit']+'/'+PUBLIC.as_posix()
assert any(h.startswith(source_url+'#L') for h in parsed.hrefs)
assert sha(PUBLIC)==load(RUN/'body-bindings-v1.json')['public_sha256']
write(RUN/'registry-v2.json',dict(status='passed',source_commit=m['source_commit'],source_dirty=False,lean_verified=True,registry_sha256=sha(site/'books/registry.json'),registry_path=(site/'books/registry.json').as_posix(),identity=r['identity'],preserved_base_node_IDs_URLs_and_hashes=10835,new_registry_nodes=59,total_registry_nodes=10894,new_public_nodes=58,new_private_source_nodes=1,private_source_identity_basis=nodes[private_id]['identity_basis'],new_proofs=48,new_definitions=10,source_cards=9,new_source_cards=1,new_public_notes=7,curated_links_preserved=4,source_route_HTML_sha256=sha(reader),module_HTML_sha256=sha(module),module_path=module_path,same_shared_registry=True,named_canaries=16,module_all48_exact_headers_present=True,randomized_reader_full_exact_headers_present=True,compiled_complete_proof_source_bound=True,generated_exact_proof_code_disclosure=False,chapter_complete=False,goal_complete=False))
print('10835old IDsURLsstatementhashes preserved;58newactual public nodes plus1explicit private source node;48complete headers and randomized reader assumptions verified.')
