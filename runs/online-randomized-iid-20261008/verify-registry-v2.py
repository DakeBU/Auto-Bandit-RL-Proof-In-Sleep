from common_integrated_v2 import *
from html.parser import HTMLParser

fixed_integrated()
site=Path('tmp/online-randomized-iid-site-v2')
r,m,old=load(site/'books/registry.json'),load(site/'site-manifest.json'),load(RUN/'registry-base-snapshot-v2.json')
assert r['lean_verified'] and m['lean_verified'] and not m['source_dirty']
assert r['source_commit']==m['source_commit']
nodes={x['id']:x for x in r['nodes']};base={x['id']:x for x in old['nodes']}
assert len(base)==10923 and r['identity']==old['identity']
assert all(i in nodes and nodes[i]['url']==n['url'] and nodes[i].get('statement_sha256')==n.get('statement_sha256') for i,n in base.items())
production=load(MANIFEST)['declarations']
assert len(production)==8
assert set(nodes)-set(base)=={'declaration:'+n for n in production}
assert len(nodes)==10931
bindings={x['name']:x for x in load(RUN/'full-fence-bindings-v2.json')}
for name in production:
    node=nodes['declaration:'+name]
    assert node['status']=='compiled' and 'online-learning' in node['books'] and 'teaching:online-foundations' in node['chapters'],name
    if name in bindings: assert node['statement_sha256']==bindings[name]['statement_hash'],name
assert not any(TEST in node['id'] for node in r['nodes'])

class ReaderText(HTMLParser):
    def __init__(self): super().__init__();self.text=[];self.hrefs=[]
    def handle_data(self,data): self.text.append(data)
    def handle_starttag(self,tag,attrs):
        if tag=='a': self.hrefs.extend(v for k,v in attrs if k=='href')

reader=site/'chapters/online-foundations/index.html'
parsed=ReaderText();parsed.feed(reader.read_text(encoding='utf8'));text=''.join(parsed.text)
reading=next(x for x in load('website/content/readings.json')['readings'] if x['slug']==ROUTE)
assert len(reading['source_theorems'])==13 and len(reading['teaching_route'])==4
notes=[x for x in load('website/content/highlights.json')['highlights'] if x['full_name'] in production]
assert len(notes)==7
for name in reading['teaching_route']+[x['full_name'] for x in notes]:
    assert name in text and '../../'+nodes['declaration:'+name]['url'] in parsed.hrefs,name
for phrase in ['WHOLE infinite target process','strict-past','F_t contained in H_t','EVERY seed',
        'a.s.','outside expectation','same probability law','subordinate-information',
        'XOR','two-round expected excess is1/2','42 theorem-kind','Native safe scans do not compile',
        'not seven printed source statements','asymptotic-success equivalence','unknown(null)',
        'five old main-relative','totalGoalACTIVE','OPENdraft/unmergedPR194','canonicalmain6847']:
    assert phrase in text,phrase
module_path=nodes['declaration:'+PRE+'randomized_history_policy_expectedFixed_excess']['url'].split('#')[0]
module=site/module_path;parsed=ReaderText();parsed.feed(module.read_text(encoding='utf8'));module_text=''.join(parsed.text)
for name in production: assert name in module_text,name
sys.path.insert(0,str(ROOT))
from tools.abrl_lifecycle import normalize_statement
headers={x['name']:x['header'] for x in load(RUN/'actual-public-canary-headers-v2.json') if x['path']==PUBLIC.as_posix()}
assert len(headers)==7
for name,header in headers.items():
    assert normalize_statement(header) in ' '.join(module_text.split()),name
    assert normalize_statement(header) in ' '.join(text.split()),name
source_url='https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/blob/'+m['source_commit']+'/'+PUBLIC.as_posix()
assert any(href.startswith(source_url+'#L') for href in parsed.hrefs)
write(RUN/'registry-v2.json',dict(status='passed',source_commit=m['source_commit'],source_dirty=False,lean_verified=True,
    registry_sha256=sha(site/'books/registry.json'),registry_path=(site/'books/registry.json').as_posix(),identity=r['identity'],
    preserved_base_IDs_URLs_statement_hashes=10923,new_registry_nodes=8,total_registry_nodes=10931,
    new_public_proofs=7,new_public_definitions=1,source_cards=13,new_source_cards=1,new_proof_notes=7,
    curated_links_preserved=4,source_route_HTML_sha256=sha(reader),module_HTML_sha256=sha(module),module_path=module_path,
    seven_actual_headers_present=True,same_shared_registry=True,named_canaries=29,
    private_seed_subordinate_information_finite_producer_closed=True,full_source_kernel_and_asymptotic_coverage_required=True,
    chapter_complete=False,goal_complete=False))
print('10923 prior registry IDs/URLs/statement hashes preserved; eight new shared nodes; exact seven note/catalogue headers present.')
