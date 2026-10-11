"""Read-only structural QA; run only after actual shared gate and site generation."""
from pathlib import Path
import argparse,hashlib,json,re
from html.parser import HTMLParser
from urllib.parse import urlsplit,unquote
ROOT=Path(__file__).resolve().parents[2]
OLD=ROOT/'tmp/online-ch2-adaptive-osd-site-20261011-v2'
SITE=ROOT/'tmp/online-ch2-weighted-identity-site-20261011-v1'
HEAD='c071e678cdd563a847b71e84ae3b4fc1d54faee9'
EXPECTED={'declaration:BanditRL.OnlineWeightedPotential.weighted_difference_sum_eq','declaration:BanditRL.OnlineWeightedPotential.distance_potential_sum_eq'}
def load(p):return json.loads(p.read_text(encoding='utf-8'))
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
class HTML(HTMLParser):
 def __init__(self):super().__init__();self.ids=set();self.links=[];self.text=[];self.exact=0
 def handle_starttag(self,tag,attrs):
  a=dict(attrs)
  if 'id' in a:self.ids.add(a['id'])
  if tag=='a' and 'href' in a:self.links.append(a['href'])
  if tag=='details' and 'exact-lean' in a.get('class','').split():self.exact+=1
 def handle_data(self,data):self.text.append(data)
class DeclarationFolds(HTMLParser):
 def __init__(self):super().__init__();self.blocks={};self.current=None;self.depth=0;self.in_pre=False
 def handle_starttag(self,tag,attrs):
  a=dict(attrs)
  if tag=='details':
   if self.current is not None:self.depth+=1
   elif 'declaration' in a.get('class','').split():
    self.current={'text':[],'header':[],'links':[]};self.blocks[a['id']]=self.current;self.depth=1
  if self.current is not None:
   if tag=='pre' and 'lean-code' in a.get('class','').split():self.in_pre=True
   if tag=='a' and 'href' in a:self.current['links'].append(a['href'])
 def handle_endtag(self,tag):
  if self.current is not None:
   if tag=='pre':self.in_pre=False
   if tag=='details':
    self.depth-=1
    if self.depth==0:self.current=None
 def handle_data(self,data):
  if self.current is not None:
   self.current['text'].append(data)
   if self.in_pre:self.current['header'].append(data)
def normalized(s):return re.sub(r'\s+',' ',s).strip()
def frozen_header(name):
 packet=(ROOT/'docs/contracts/online-ch2-weighted-identity-v1/neutral-frozen-headers-v1.txt').read_text(encoding='utf-8')
 start=packet.index('theorem '+name+' ');tail=packet[start:]
 return normalized(re.split(r'\n(?:theorem |end BanditRL)',tail,maxsplit=1)[0])

def parse(p):
 h=HTML();h.feed(p.read_text(encoding='utf-8'));return h
def check_local_link(page,href):
 u=urlsplit(href)
 if u.scheme or u.netloc:return
 path=(page.parent/unquote(u.path)).resolve() if u.path else page
 if path.is_dir():path=path/'index.html'
 assert path.is_file(),('missing link',href)
 if u.fragment and path.suffix=='.html':assert unquote(u.fragment) in parse(path).ids,('missing anchor',href)
a=argparse.ArgumentParser();a.add_argument('--gate-receipt',type=Path,required=True);a.add_argument('--gate-sha256',required=True);a.add_argument('--old-registry-sha256',required=True);args=a.parse_args()
assert sha(args.gate_receipt)==args.gate_sha256,'gate RAW mismatch'
gate=load(args.gate_receipt)
assert gate.get('actual_exit')==0,'actual successful shared check receipt required'
argv=gate.get('argv')
assert isinstance(argv,list) and all(isinstance(x,str) for x in argv),'actual argv array required'
assert any(x.replace('\\','/').endswith('tools/bandit.py') for x in argv) and 'check' in argv,'must bind actual tools/bandit.py check argv'
assert gate.get('capture_integrity_ok') is True,'capture integrity required'
for phase in ['pre_git','post_git']:
 git=gate.get(phase,{})
 assert git.get('HEAD')==HEAD,phase+' exact HEAD mismatch'
 assert git['status_porcelain_v1_z_hex']=='',phase+' porcelain-v1-z status must be exactly empty'
assert SITE.is_dir(),'future site is not built'
assert sha(OLD/'books/registry.json')==args.old_registry_sha256
old=load(OLD/'books/registry.json');new=load(SITE/'books/registry.json')
assert old['schema_version']==new['schema_version']==1
assert new['source_commit']==HEAD and new['lean_verified'] is True
ob={x['id']:x for x in old['nodes']};nb={x['id']:x for x in new['nodes']}
assert len(ob)==len(old['nodes'])==11098
assert len(nb)==len(new['nodes'])
assert all(k in nb and nb[k]==v for k,v in ob.items()),'old canonical registry object changed'
assert set(nb)-set(ob)==EXPECTED,'must add exactly two production IDs'
page=SITE/'chapters/online-ogd/index.html';html=parse(page);text=' '.join(html.text)
for name in EXPECTED:
 node=nb[name];assert node['status']=='compiled'
 url=node['url'];check_local_link(SITE/'index.html',url)
 module_page=SITE/url.split('#')[0];mh=parse(module_page)
 assert name[len('declaration:'):] in ' '.join(mh.text)
 exact_links=[u for u in mh.links if '/blob/'+HEAD+'/BanditRLProof/OnlineWeightedPotential.lean#L' in u]
 assert exact_links,('module full-source line link must target candidate commit',name)
 folds=DeclarationFolds();folds.feed(module_page.read_text(encoding='utf-8'))
 anchor=url.split('#',1)[1];assert anchor in folds.blocks,'exact declaration fold missing'
 block=folds.blocks[anchor];full_name=name[len('declaration:'):]
 assert full_name in ''.join(block['text']),'declaration name missing from its own fold'
 assert normalized(''.join(block['header']))==frozen_header(full_name.rsplit('.',1)[1]),'exact frozen header differs inside declaration fold'
 assert any('/blob/'+HEAD+'/BanditRLProof/OnlineWeightedPotential.lean#L' in u for u in block['links']),'own declaration fold lacks commit-pinned full-proof source link' 
assert html.exact>0
for token in ['Why changing step sizes leaves an interior correction','BanditRL.OnlineWeightedPotential.distance_potential_sum_eq','BanditRL.OnlineWeightedPotential.weighted_difference_sum_eq','NormedAddCommGroup','terminal']:
 assert token in text or token in ''.join(html.text),('missing reader detail',token)
assert any('1912.13213v10' in u and ('page=26' in u or '#page=26' in u) for u in html.links),'PDF26 anchor missing'
assert any('/blob/'+HEAD+'/BanditRLProof/OnlineWeightedPotential.lean#L' in u for u in html.links),'lesson proof-source link not pinned to candidate'
# Verify source row exact formula and old-row preservation using sealed before snapshots.
before=ROOT/'tmp/online-ch2-weighted-reader-plan-20261011/integration-candidate-v4/before'
oldread=load(before/'website/content/readings.json');cur=load(ROOT/'website/content/readings.json')
oldrow=next(x for x in oldread['readings'] if x['slug']=='online-ogd');row=next(x for x in cur['readings'] if x['slug']=='online-ogd')
added=[x for x in row['source_theorems'] if x not in oldrow['source_theorems']];assert len(added)==1
assert [x for x in row['source_theorems'] if x not in added]==oldrow['source_theorems']
card=added[0];assert card['pdf_page']==26
for token in ['x_{T+1}','2\\eta_T','\\frac12','T-1','\\eta_{t+1}']:
 assert token in card['math'],('missing exact formula component',token)
assert 'No monotonicity' in card['contract']['assumptions']
# Rendered HTML contains the same complete formula, possibly HTML-escaped in attributes.
from html import unescape
assert card['math'] in unescape(page.read_text(encoding='utf-8')),'full rendered formula drift'
oldhi=load(before/'website/content/highlights.json')['highlights'];hi=load(ROOT/'website/content/highlights.json')['highlights'];assert len(hi)==len(oldhi)+1 and hi[:-1]==oldhi
lesson=hi[-1];assert lesson['dependencies']==['BanditRL.OnlineWeightedPotential.weighted_difference_sum_eq']
assert lesson['proof_idea'] in text,'full cancellation proof missing'
coverage=next(x for x in load(ROOT/'docs/contracts/online-book-v1/coverage.json')['chapters'] if x['chapter']==2)
assert coverage['mandatory_count'] is None and coverage['accepted'] is False
assert coverage['required_open_forward_containers']==8 and coverage['required_future_mathematical_claims_open_unenumerated']==6
print(json.dumps({'status':'structural checks passed; visual/browser QA still separate','candidate_commit':HEAD,'old_registry_objects_preserved':11098,'new_production_ids':sorted(EXPECTED),'chapter_proof_denominator':None,'test_boundary':'Full ProofGraph layer may contain five Test theorems and ten support definitions; they are not new Book canonical production IDs and never a source denominator. This helper does not certify full ProofGraph graph correctness.','browser_run':False,'build_run':False,'canonical_writes':False},indent=2))
