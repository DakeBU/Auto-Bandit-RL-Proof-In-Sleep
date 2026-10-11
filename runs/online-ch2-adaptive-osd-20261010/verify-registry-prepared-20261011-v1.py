from delivery_guard_20261011_v1 import *
a=arguments();fixed(a);binding=load(RUN/('site-binding-'+a.tag+'.json'));site=Path(binding['site']);same_binding(binding['source_binding'])
c=CONFIG['registry_compressed'];assert sha(c['path'])==c['sha256']
raw=gzip.decompress(Path(c['path']).read_bytes());old=json.loads(raw)
assert hashlib.sha256(raw).hexdigest()==CONFIG['registry_baseline']['registry']['sha256']
current=load(site/'books/registry.json');manifest=load(site/'site-manifest.json')
assert current['source_commit']==manifest['source_commit']==binding['head'] and current['lean_verified'] and manifest['lean_verified']
assert current['identity']==old['identity']
ob={n['id']:n for n in old['nodes']};nb={n['id']:n for n in current['nodes']}
assert len(ob)==len(old['nodes'])==CONFIG['registry_baseline']['nodes']
assert len(nb)==len(current['nodes'])==CONFIG['expected_total']
for key,value in ob.items(): assert nb[key]==value,key
assert set(nb)-set(ob)==set(CONFIG['new_registry_ids'])
modules={}
for key in CONFIG['new_registry_ids']:
    n=nb[key];assert n['identity_basis']=='source-qualified-name'
    url=n['url'].split('#')[0];p=site/url;assert p.is_file();modules[url]=sha(p)
assert not any('OnlineAdaptiveOSDCanary' in key or 'OnlineAdaptivePotentialCanary' in key for key in nb)
reading=next(r for r in load(ROOT/'website/content/readings.json')['readings'] if r['slug']=='online-ogd')
assert len(reading['source_theorems'])==CONFIG['expected_source_cards']
write(RUN/('registry-inspected-'+a.tag+'.json'),dict(source_commit=binding['head'],source_dirty=binding['source_dirty'],lean_verified=True,baseline_nodes=len(ob),retained_complete_old_objects=True,new_nodes=40,structural_breakdown=CONFIG['structural_counts'],total_nodes=len(nb),source_cards=len(reading['source_theorems']),module_HTML_sha256=modules,registry=rows([site/'books/registry.json']),chapter_proof_total=None,chapter_complete=False,deployed=False,pixel_review='separate required gate'))
