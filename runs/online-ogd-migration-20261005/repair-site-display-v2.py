"""Repair actual source-reader display gate without removing declarations or formulas."""
from pathlib import Path
import hashlib,json
run=Path(__file__).parent
def load(p):return json.loads(Path(p).read_text(encoding='utf-8'))
def write(p,x):
    with Path(p).open('w',encoding='utf-8',newline='\n') as f:json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')
before={}
for n in ['readings','highlights']:
    p=Path('website/content/'+n+'.json');raw=p.read_bytes()
    snapshot=run/('leaves/pre-site-display-repair-'+n+'-v2.json')
    assert not snapshot.exists();snapshot.write_bytes(raw)
    before[n]=dict(path=p.as_posix(),snapshot=snapshot.as_posix(),sha256=hashlib.sha256(raw).hexdigest())
rpath=Path('website/content/readings.json');r=load(rpath)
reading=next(x for x in r['readings'] if x['slug']=='online-ogd')
assert len(reading['notation'])==5
reading['notation']=reading['notation'][:3]
reading['notation'][1]['meaning']='Gradient of the supplied ambient real extension of the current loss at x_t. On a thin V its restriction alone does not fix the full ambient gradient; extension independence is not claimed.'
assert all('arbitrary open U' in c['contract']['assumptions'] for c in reading['source_theorems'][1:])
write(rpath,r)
hpath=Path('website/content/highlights.json');h=load(hpath)
route=set(reading['teaching_route']);assert len(route)==4
for node in h['highlights']:
    if node.get('chapter')=='online-ogd':node['featured']=node['full_name'] in route
assert sum(x.get('featured') is True for x in h['highlights'] if x.get('chapter')=='online-ogd')==4
assert len([x for x in h['highlights'] if x.get('chapter')=='online-ogd'])==19
write(hpath,h)
for name in ['verify-registry','browser']:
    p=run/(name+'-final01.py')
    text=p.read_text(encoding='utf-8').replace('site-final01','site-final02').replace('reader-final01','reader-final02').replace('browser-final01','browser-final02').replace('registry-final01','registry-final02')
    with (run/(name+'-final02.py')).open('w',encoding='utf-8',newline='\n') as f:f.write(text)
record=dict(status='repair-authored',failed_gate='site-final01-check',preserved_snapshots=before,
    notation_primer_entries=3,featured_teaching_notes=4,total_OGD_notes_retained=19,
    all_old_names_and_urls_retained=True,new_source_declarations_retained=14,source_cards_retained=5,
    all_source_assumption_formulas_retained=True,public_Lean_files_unchanged=True,
    reason='Three short notation entries plus complete source assumptions in cards/notes. Four existing teaching-route notes explicitly featured; all nineteen declarations and historical notes remain in the same registry/inventory.',
    pending='Clean committed site02 build/check/native registry/screenshot and final distinct reader.')
write(run/'site-display-repair-v2.json',record)
print('Display repair:three notation entries/four explicit featured route notes; all19 notes,14 new declarations and5 source cards retained.')
