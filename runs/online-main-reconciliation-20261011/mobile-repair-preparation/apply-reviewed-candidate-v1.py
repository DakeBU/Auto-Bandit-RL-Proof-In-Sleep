from pathlib import Path
import json,hashlib,subprocess,sys
r=Path.cwd();d=r/'tmp/online-main-reconciliation-mobile-fix-20261011';base=r/'runs/online-main-reconciliation-20261011'
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
git=lambda *a:subprocess.check_output(['git',*a],cwd=r)
assert git('rev-parse','HEAD').decode().strip()=='e7babdaa0333262b87e3988159178364de33159e'
assert git('status','--porcelain=v1','-z')==b''
assert h(d/'candidate-site.css')=='0527c9855cbda6100517bf961c5649d5abb10900cdb3668a46b30c4d38a39d14'
assert h(r/'website/static/site.css')=='2304ca6c9de5fd6771be6b1bfab32bd3ab80e594db85c11aa7d530a30875fb90'
assert h(d/'native-manifest-draft-v1.json')=='b711844d65c7bb4accd8d74b2bf434e907eb321b6363c7f2c72d8cfdfeee14fa'
review=Path(sys.argv[1]);expected=sys.argv[2];assert h(review)==expected
rv=json.loads(review.read_bytes());assert rv.get('eligible_for_application') is True
plan=r/'tmp/online-main-reconciliation-final-port-plan-20261011/historical-port-plan-v1.json';assert h(plan)=='4e18914db1b38881542a90db8e3006295a5aca222440a8aa82566ea4672ec9b8'
rows=json.loads(plan.read_bytes())['rows']
for f in sorted(d.iterdir()):
 if f.is_file():rows.append({'source':f.relative_to(r).as_posix(),'destination':(base/'mobile-repair-preparation'/f.name).relative_to(r).as_posix(),'sha256':h(f),'bytes':f.stat().st_size,'already_retained':False})
rows.append({'source':review.relative_to(r).as_posix(),'destination':(base/'mobile-repair-independent-review'/review.name).relative_to(r).as_posix(),'sha256':expected,'bytes':review.stat().st_size,'already_retained':False})
rows.append({'source':plan.relative_to(r).as_posix(),'destination':(base/'historical-port-plan-v1.json').relative_to(r).as_posix(),'sha256':h(plan),'bytes':plan.stat().st_size,'already_retained':False})
for row in rows:
 src=r/row['source'];dest=(r/row['destination']).resolve();assert base.resolve() in dest.parents;assert h(src)==row['sha256'] and src.stat().st_size==row['bytes']
 if dest.exists():assert h(dest)==row['sha256'] and dest.stat().st_size==row['bytes']
manifest=r/'research-wiki/contribution-contracts/ONLINE-MAIN-MOBILE-GRID-20261011.json';receipt=base/'mobile-grid-repair-application-v1.json';assert not manifest.exists() and not receipt.exists()
created=[]
for row in rows:
 dest=r/row['destination']
 if not dest.exists():dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes((r/row['source']).read_bytes());created.append(row['destination'])
 assert h(dest)==row['sha256'] and dest.stat().st_size==row['bytes']
manifest.write_bytes((d/'native-manifest-draft-v1.json').read_bytes())
(r/'website/static/site.css').write_bytes((d/'candidate-site.css').read_bytes())
report={'status':'APPLIED_REVIEWED_CSS_CANDIDATE_NOT_RENDERED_ACCEPTED','source_head':'e7babdaa0333262b87e3988159178364de33159e','review_sha256':expected,'css_sha256':h(r/'website/static/site.css'),'native_manifest_sha256':h(manifest),'rows':rows,'created_archive_paths':created,'scope':'Exact preserved historical failure/success evidence, two CSS rules, native maintenance metadata only. No mathematical changes; fresh same-HEAD gates and reader checks required. C2 partial/false/null; 7+6 open; Goal ACTIVE. Browser profiles retained locally excluded from exports.'}
receipt.write_bytes((json.dumps(report,indent=2)+'\n').encode());print(json.dumps({'receipt':str(receipt),'sha256':h(receipt),'rows':len(rows),'created_unique':len(created)}))
