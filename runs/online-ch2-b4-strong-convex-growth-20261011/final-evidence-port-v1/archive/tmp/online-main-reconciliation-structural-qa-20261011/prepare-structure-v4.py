from pathlib import Path
import hashlib,json,difflib
ROOT=Path(__file__).resolve().parents[2]
BASE=Path(__file__).resolve().parent
old=BASE/'check-reconciliation-structure-v3.py'; b=old.read_bytes()
assert hashlib.sha256(b).hexdigest()=='879ec5df108e5d1585686fbae7bbcb5fb30f1a91e3943dfae83c0d9e7386e009'
s=b.decode();original=s
replacements=[
 ("NAME='BanditRL.OnlineCumulativePotential.finite_regret_identity'", "NAME='BanditRL.OnlineCumulativePotential.finite_regret_identity'\nGROWTH='BanditRL.OnlineConvex.stronglyConvex_minimum_growth'"),
 ("need(len(additions)==1,'exactly one new highlight object')", "need(len(additions)==2,'exactly two new highlight objects since baseline: accepted-main projection and reviewed conditional growth')"),
 ("need(json.loads(additions[0])['full_name']=='BanditRL.OnlineGradientDescent.project_existsUnique','only genuinely new unique-projection highlight')", "need({json.loads(v)['full_name'] for v in additions}=={'BanditRL.OnlineGradientDescent.project_existsUnique',GROWTH},'only projection and conditional-growth highlight additions')"),
 ("len(nm)==len(reg['nodes'])==11106", "len(nm)==len(reg['nodes'])==11107"),
 ("need(set(nm)-set(om)=={unique},'sole new main projection theorem')", "need(set(nm)-set(om)=={unique,'declaration:'+GROWTH},'only main projection and reviewed growth theorem added to baseline')"),
 ("manifest['declaration_count']==11106", "manifest['declaration_count']==11107"),
 ("need(nm[unique]['status']=='compiled','new unique-projection node compiled')", "need(nm[unique]['status']=='compiled','new unique-projection node compiled')\n need(nm['declaration:'+GROWTH]['status']=='compiled','conditional-growth node compiled')"),
 ("'new_production_ID':unique", "'new_production_ID':unique,'new_conditional_dependency_ID':'declaration:'+GROWTH")]
for before,after in replacements:
 assert s.count(before)==1,before;s=s.replace(before,after)
dest=BASE/'check-reconciliation-structure-v4.py'
with dest.open('xb') as f:f.write(s.encode())
spec=json.loads((BASE/'input-spec-execution-v4.json').read_text(encoding='utf-8'))
spec['head']='cf1a424f2312e7c5b730717cf0a96d65837894bd'
spec['checker_sha256']=hashlib.sha256(dest.read_bytes()).hexdigest()
for path in ['BanditRLProof/OnlineStrongConvexMinimum.lean','Tests/OnlineStrongConvexMinimumCanary.lean',
 'docs/contracts/online-ch2-b4-strong-convex-growth-v1/neutral-frozen-header-v1.txt',
 'website/content/chapters.json','website/content/readings.json','website/content/highlights.json',
 'research-wiki/contribution-contracts/online-ch2-b4-strong-convex-growth-20261011.json']:
 spec['bindings'][path]=hashlib.sha256((ROOT/path).read_bytes()).hexdigest()
spec['instruction']='Only one additional reviewed production declaration/card/module relative to v3 candidate; retain every old full registry/highlight object including duplicate multiplicities, exact projection block and complete RAW/ZIP/governance/schema3/Book checks. New reader JSON bytes pinned to independently reviewed/appplied V3; no old-object exceptions.'
out=BASE/'input-spec-execution-v5.json'
with out.open('x',encoding='utf-8') as f:json.dump(spec,f,indent=2);f.write('\n')
diff=BASE/'structure-v3-to-v4.diff'
with diff.open('x',encoding='utf-8') as f:f.writelines(difflib.unified_diff(original.splitlines(True),s.splitlines(True),fromfile=old.name,tofile=dest.name))
print(json.dumps({p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in (dest,out,diff)},indent=2))
