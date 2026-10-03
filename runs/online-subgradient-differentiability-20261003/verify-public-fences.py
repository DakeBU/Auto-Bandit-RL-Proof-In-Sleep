from pathlib import Path
import json, subprocess, hashlib

root=Path.cwd()
run=root/'runs/online-subgradient-differentiability-20261003'
original=root/'docs/contracts/online-subgradient-differentiability-v2'
public=root/'docs/contracts/online-subgradient-differentiability-public-v1'
public.mkdir(exist_ok=True)
targets=['theorem_2_22','theorem_2_22_gradient','theorem_2_22_forward',
 'sourceDifferentiableAt_regular','singleton_subdifferential_interior',
 'singleton_subdifferential_hasGradientAt','subgradient_norm_le_lipschitz_ball',
 'subgradients_locally_bounded','subgradient_limit_of_continuousAt','singleton_subgradient_tendsto']
checks=[]
for target in targets:
    fence=json.loads((original/(target+'.json')).read_text(encoding='utf-8'))
    fence['file']='BanditRLProof/OnlineSubgradientDifferentiability.lean'
    path=public/(target+'.json')
    path.write_text(json.dumps(fence,indent=2)+'\n',encoding='utf-8')
    result=subprocess.run(['python','-X','utf8','tools/bandit.py','safe-verify','--fence',str(path)],capture_output=True,text=True,encoding='utf-8')
    assert result.returncode==0,(target,result.stdout,result.stderr)
    check=json.loads(result.stdout)
    assert check['ok'] and check['actual_statement_hash']==fence['statement_hash']
    checks.append(check)
extra=[('docs/contracts/online-affine-finite-neighborhood-v1/affine_support_of_finite_neighborhood.json','BanditRLProof/OnlineConvexMinorant.lean'),
 ('docs/contracts/online-subgradient-interior-public-v1/affine_support_of_domain_interior.json','BanditRLProof/OnlineConvexMinorant.lean')]
for path,file in extra:
    result=subprocess.run(['python','-X','utf8','tools/bandit.py','safe-verify','--fence',path,'--lean-file',file],capture_output=True,text=True,encoding='utf-8')
    assert result.returncode==0,(path,result.stdout,result.stderr)
    checks.append(json.loads(result.stdout))
old=json.loads((root/'docs/contracts/online-subgradient-interior-public-v1/integration.json').read_text())
text=(root/'BanditRLProof/OnlineConvexMinorant.lean').read_text(encoding='utf-8')
start=text.index('theorem affine_minorant_of_domain_interior')
header=text[start:text.index(' := by',start)].strip()
assert hashlib.sha256(header.encode()).hexdigest()==old['old_header_sha256']
out={'status':'passed','checks':checks,'unchanged_old_minorant_header_sha256':old['old_header_sha256'],
 'boundary':'Statement-fence verification only; separate focused/root builds and semantic review are required.'}
(run/'public-frozen-check.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'status':'passed','frozen_checks':len(checks),'old_minorant_header_preserved':True}))
