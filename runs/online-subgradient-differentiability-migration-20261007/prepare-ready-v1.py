"""Prepare actual pinned API and compiled dependency probes before review."""
from pathlib import Path
import hashlib,json
run=Path(__file__).parent;sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(n,s):
 p=run/n;assert not p.exists(),p;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(s.encode('utf-8'))
named=json.loads((run/'public-named-declarations-v1.json').read_text(encoding='utf-8'))
old=Path('runs/online-subgradient-basic-migration-20261006/leaves/export-scoped-dependencies-v1.lean')
text=old.read_text(encoding='utf-8');a=text.index('def targets');b=text.index('\ndef moduleName')
text=text[:a]+'def targets : Array Name := #[\n  '+',\n  '.join('`'+n for n in named['public_proofs']+named['public_definitions'])+']\n'+text[b:]
text=text.replace('two retained basic subgradient proofs and one complete definition; direct type/value boundary only','eleven retained differentiability proofs and one complete local-real definition; direct type/value boundary only; canary graph not exported')
write('leaves/export-scoped-dependencies-v1.lean',text)
apis=['BanditRL.OnlineConvex.supporting_functional_at_closure','BanditRL.OnlineConvex.affine_support_of_finite_neighborhood','BanditRL.OnlineConvex.subgradient_exists_of_domain_interior','BanditRL.OnlineConvex.theorem_2_7','ConvexOn.locallyLipschitzOn_interior','IsCompact.tendsto_nhds_of_unique_mapClusterPt','hasFDerivAt_iff_isLittleO','IsLocalMin.hasFDerivAt_eq_zero','InnerProductSpace.toDual','complete_of_proper','interior_singleton','DifferentiableAt.congr_of_eventuallyEq']
write('leaves/pinned-required-APIs-v1.lean','import BanditRLProof\nopen Set Filter\nopen scoped Topology\n'+''.join('#check @'+n+'\n' for n in apis))
rows=[dict(path=(run/n).as_posix(),sha256=sha(run/n)) for n in ['leaves/export-scoped-dependencies-v1.lean','leaves/pinned-required-APIs-v1.lean']]
write('ready-generated-before-use-v1.json',json.dumps(dict(rows=rows,method_donor=dict(path=old.as_posix(),sha256=sha(old)),before_first_use=True),indent=2)+'\n')
write('preparation-export-path-diagnostic-v1.md','Readonly guessed current Interior export-scoped-dependencies-v1.lean absent; actual rg lists export-retained-dependencies and export-public-dependencies. Reused actual Basic exporter after reading it. No theorem/gate mutation. Source rendering defaultPython lacked pypdfium2; actual installed Poppler succeeded, raw v2 output and actual viewed PNG separately retained.\n')
print('Pinned API and12node producer/complete-definition compiled-environment exporter bound before first use.')
