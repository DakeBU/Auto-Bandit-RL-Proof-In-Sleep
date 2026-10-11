from pathlib import Path
p=Path('tmp/online-ch2-b4-finite-identity-formalizer-20261011')
s=(p/'prepare-v1.py').read_text(encoding='utf-8').split("h=root/")[0]
s=s.replace("print(name,p.returncode,p.stdout.decode('utf-8',errors='replace'),p.stderr.decode('utf-8',errors='replace'))","print(name,p.returncode)")
exec(s)
probe=(out/'HeaderOriginalContextProbe.lean').read_text(encoding='utf-8')
minimal=probe.replace('import Mathlib.Algebra.BigOperators.Module\nimport Mathlib.Tactic','import Mathlib.Algebra.BigOperators.Group.Finset.Basic\nimport Mathlib.Data.Real.Basic')
put('HeaderMinimalContextProbe.lean',minimal)
run('header-minimal-context-elaboration-v1',['lake','env','lean','tmp/online-ch2-b4-finite-identity-formalizer-20261011/HeaderMinimalContextProbe.lean'])
run('retrieval-telescope-names-v1',['rg','-n','sum_range_sub|sum_range_succ','.lake/packages/mathlib/Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean'])