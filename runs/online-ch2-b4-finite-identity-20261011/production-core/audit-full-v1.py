from pathlib import Path
import os
p=Path('tmp/online-ch2-b4-finite-identity-core-20261011')
s=(p/'audit-v1.py').read_text(encoding='utf-8').split('sys.path.insert')[0];exec(s)
probe=(out/'PublicCompiledProbe.lean').read_text(encoding='utf-8').replace('open Lean Elab Command\n','open Lean Elab Command\nset_option pp.all true\nset_option pp.proofs true\nset_option pp.maxDepth 100000\nset_option pp.maxSteps 10000000\n').replace('compiled-constant-occurrences-v1.json','compiled-constant-occurrences-v2.json')
put('PublicCompiledProbeFull.lean',probe)
env=os.environ.copy();env['LEAN_PATH']=str(out/'compiled')+os.pathsep+(out/'lake-search-path-v1.stdout.raw').read_text().strip()
run('public-compiled-probe-full-v1',['lean','tmp/online-ch2-b4-finite-identity-core-20261011/PublicCompiledProbeFull.lean'],env)