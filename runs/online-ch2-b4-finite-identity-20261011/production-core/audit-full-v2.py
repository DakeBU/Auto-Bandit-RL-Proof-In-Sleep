from pathlib import Path
import os
p=Path('tmp/online-ch2-b4-finite-identity-core-20261011')
s=(p/'audit-v1.py').read_text(encoding='utf-8').split('sys.path.insert')[0];exec(s)
probe=(out/'PublicCompiledProbeFull.lean').read_text(encoding='utf-8').replace('set_option pp.maxDepth 100000\n','').replace('compiled-constant-occurrences-v2.json','compiled-constant-occurrences-v3.json')
put('PublicCompiledProbeFullV2.lean',probe)
env=os.environ.copy();env['LEAN_PATH']=str(out/'compiled')+os.pathsep+(out/'lake-search-path-v1.stdout.raw').read_text().strip()
run('public-compiled-probe-full-v2',['lean','tmp/online-ch2-b4-finite-identity-core-20261011/PublicCompiledProbeFullV2.lean'],env)