from pathlib import Path
import os,json
p=Path('tmp/online-ch2-b4-finite-identity-core-20261011')
s=(p/'audit-v1.py').read_text(encoding='utf-8').split('sys.path.insert')[0];exec(s)
r=run('lake-search-path-v1',['lake','env','python','-c','import os; print(os.environ.get("LEAN_PATH", ""))']);assert r.returncode==0
lakepath=r.stdout.decode().strip(); env=os.environ.copy();env['LEAN_PATH']=str(out/'compiled')+os.pathsep+lakepath
run('public-compiled-probe-v2',['lean','tmp/online-ch2-b4-finite-identity-core-20261011/PublicCompiledProbe.lean'],env)