from pathlib import Path
import os
p=Path('tmp/online-ch2-b4-finite-identity-canary-core-20261011');s=(p/'prepare-v1.py').read_text(encoding='utf-8').split('checks=')[0];exec(s)
path=root/'Tests/OnlineCumulativePotentialCanary.lean'
s=path.read_text(encoding='utf-8').replace('fun _ v : ℝ =>','fun (_ : ℕ) (v : ℝ) =>').replace('fun t v : ℝ =>','fun (t : ℕ) (v : ℝ) =>')
put('candidate-v2.lean',s);path.write_bytes(s.encode('utf-8'))
env=os.environ.copy();env['LEAN_PATH']=str(root/'tmp/online-ch2-b4-finite-identity-core-20261011/compiled')+os.pathsep+(out/'lake-search-path-v1.stdout.raw').read_text().strip()
run('focused-v2',['lean','Tests/OnlineCumulativePotentialCanary.lean'],env)