from common import *
import ast
old=load(RUN/'native-package-helpers-prepared-20261011-v1.json')
paths=[]
for row in old['scripts']:
    p=Path(row['path']);assert sha(p)==row['sha256']
    name=p.name.replace('_v1.py','_v2.py').replace('-v1.py','-v2.py')
    s=p.read_text(encoding='utf8').replace('native_package_guard_prepared_20261011_v1','native_package_guard_prepared_20261011_v2')
    for before in ['freeze-native-package-plan-prepared-20261011-v1.py','execute-native-package-prepared-20261011-v1.py','prepare-postnative-transition-prepared-20261011-v1.py']:
        s=s.replace(before,before.replace('-v1.py','-v2.py'))
    if p.name.startswith('freeze-native'):
        s=s.replace("all_inputs=[Path(r['path']) for r in verified['gate_rows']+verified['source_binding']+helpers+support]+mutable+[a.request]+extra", "all_inputs=[Path(r['path']) for r in verified['gate_rows']+verified['source_binding']+helpers+support]+mutable+[a.request,PDF]+extra+list(RUN.rglob('*'))+list(CONTRACT.rglob('*'))")
        s=s.replace('input_manifest path/hash, approved_native_plan_sha256','input_manifest as an object {path: absolute path, sha256: raw SHA256}, approved_native_plan_sha256')
    ast.parse(s,filename=name);write(RUN/name,s);paths.append(RUN/name)
write(RUN/'native-package-helpers-prepared-20261011-v2.json',dict(old,scripts=rows(paths),supersedes=rows([RUN/'native-package-helpers-prepared-20261011-v1.json']),improvements='Future FINAL inputmanifest includes complete existing OWN RUN/CONTRACT history and pinnedPDF automatically, preserving failed attempts; FINAL receipt input_manifest object schema explicit. No helpers executed and actual request/plan remain unfrozen.'))
print('Nativepreparedv2manifest SHA '+sha(RUN/'native-package-helpers-prepared-20261011-v2.json'))
