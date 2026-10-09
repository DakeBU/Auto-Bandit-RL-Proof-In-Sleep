from publication_guard_v1 import *
fixed()
source=ROOT/'runs/online-ch2-prescient-20261009/capture-prescient-reader-v1.cjs'
assert sha(source)=='f0dab415b39d31efc278a9a3f4e17eb670a0f0fceafca0561c729d1f56921a4a'
script=source.read_text(encoding='utf8')
for old,new in [('nodes.length!==7','nodes.length!==1'),('Missing seven new public nodes','Missing one new public node'),('prescient-source-card-v1.png','proximal-source-card-v1.png'),('actual-affine-prescient-notes-and-sharp-movement-bound-captured','actual-real-convex-minimizer-comparison-captured')]:
    assert script.count(old)==1;script=script.replace(old,new)
write(RUN/'capture-proximal-reader-v1.cjs',script)
write(RUN/'browser-tool-reuse-v1.json',dict(source_path=source.as_posix(),source_sha256=sha(source),new_script_sha256=sha(RUN/'capture-proximal-reader-v1.cjs'),intended_images=4,changes='Only target arity/task label/output filename. Same actual Edge DOM/math/geometry/folded Lean/builtin-wrap machinery. Actual current DOM must satisfy observed source math10 and source cards7; unrun browser is not rendering evidence.',browser_run_pending=True,chapter_complete=False,whole_Goal_status='ACTIVE'))
print('One-node actual browser capture prepared; not run yet.')
