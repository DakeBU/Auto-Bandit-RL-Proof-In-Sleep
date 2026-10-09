from common_nonsmooth_publication_v2 import *

fixed()
source=ROOT/'runs/online-c1-chapter-audit-20261009/capture-reader-v3.cjs'
s=source.read_text(encoding='utf8')
s=s.replace("JSON.parse(fs.readFileSync(targetsFile,'utf8')).new_targets", "JSON.parse(fs.readFileSync(targetsFile,'utf8')).targets.map(t=>({name:t.declaration}))")
s=s.replace('nodes.length!==4','nodes.length!==3').replace('Missing four new public nodes','Missing three new public nodes')
s=s.replace('-v3','-v1').replace('chapter-audit-source-card','nonsmooth-source-card')
s=s.replace('actual-initialized-ftl-notes-and-current-chapter-audit-captured','actual-nonsmooth-notes-and-source-qualification-captured')
write(RUN/'capture-nonsmooth-reader-v1.cjs',s)
write(RUN/'nonsmooth-browser-tool-reuse-v1.json',dict(
    source=source.relative_to(ROOT).as_posix(),source_sha256=sha(source),
    actual_new_script_sha256=sha(RUN/'capture-nonsmooth-reader-v1.cjs'),
    intended_images=8,changes='Only actual target JSON adapter, 3-node arity, task-specific output suffix/status/source-card name. Same existing DOM geometry/math/no-overflow and exact folded/module wrap checks.',
    actual_browser_not_yet_run=True,chapter_complete=False,whole_Goal_status='ACTIVE'))
fixed()
print('Read-only browser capture helper prepared from existing tested machinery; current site not yet built or visually certified.')
