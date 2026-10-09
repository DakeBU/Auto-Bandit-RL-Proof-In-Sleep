from common_nonsmooth_publication_v2 import *
fixed()
write(RUN/'nonsmooth-checkpoint-helper-schema-repair-v1.json',dict(
    actual_failed_command=['python','-B','-X','utf8','runs/online-ch2-chapter-audit-20261009/checkpoint-nonsmooth-site-v1.py'],
    actual_exit=1,actual_error="KeyError: 'rows'",
    cause='Review input manifests actually use files, not rows. Failure occurred before any commit, scope exception, contributor or site command.',
    repair='Read the actual files schema in both manifests; exact proof/reader/hash scope unchanged.',
    failed_helper_sha256=sha(RUN/'checkpoint-nonsmooth-site-v1.py'),mathematical_repair=False,
    chapter_complete=False,whole_Goal_status='ACTIVE'))
original=(RUN/'checkpoint-nonsmooth-site-v1.py').read_text('utf8')
assert original.count("['rows']")==2
code=original.replace("['rows']","['files']")
exec(compile(code,str(RUN/'checkpoint-nonsmooth-site-v1.py')+' [files-schema-v2]', 'exec'))
