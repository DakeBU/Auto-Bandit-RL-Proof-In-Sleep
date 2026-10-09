from publication_guard_v1 import *
fixed()
failed=load(RUN/'candidate-full-diff-check-v1.json')
out=base64.b64decode(failed['stdout_base64']).decode('utf8')
assert failed['actual_exit']==2
expected=[('blind-reconstruction-v1.md',83,'96412f8940cf519b926bd68279287eb3ecb1f763dc71e7fd6ec22d42c119f684'),('canary-blind-v1.md',30,'fc234afdccf2fcdfe7238f3145b6633c412d8affa9bc349215d699139c13bd85')]
reports=[]
for name,line,pin in expected:
    p=RUN/name;assert sha(p)==pin
    raw=p.read_bytes();lines=raw.splitlines()
    bad=[i+1 for i,s in enumerate(lines) if s.rstrip(b' \t')!=s]
    assert bad==[line] and lines[line-1].endswith(b'\\ ')
    assert str(p.relative_to(ROOT).as_posix())+':'+str(line)+': trailing whitespace.' in out
    reports.append(dict(path=p.as_posix(),sha256=pin,line=line,raw_base64=base64.b64encode(raw).decode('ascii'),exact_problem_line_base64=base64.b64encode(lines[line-1]).decode('ascii'),kind='Immutable received neutral decoder Markdown, one literal LaTex control-space at end of line; no source/statement/Lean/Test/reader file.'))
assert out.count(': trailing whitespace.')==2 and ': new blank line at EOF.' not in out
paths=[Path(x['path']).relative_to(ROOT).as_posix() for x in reports]
capture('candidate-prospective-scoped-diff-check-v2','git','diff','--cached',BASE,'--check','--','.',*[':(exclude)'+p for p in paths])
write(RUN/'RAW-format-exception-proposal-v1.json',dict(prior_failed_command_sha256=sha(RUN/'candidate-full-diff-check-v1.json'),actual_full_exit=2,actual_scoped_exit=0,proposed_exact_RAW_exceptions=reports,scope='Only two SHA-bound immutable received Markdown files, each exactly one diagnosed LaTex control-space. Keep originals byte-for-byte; no theorem/source/Test/reader/other-file exception and no full-diff exit0 claim.',proof_and_targets_and_root_and_reader_unchanged=True,full_harness_not_rerun_or_weakened=True,whole_Goal_status='ACTIVE'))
write(RUN/'RAW-format-review-packet-v1.md','Supplemental exact immutable-report format boundary only. Full git diff check actually exits2 for exactly2 trailing-space diagnostics, one in each earlier received decoder Markdown; each is a literal LaTex control-space, and all source/statement/proof/Test/root/reader bytes remain unchanged. Original SHA-bound reports were already independently source-reviewed; retain original RAW, rather than silently rewriting received evidence. Proposal binds exact file/line/RAW bytes and full failure, prospective exclusion check actual0. Assess preservation of evidence and a precise supplementary scoped whitespace exception, or require a different versioned repair. No claim full diff exit0. No mathematical or source-fidelity exemption; full Lean/harness already0/472tests7existing skips. This is prospective metadata permission only; candidate commit/site/FINAL/native/delivery still pending. Output RAW-format-review-v1.md/json one final LF, approved_RAW_exceptions or explicit required repairs; do not mutate inputs.')
files=[PUBLIC,CANARY,RUN/'candidate-full-diff-check-v1.json',RUN/'candidate-prospective-scoped-diff-check-v2.json',RUN/'RAW-format-exception-proposal-v1.json',RUN/'RAW-format-review-packet-v1.md',RUN/'full-harness-inspected-v1.json',RUN/'canary-BODY-publication-review-v2.json',RUN/'publication-review-binding-v2.json']+[RUN/x[0] for x in expected]
write(RUN/'RAW-format-review-inputs-v1.json',dict(rows=rows(files),allowed_new_outputs=['RAW-format-review-v1.md','RAW-format-review-v1.json'],no_existing_changes=True))
fixed()
print('Exact two immutable received RAW diagnostics and prospective scoped0 bound for review; no full0 claim.')
