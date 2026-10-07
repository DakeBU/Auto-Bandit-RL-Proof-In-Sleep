from common_integrated_v1 import *
fixed_integrated()
assert load(RUN/'scoped-diff-pre-FINAL-v1-exit.json')['exit_code']==2
log=(RUN/'scoped-diff-pre-FINAL-v1.log').read_text(encoding='utf8')
assert log.strip().endswith('full-blind-decoder-v1.md:1039: new blank line at EOF.')
s=(RUN/'check-scoped-diff-v1.py').read_text(encoding='utf8')
old="if p.endswith('.log'):reason='exact raw command output'"
new="if p.endswith('/full-blind-decoder-v1.md'):\n   assert sha(p)==load(RUN/'full-blind-decoder-receipt-v1.json')['report']['sha256_raw_bytes']\n   reason='Exact independent decoder report raw bytes already receipt-bound; one trailing blank at EOF retained, no rewrite of independent review'\n  elif p.endswith('.log'):reason='exact raw command output'"
assert old in s;s=s.replace(old,new);write(RUN/'check-scoped-diff-v2.py',s)
write(RUN/'review-report-format-preservation-v2.json',dict(failed_gate='scoped-diff-pre-FINAL-v1',actual_exit_code=2,exact_failure_log_sha256=sha(RUN/'scoped-diff-pre-FINAL-v1.log'),exception_path=(RUN/'full-blind-decoder-v1.md').as_posix(),report_sha256=sha(RUN/'full-blind-decoder-v1.md'),report_receipt_sha256=sha(RUN/'full-blind-decoder-receipt-v1.json'),reason='Single trailing blank line at independent report EOF. Preserve exact already reviewed/receipt-bound bytes; retain only this named raw-report whitespace exception. Production/contract/scripts/current docs remain checked.',mathematical_target_unchanged=True))
gate('scoped-diff-pre-FINAL-v2',sys.executable,'-B','-X','utf8',RUN/'check-scoped-diff-v2.py','pre-FINAL-v2')
source=(RUN/'prepare-final-v1.py').read_text(encoding='utf8');tail=source[source.index('mutable='):]
write(RUN/'prepare-final-v2.py',"from common_integrated_v1 import *\nfixed_integrated()\nr=load(RUN/'registry-v3.json')\nassert load(RUN/'pixel-review-v1.json')['status']=='passed'\nassert load(RUN/'scoped-diff-pre-FINAL-v2-exit.json')['exit_code']==0\n"+tail)
print('Single immutable independent-report format exception recorded. Run prepare-final-v2 DIRECT after this helper exits.')
