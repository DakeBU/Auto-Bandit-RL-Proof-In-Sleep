from common_accepted_v1 import *
accepted_fixed()
old=load(RUN/'diff-raw-evidence-exceptions-v5.json')['exceptions']
for row in old:
    assert sha(row['path'])==row['sha256']
extra=[dict(path=(RUN/n).relative_to(ROOT).as_posix(),sha256=sha(RUN/n),
    reason='Exact immutable successful diff stdout gained one trailing blank line from print(empty child stdout); preserve command evidence bytes.')
    for n in ['scoped-diff-pre-push-v5.log','scoped-diff-publication-v5.log']]
write(RUN/'diff-raw-evidence-exceptions-v6.json',dict(exceptions=old+extra,
    failure='scoped-diff-delivery-v5 actual exit1/child Git exit2: two newly committed successful-check stdout files have blank line at EOF.',
    exact_two_new_exceptions=True,production_reader_contract_scripts_still_checked=True,
    repair='Preserve both closed original logs by hash. Future checker writes exact child stdout without adding a blank line.',
    source_or_statement_change=False,all_prior_receipts_unchanged=True))
checker=(RUN/'check-scoped-diff-v5.py').read_text(encoding='utf8')
checker=checker.replace('diff-raw-evidence-exceptions-v5.json','diff-raw-evidence-exceptions-v6.json')
checker=checker.replace("print(child.stdout.decode('utf8',errors='replace'))", "sys.stdout.write(child.stdout.decode('utf8',errors='replace'))")
write(RUN/'check-scoped-diff-v6.py',checker)
close=(RUN/'close-delivery-v1.py').read_text(encoding='utf8')
tail=close[close.index("gate('contributor-delivery-v1'"):]
tail=tail.replace("gate('contributor-delivery-v1',sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',BASE)", "assert load(RUN/'contributor-delivery-v1-exit.json')['exit_code']==0")
tail=tail.replace("gate('scoped-diff-delivery-v5',sys.executable,'-B','-X','utf8',RUN/'check-scoped-diff-v5.py','delivery-v5')", "gate('scoped-diff-delivery-v6',sys.executable,'-B','-X','utf8',RUN/'check-scoped-diff-v6.py','delivery-v6')")
write(RUN/'resume-close-delivery-v2.py',"from common_accepted_v1 import *\naccepted_fixed()\nassert load(RUN/'delivery-obligations-overlay-v1.json')['PR_number']==192\n"+tail)
print('Exact two successful stdout exceptions bound; pending delivery tail prepared, no native or metadata replay.')
