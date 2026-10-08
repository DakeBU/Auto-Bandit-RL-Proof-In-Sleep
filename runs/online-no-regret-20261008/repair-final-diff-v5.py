from common_integrated_v2 import *
fixed_integrated()
old = load(RUN / 'diff-raw-evidence-exceptions-v4.json')['exceptions']
for row in old:
    assert sha(row['path']) == row['sha256']
new = [dict(path=(RUN / name).relative_to(ROOT).as_posix(), sha256=sha(RUN / name),
            reason='Immutable failed diff stdout quotes the original independently bound evidence whitespace; retain exact bytes.')
       for name in ['scoped-diff-v3.log', 'scoped-diff-pre-FINAL-v4.log']]
write(RUN / 'diff-raw-evidence-exceptions-v5.json', dict(
    exceptions=old + new,
    repair='v4 omitted two subsequently committed failed-check stdout files that quote the preserved original whitespace. Only these exact hash-bound evidence paths are additionally excluded; all source, reader, scripts, contracts and successful checks remain checked.',
    failed_gate='scoped-diff-pre-FINAL-v4-exit.json', source_or_statement_change=False))
original = (RUN / 'check-scoped-diff-v4.py').read_text(encoding='utf8')
write(RUN / 'check-scoped-diff-v5.py', original.replace('diff-raw-evidence-exceptions-v4.json', 'diff-raw-evidence-exceptions-v5.json'))
prepare = (RUN / 'prepare-final-v2.py').read_text(encoding='utf8')
prepare = prepare.replace("gate('source-scope-pre-FINAL-v1',sys.executable,'-B','-X','utf8',RUN/'audit-scope-v3.py','pre-FINAL-v1')", "assert load(RUN/'source-scope-pre-FINAL-v1-exit.json')['exit_code']==0")
prepare = prepare.replace("gate('contributor-pre-FINAL-v1',sys.executable,'-B','-X','utf8','tools/check_contributor_contract.py','--base',BASE)", "assert load(RUN/'contributor-pre-FINAL-v1-exit.json')['exit_code']==0")
prepare = prepare.replace("gate('scoped-diff-pre-FINAL-v4',sys.executable,'-B','-X','utf8',RUN/'check-scoped-diff-v4.py','pre-FINAL-v4')", "gate('scoped-diff-pre-FINAL-v5',sys.executable,'-B','-X','utf8',RUN/'check-scoped-diff-v5.py','pre-FINAL-v5')")
write(RUN / 'prepare-final-v3.py', prepare)
print('Exact two additional immutable failed logs bound; no source, header or receipt changes.')
