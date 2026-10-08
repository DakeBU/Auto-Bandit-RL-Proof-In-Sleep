from common_accepted_v3 import *
from commit_owned_v2 import stage_owned
import ast

accepted_fixed()
old_exceptions = load(RUN/'diff-raw-bound-exceptions-v2.json')['exceptions']
new_names = ['publish-push-v4.log','scoped-diff-draft-delivery-v3.log']
extras = [dict(path=(RUN/n).relative_to(ROOT).as_posix(),sha256=sha(RUN/n),
    reason='Actual Git remote raw stdout, or actual failed whitespace checker quoting it; never production/test/reader/contract/helper code.') for n in new_names]
write(RUN/'diff-raw-bound-exceptions-delivery-v4.json',dict(exceptions=old_exceptions+extras,
    original_source_gate_exceptions=5,new_delivery_raw_stdout_exceptions=2,
    raw_bytes_preserved=True,executable_helper_exemptions=0))
old = (RUN/'check-scoped-diff-v2.py').read_text(encoding='utf8')
old = old.replace("diff-raw-bound-exceptions-v2.json", "diff-raw-bound-exceptions-delivery-v4.json")
old = old.replace('assert len(exceptions)==5','assert len(exceptions)==7')
old = old.replace("assert {Path(r['path']).name for r in exceptions}==expected", "expected.update(['publish-push-v4.log','scoped-diff-draft-delivery-v3.log'])\nassert {Path(r['path']).name for r in exceptions}==expected")
old = old.replace("'scoped-diff-'+sys.argv[1]", "'scoped-delivery-diff-'+sys.argv[1]")
ast.parse(old)
write(RUN/'check-scoped-delivery-diff-v4.py',old)
prior = load(RUN/'proposed-publication-v3.json')
body = Path(prior['body_path']).read_text(encoding='utf8')
before = 'Scoped checking passes with exactly five SHA-bound raw stdout exceptions and no production, test, reader, contract or executable-helper exemption.'
after = ('Proof acceptance used five SHA-bound raw stdout exceptions. Delivery adds two SHA-bound raw stdout logs '
    '(Git remote output and the failed whitespace check quoting it). Scoped checking passes with these seven exact exceptions '
    'and no production, test, reader, contract or executable-helper exemption.')
assert body.count(before) == 1
write(RUN/'prospective-PR-title-v4.txt',Path(prior['title_path']).read_bytes())
write(RUN/'prospective-PR-body-v4.md',body.replace(before,after))
write(RUN/'proposed-publication-delivery-v4.json',dict(operative_for_body_update=True,
    supersedes_publication_text_version=3,original_approved_creation_body_sha256=prior['body_sha256'],
    title_path=(RUN/'prospective-PR-title-v4.txt').relative_to(ROOT).as_posix(),
    title_sha256=sha(RUN/'prospective-PR-title-v4.txt'),
    body_path=(RUN/'prospective-PR-body-v4.md').relative_to(ROOT).as_posix(),
    body_sha256=sha(RUN/'prospective-PR-body-v4.md'),PR=195,body_update_review_pending=True,
    source_statements_proofs_readers_unchanged=True,chapter_complete=False,goal_complete=False))
write(RUN/'delivery-raw-review-packet-v4.md', '''# Narrow actual draft-delivery raw stdout repair

Reuse distinct source_reviewer, Astra/medium. This is only final delivery evidence repair, not source/proof/reader recertification. Original1822 and all56 postnative bytes remain fixed. PR195 actually created draft/open/unmerged and officially attached; initial title/body match original approved3 exactbytes. Preserve all original receipts and prospective3 files.

Actual publish-push-v3 failed403 via cached artifact account; active gh account's repository push permission was read, per-command official gh auth git-credential succeeded without global settings changes. Actual raw publish-push-v4.log includes GitHub remote lines ending in spaces. Original five source stdout exceptions remain unchanged. Latest scoped check failed solely on that new raw log; its failed checker stdout quotes those exact trailing spaces. New delivery whitelist adds EXACTLY these two raw stdout files, individually SHA-bound, to total7. No production/Test/reader/contract/executable-helper exemption. check-scoped-delivery-diff-v4.py genuinely checks the complete staged base diff excluding only those7. Full unexcluded check remains failed; no commandexit0 implies compiled. Review code and actual new pass. One separate delivery-only extra parenthesis failure was fixed in newhelper4 with originalhelper/replaystdout/ASTproof retained; public/header/Test/reader bytes unchanged.

proposed-publication-delivery-v4.json selects the EXACT next PR195 body, changing only the paragraph explaining original5 proof-gate exceptions and two deliveryraw exceptions to current7. Title unchanged. Current PRbody3 was initially accurate; update has not happened. Decide accepted|accepted-with-explicit-delta|rejected for the 2raw exceptions and exact prospectivebody4 ONLY. Publish/update permission already user-authorized; reviewer is judging evidence, not new human authorization. Preserve16/null/kernel/asymptotic/oldfive/C1C2/3-16/appendix/Goalactive/no merge/live/retirement. Future own delivery records may be versioned to report actual7 and record actual PRbody update, evidence commit/push/direct remote head verification. No frozen contract/reader edits.

Write ONLY delivery-raw-review-v4.md and delivery-raw-receipt-v4.json. Actor/task, verdict, report/rawSHA, fixed_input_count, all reviewed_files/inputindex/report rawbindings, before_after_raw_hashes_match/inputs_unchanged, required_repairs array, exact_two_raw_stdout_exception_verdicts, exact_prospective_body/title_SHA and original3 preserved, future_limited_delivery_records permission. No chapter/Goal acceptance. Return hashes.
''')
stage_owned()
gate('scoped-delivery-diff-v4',sys.executable,'-B','-X','utf8',RUN/'check-scoped-delivery-diff-v4.py','repair-v4')
names = ['publish-push-v3.log','publish-push-v3-exit.json','publish-push-v4.log','publish-push-v4-exit.json',
    'push-credential-repair-v4.json','publish-active-account-rights-v4.log','publish-active-account-rights-v4-exit.json',
    'scoped-diff-draft-delivery-v3.log','scoped-diff-draft-delivery-v3-exit.json',
    'diff-raw-bound-exceptions-v2.json','diff-raw-bound-exceptions-delivery-v4.json',
    'check-scoped-delivery-diff-v4.py','scoped-delivery-diff-v4.log','scoped-delivery-diff-v4-exit.json',
    'scoped-delivery-diff-repair-v4.json','proposed-publication-delivery-v4.json','prospective-PR-title-v4.txt',
    'prospective-PR-body-v4.md','close-draft-delivery-v3.py','close-draft-delivery-v4.py',
    'repair-delivery-syntax-v4.py','delivery-syntax-repair-v4.json','close-delivery-v3-syntax-failed-replay.log',
    'close-delivery-v3-syntax-failed-replay-exit.json','official-app-PR195-attachment-v3.json',
    'actual-PR195-REST-v3.log','actual-PR195-REST-v3-exit.json','delivery-raw-review-packet-v4.md']
paths = [RUN/n for n in names]
rows = [dict(path=p.resolve().as_posix(),sha256=sha(p)) for p in paths]
write(RUN/'delivery-raw-review-inputs-v4.json',dict(rows=rows,fixed_input_count=len(rows),
    phase='Narrow actual delivery raw exception/body paragraph audit only',chapter_complete=False,goal_complete=False))
print('Actual seven-raw-only delivery diff passes; narrow review inputs',len(rows))
