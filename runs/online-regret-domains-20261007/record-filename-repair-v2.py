from common_v1 import *
fixed(integrated=True)
p=Path('research-wiki/contribution-contracts/online-regret-domains-20261007.json')
assert p.exists() and p.name in [q.name for q in p.parent.iterdir()]
assert sha(p)=='a945a9450278fc066e7de3f394df0615f27570096169410b54e9b4e53145544f'
write(RUN/'filename-case-repair-v2.json',dict(original_failed_command='python -B -X utf8 runs/online-regret-domains-20261007/audit-scope-v1.py pre-site',actual_exit_code=1,failed_path='research-wiki/contribution-contracts/ONLINE-REGRET-DOMAINS-20261007.json',reason='Integration helper used uppercase task ID for filename; frozen owned paths require lowercase manifest filename. Same Windows physical file was renamed case-only using Rename-Item; SHA equality checked by actual tool.',corrected_filename=p.as_posix(),raw_sha256=sha(p),mathematical_statement_changed=False,reviewed_public_and_canary_bytes_unchanged=True,no_scope_expansion=True,executed_helper_original_preserved=True))
gate('scope-pre-site-v3',sys.executable,'-B','-X','utf8',RUN/'audit-scope-v1.py','pre-site-v3')
