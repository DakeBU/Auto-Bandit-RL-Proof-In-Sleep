from common_integrated_v2 import *

fixed_integrated()
source = (RUN/'prepare-repaired-FINAL-tools-v3.py').read_text(encoding='utf8')
assert not (RUN/'prepare-final-v3.py').exists()
write(RUN/'FINAL-tool-preparation-repair-v4.json', dict(actual_prior_exit_code=1,
    prior_helper_sha256=sha(RUN/'prepare-repaired-FINAL-tools-v3.py'),
    actual_error='AssertionError: Current clean af28b5d v6 browser passes.',
    cause='An exact text replacement expected uppercase Current, while the actual template uses lowercase current.',
    repair='Correct only that replacement key in the executable v4 adaptation; original v3 failure/helper retained.',
    original_FINAL_rejection_preserved=True, no_Lean_reader_target_change=True, package_accepted=False, chapter_complete=False, goal_complete=False))
source = source.replace("('Current clean af28b5d v6 browser passes.',", "('current clean af28b5d v6 browser passes.',")
exec(compile(source, 'prepare-repaired-FINAL-tools-operational-v4', 'exec'))
