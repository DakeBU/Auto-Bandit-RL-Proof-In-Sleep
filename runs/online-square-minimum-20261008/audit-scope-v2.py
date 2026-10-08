from common_integrated_v1 import *

original = RUN / 'audit-scope-v1.py'
failure_record = RUN / 'scope-check-repair-v2.json'
if not failure_record.exists():
    write(failure_record, dict(failed_script=original.as_posix(), failed_script_sha256=sha(original),
        observed_actual_exit_code=1, observed_assertion='AssertionError: MANIFEST.md',
        cause='The initial ownership checker counted only eight reference-index appends and omitted the two actual task/blueprint registration appends.',
        repair='Check exact two own-task registration entries plus exact eight own native reference-index paths; retain the old checker and every raw prefix.',
        actual_MANIFEST_not_edited_by_repair=True, target_context_source_unchanged=True))
source = original.read_text(encoding='utf8')
old = "        assert len(lines) == 8 and all(RUN.name in line and 'native-reference-index' in line for line in lines), p\n"
assert source.count(old) == 1
new = '''        assert len(lines) == 10, p
        assert '`bandit.py new-task`' in lines[0] and '`tasks/' + TASK + '.md`' in lines[0], p
        assert '`bandit.py blueprint-refresh`' in lines[1] and '`proof-blueprints/' + TASK + '.md`' in lines[1], p
        reference_names = ['lml_bandit_cards.json', 'mathlib_bandit_cards.json', 'bandit_textbook_cards.json',
            'bandit_paper_cards.json', 'bandit_scenario_cards.json', 'proof_weapon_cards.json',
            'local_leaf_cards.json', 'local_lean_declarations.json']
        for line, filename in zip(lines[2:], reference_names):
            assert '`bandit.py reference-index`' in line and '`runs/' + RUN.name + '/native-reference-index/' + filename + '`' in line, p
'''
exec(compile(source.replace(old, new), original.as_posix() + ':ownership-repair-v2', 'exec'))
