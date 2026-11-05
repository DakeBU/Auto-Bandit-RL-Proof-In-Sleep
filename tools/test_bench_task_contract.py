import json
import tempfile
import unittest
from pathlib import Path
from tools import bench_task_contract as intake


class IntakeTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)/'task'
        intake.scaffold(self.root, 'BRB-DRAFT-TEST', 'agentic-lean')

    def task(self):
        return json.loads((self.root/'task.json').read_text())

    def save(self, task):
        task['contract_sha256'] = intake.seal(self.root, task)
        (self.root/'task.json').write_text(json.dumps(task))

    def test_draft_is_intake_only(self):
        self.assertEqual(intake.validate(self.root)['stage'], 'draft')
        with self.assertRaises(FileExistsError):
            intake.scaffold(self.root, 'OTHER', 'reasoning')

    def test_mutating_instruction_or_solution_invalidates_seal(self):
        for name in ('instruction.md', 'solution/reference.txt'):
            old = (self.root/name).read_bytes()
            (self.root/name).write_text('Changed mathematical task')
            with self.assertRaisesRegex(ValueError, 'sealing'):
                intake.validate(self.root)
            (self.root/name).write_bytes(old)

    def test_intake_cannot_admit_or_publish_test_split(self):
        for field, value in [('stage','admitted'), ('split','test')]:
            task = self.task(); task[field] = value; self.save(task)
            with self.assertRaises(ValueError): intake.validate(self.root)
            task[field] = 'draft' if field == 'stage' else 'dev'; self.save(task)

    def test_agent_visibility_excludes_gold(self):
        path = self.root/'environment/manifest.json'
        env = json.loads(path.read_text()); env['agent_visible'].append('solution')
        path.write_text(json.dumps(env)); self.save(self.task())
        with self.assertRaisesRegex(ValueError, 'exclude'): intake.validate(self.root)

    def test_unexecuted_template_cannot_be_candidate(self):
        task = self.task(); task['stage'] = 'candidate'; self.save(task)
        with self.assertRaisesRegex(ValueError, 'immutable'): intake.validate(self.root)

    def test_budget_and_format_are_explicit(self):
        task = self.task(); task['budgets']['tokens'] = 0; self.save(task)
        with self.assertRaisesRegex(ValueError, 'caps'): intake.validate(self.root)
        task['budgets']['tokens'] = 100; task['answer_format'] = 'natural-language'; self.save(task)
        with self.assertRaisesRegex(ValueError, 'artifacts'): intake.validate(self.root)


if __name__ == '__main__': unittest.main()
