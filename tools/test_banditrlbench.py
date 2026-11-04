"""Operational regressions: immutable tasks, gold separation and honest receipts."""
import argparse
import copy
import json
import tempfile
import unittest
from pathlib import Path

from tools import banditrlbench as run


class RunnerTests(unittest.TestCase):
    def setUp(self):
        self.data = run.registry.load()
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)

    def prepare(self, track='non-lean'):
        out = self.root / track
        args = argparse.Namespace(output=out, track=track, mode='closed-book', model='unit-fixture', agent='unit-fixture')
        run.prepare(args, self.data)
        return out, args

    def test_prompt_bundle_has_exact_target_but_no_gold(self):
        out, args = self.prepare('lean')
        prompts = [json.loads(x) for x in (out / 'prompts.jsonl').read_text().splitlines()]
        for row in prompts:
            self.assertIn('target_signature', row)
            self.assertNotIn('reference_proof', row)
            self.assertNotIn('answer', row)
            self.assertNotIn('rubric', row)
        self.assertEqual(len(run.read_predictions(out / 'predictions.jsonl', self.data, 'lean')), 2)
        with self.assertRaises(FileExistsError):
            run.prepare(args, self.data)

    def test_stale_target_and_duplicate_submission_rejected(self):
        out, _ = self.prepare('lean')
        path = out / 'predictions.jsonl'
        rows = [json.loads(x) for x in path.read_text().splitlines()]
        original = copy.deepcopy(rows)
        rows[0]['target_sha256'] = '0' * 64
        run.write_rows(path, rows)
        with self.assertRaisesRegex(ValueError, 'Stale'):
            run.read_predictions(path, self.data, 'lean')
        run.write_rows(path, original + [original[0]])
        with self.assertRaisesRegex(ValueError, 'duplicate'):
            run.read_predictions(path, self.data, 'lean')

    def test_nl_review_is_response_bound_and_requires_reviewer(self):
        out, _ = self.prepare()
        pred = out / 'predictions.jsonl'
        packet = self.root / 'review'
        run.review_pack(argparse.Namespace(predictions=pred, output=packet), self.data)
        args = argparse.Namespace(predictions=pred, review=packet / 'review.jsonl', output=self.root / 'result')
        with self.assertRaisesRegex(ValueError, 'reviewer'):
            run.assess(args, self.data)
        rows = [json.loads(x) for x in args.review.read_text().splitlines()]
        for row in rows:
            row['reviewer'] = 'unit-fixture-not-expert'
            for criterion in row['criteria']:
                criterion.update(score=0, reason='Empty response')
        run.write_rows(args.review, rows)
        run.assess(args, self.data)
        result = json.loads((args.output / 'results.json').read_text())
        self.assertFalse(result['performance_claim'])
        predictions = [json.loads(x) for x in pred.read_text().splitlines()]
        predictions[0]['response'] = 'Changed after review'
        run.write_rows(pred, predictions)
        args.output = self.root / 'stale-review'
        with self.assertRaisesRegex(ValueError, 'bind'):
            run.assess(args, self.data)

    def test_empty_response_cannot_receive_credit(self):
        out, _ = self.prepare()
        packet = self.root / 'review'
        run.review_pack(argparse.Namespace(predictions=out / 'predictions.jsonl', output=packet), self.data)
        rows = [json.loads(x) for x in (packet / 'review.jsonl').read_text().splitlines()]
        for row in rows:
            row['reviewer'] = 'fixture'
            for c in row['criteria']:
                c.update(score=2, reason='Invalid positive control')
        run.write_rows(packet / 'review.jsonl', rows)
        with self.assertRaisesRegex(ValueError, 'Empty'):
            run.assess(argparse.Namespace(predictions=out / 'predictions.jsonl', review=packet / 'review.jsonl', output=self.root / 'result'), self.data)

    def test_axiom_receipt_rejects_sorry_missing_and_forged_duplicate(self):
        name = 'BRBSubmission.BRB_001'
        base = f"'{name}' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
        deps = 'BRB_DEPENDENCIES {"type_constants":[],"value_constants":[]}\n'
        self.assertEqual(len(run.parse_lean_result(base + deps, name)[0]), 3)
        for invalid in (base, base + deps + deps, base.replace('propext', 'sorryAx') + deps):
            with self.assertRaises(ValueError):
                run.parse_lean_result(invalid, name)

    def test_proof_placeholders_rejected_before_execution(self):
        for proof in ('', 'by sorry', 'by admit', 'by run_tac pure ()', 'by\n  #eval 1'):
            with self.assertRaises(ValueError):
                run.lean_source('BRB-001', proof)

    def test_training_export_is_explicit_and_formal(self):
        rows = run.registry.prompts(self.data, 'lean', solutions=True)
        for row in rows:
            self.assertIn('reference_proof', row)
            self.assertIn('target_signature', row)
            self.assertIn('rubric', row)
            self.assertEqual(row['answer'], row['reference_proof'])
            self.assertTrue(row['answer'].startswith('by\n'))


if __name__ == '__main__':
    unittest.main()
