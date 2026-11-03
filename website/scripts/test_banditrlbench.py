"""Regression checks for prompt leakage, split leakage and contract drift."""
import copy
import unittest
from website.scripts import banditrlbench as bench

class SeedTests(unittest.TestCase):
    def setUp(self):
        self.data=bench.load()

    def test_prompt_exports_hide_gold_in_both_tracks(self):
        for track in ('non-lean','lean'):
            for row in bench.prompts(self.data,track):
                self.assertNotIn('answer',row)
                self.assertNotIn('rubric',row)
                self.assertNotIn('reference_declaration',row)

    def test_contract_mutation_is_rejected(self):
        data=copy.deepcopy(self.data)
        data['cores'][0]['assumptions'].append('Additional independence assumption')
        with self.assertRaisesRegex(ValueError,'contract'):
            bench.validate(data)

    def test_source_rebinding_is_rejected(self):
        data=copy.deepcopy(self.data)
        data['cores'][0]['source_sha256']='0'*64
        with self.assertRaisesRegex(ValueError,'Source'):
            bench.validate(data)

    def test_track_views_share_core_contracts_and_exclude_planned(self):
        nl={row['core_id']:row for row in bench.prompts(self.data,'non-lean')}
        formal=bench.prompts(self.data,'lean')
        self.assertEqual(len(nl),4)
        self.assertEqual({row['core_id'] for row in formal},{'BRB-001','BRB-003'})
        for row in formal:
            for field in ('core_id','contract_hash','family_id','split','source_commit'):
                self.assertEqual(row[field],nl[row['core_id']][field])

if __name__=='__main__':unittest.main()
