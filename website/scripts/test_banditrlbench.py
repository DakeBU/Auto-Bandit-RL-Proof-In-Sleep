"""Regression checks for prompt leakage, split leakage and contract drift."""
import copy
import unittest
from website.scripts import banditrlbench as bench
from website.scripts.check_site import LinkCollector, check_benchmark_source_bindings

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

    def evidence_collector(self):
        collector=LinkCollector()
        for core in self.data['cores']:
            collector.feed(f'<a href="https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/blob/{core["source_commit"]}/{core["source_file"]}" data-benchmark-core="{core["core_id"]}" data-benchmark-contract="{core["contract_hash"]}" data-benchmark-snapshot="{core["source_commit"]}">Frozen source</a>')
        return collector

    def test_frozen_evidence_is_not_current_declaration_certificate(self):
        collector=self.evidence_collector()
        self.assertEqual(collector.source_links,[])
        self.assertEqual(collector.source_link_count,0)
        self.assertEqual(check_benchmark_source_bindings(collector,'banditrlbench/non-lean/index.html',self.data['cores']),[])
        self.assertTrue(check_benchmark_source_bindings(collector,'index.html',self.data['cores']))

    def test_frozen_evidence_rejects_wrong_hash_url_and_missing_core(self):
        for field in ('href','data-benchmark-contract','data-benchmark-snapshot'):
            collector=self.evidence_collector()
            collector.benchmark_source_links[0][field]='invalid'
            self.assertTrue(check_benchmark_source_bindings(collector,'banditrlbench/non-lean/index.html',self.data['cores']))
        collector=self.evidence_collector()
        collector.benchmark_source_links.pop()
        self.assertTrue(check_benchmark_source_bindings(collector,'banditrlbench/non-lean/index.html',self.data['cores']))

    def test_unmarked_historical_link_stays_in_current_source_gate(self):
        collector=LinkCollector()
        collector.feed('<a href="https://github.com/DakeBU/Auto-Bandit-RL-Proof-In-Sleep/blob/old/BanditRLProof/Test.lean">source</a>')
        self.assertEqual(len(collector.source_links),1)
        self.assertEqual(collector.benchmark_source_links,[])

if __name__=='__main__':unittest.main()
