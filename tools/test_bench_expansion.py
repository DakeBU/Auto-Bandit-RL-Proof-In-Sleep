import argparse
import copy
import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from tools import bench_expansion as bench


class ExpansionTests(unittest.TestCase):
    def test_each_family_keeps_views_and_aliases_in_public_dev(self):
        families=bench.read(bench.BENCH/'expansion/families.json')['families']
        self.assertEqual(len(families),2)
        ids=[]
        for family in families:
            abilities=set()
            for identity in family['task_ids']:
                p,task,_=bench.package(identity)
                self.assertEqual(task['family'],family['id'])
                self.assertEqual(task['split'],'dev')
                self.assertFalse(family['held_out_eligible'])
                abilities.add(task['ability']);ids.append(identity)
                self.assertTrue(set(task['solution_aliases'])<=set(family['solution_aliases']))
            self.assertEqual(abilities,{'knowledge','reasoning','agentic-lean'})
        self.assertEqual(len(ids),len(set(ids)))

    def test_exports_require_solution_opt_in(self):
        with tempfile.TemporaryDirectory() as td:
            for include in (False,True):
                out=Path(td)/str(include)
                bench.export(argparse.Namespace(output=out,split='dev',include_solutions=include))
                path=out/('training-with-solutions.jsonl' if include else 'prompts.jsonl')
                rows=[json.loads(x) for x in path.read_text(encoding='utf-8').splitlines()]
                self.assertEqual(len(rows),6)
                for row in rows:
                    self.assertEqual('training_solution' in row,include)
                    self.assertFalse(any(k.startswith(('solution','tests')) for k in row['workspace']))
            with self.assertRaisesRegex(ValueError,'Only public dev'):
                bench.export(argparse.Namespace(output=Path(td)/'hidden',split='test',include_solutions=False))

    def test_extra_target_seal_rejects_changed_conclusion(self):
        p,task,env=bench.package('BRB-IW-L')
        with tempfile.TemporaryDirectory() as td:
            root=Path(td)
            import shutil
            shutil.copytree(p,root/'tasks'/p.name)
            target=root/'tasks'/p.name/'environment/workspace/target.json'
            t=bench.read(target);t['signature']=': True';bench.write(target,t)
            with patch.object(bench,'BENCH',root),self.assertRaisesRegex(ValueError,'Changed contract'):
                bench.package(p.name)

    def test_response_binding_prevents_reusing_reference_judgment(self):
        p,_,_=bench.package('BRB-BE-R')
        with self.assertRaisesRegex(ValueError,'Stale response'):
            bench.nl_check(p,'reference','The transition matrix is strictly contractive.')
        for label in ('no-op','wrong-answer','placeholder'):
            response=(p/f'tests/controls/{label}.txt').read_text(encoding='utf-8')
            self.assertEqual(bench.nl_check(p,label,response)['status'],'fail')

    def test_proof_only_submission_and_axiom_receipts(self):
        p,_,_=bench.package('BRB-BE-L')
        target=bench.read(p/'environment/workspace/target.json')
        for attack in ('','by sorry','by\n  axiom fake : False','by\n  run_cmd Lean.logInfo "pass"', 'by\n  exact True.intro\n#print axioms fake'):
            with self.assertRaises(ValueError): bench.source_for(target,attack,'T')
        with self.assertRaisesRegex(ValueError,'Unapproved axiom'):
            bench.parse_lean_result("'T' depends on axioms: [sorryAx]\nBRB_DEPENDENCIES {\"type_constants\":[],\"value_constants\":[]}",'T')


if __name__=='__main__': unittest.main()
