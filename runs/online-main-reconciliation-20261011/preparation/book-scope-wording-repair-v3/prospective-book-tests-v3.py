import sys,json,unittest
from pathlib import Path
from unittest.mock import patch
root=Path(__file__).resolve().parents[3];sys.path.insert(0,str(root))
from tools import test_book_registry as tests
site=tests.site
original=site.load_json
exact=site.CONTENT_DIR/'chapters.json'
candidate=Path(__file__).parent/'chapters.json'
original_ROOT=site.ROOT
counts={'candidate_reads':0,'delegated_reads':0}
def loader(path):
 if path==exact:
  counts['candidate_reads']+=1
  return json.loads(candidate.read_bytes())
 counts['delegated_reads']+=1
 return original(path)
with patch.object(site,'load_json',side_effect=loader):
 result=unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromModule(tests))
assert site.ROOT==original_ROOT and site.load_json is original
print(json.dumps({'loader_counts':counts,'tests_run':result.testsRun,'ROOT_unchanged':True,'scope':'development candidate overlay only'}))
sys.exit(0 if result.wasSuccessful() and result.testsRun==37 and counts['candidate_reads']>0 else 1)
