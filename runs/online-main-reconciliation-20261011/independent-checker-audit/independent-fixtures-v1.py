import sys,importlib.util,unittest,json
from pathlib import Path
root=Path(__file__).resolve().parents[2];candidate=root/'tmp/online-main-reconciliation-20261011/contributor-checker-candidate-v1';sys.path.insert(0,str(root))
import tools
spec=importlib.util.spec_from_file_location('tools.check_contributor_contract',candidate/'tools/check_contributor_contract.py');checker=importlib.util.module_from_spec(spec);sys.modules[spec.name]=checker;spec.loader.exec_module(checker);tools.check_contributor_contract=checker
spec=importlib.util.spec_from_file_location('review_candidate_tests',candidate/'tools/test_contributor_contract.py');tests=importlib.util.module_from_spec(spec);spec.loader.exec_module(tests)
class Additional(tests.HistoricalRows):
 def test_reviewer_nonancestor_base(self):
  self.integrate();actual=self.base;self.git('checkout','source');self.write('README','other\n');self.commit('unrelated extension');other=self.rev();self.git('checkout','main');self.base=other;self.assertIsNone(self.cert())
 def test_reviewer_merge_authored_manifest(self):
  raw=(self.root/self.manifest).read_bytes();self.git('rm',self.manifest);self.commit('remove before integration');self.integrate();self.write(self.manifest,raw.decode());self.commit('new after merge');self.assertIsNone(self.cert())
 def test_reviewer_manifest_existing_at_actual_base(self):
  raw=(self.root/self.source).read_text();m=(self.root/self.manifest).read_text();self.git('checkout','main');self.write(self.source,raw);self.write(self.manifest,m);self.commit('base already owns manifest');self.base=self.rev();self.git('merge','--no-ff','source','-m','merge');self.assertIsNone(self.cert())
 def test_reviewer_metadata_only_origin(self):
  self.git('checkout','main');self.write(self.source,(self.root/'README').read_text());self.commit('common source');common=self.rev();self.git('checkout','-b','metadata');self.write(self.manifest,json.dumps(dict(tests.base_contract(),affected_files=[self.source])));self.commit('only manifest');self.git('checkout','main');self.write('README','main extension');self.commit('actual base');self.base=self.rev();self.git('merge','--no-ff','metadata','-m','merge');self.assertIsNone(self.cert())
suite=unittest.defaultTestLoader.loadTestsFromModule(tests)
for name in ['test_reviewer_nonancestor_base','test_reviewer_merge_authored_manifest','test_reviewer_manifest_existing_at_actual_base','test_reviewer_metadata_only_origin']:suite.addTest(Additional(name))
result=unittest.TextTestRunner(verbosity=2).run(suite);sys.exit(0 if result.wasSuccessful() else 1)
