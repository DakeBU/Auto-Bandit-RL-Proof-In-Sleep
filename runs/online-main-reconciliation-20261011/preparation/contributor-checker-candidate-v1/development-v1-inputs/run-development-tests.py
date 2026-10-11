from pathlib import Path
import importlib.util, sys, unittest
root=Path(__file__).resolve().parent
repo=root.parents[2]
sys.path.insert(0,str(repo))
import tools

def load(name,p):
 s=importlib.util.spec_from_file_location(name,p);m=importlib.util.module_from_spec(s);sys.modules[name]=m;s.loader.exec_module(m);return m
c=load("tools.check_contributor_contract",root/"tools/check_contributor_contract.py")
c.ROOT=repo;c.PROCESS_MEMORY=repo/"runs/process_memory.json"
tools.check_contributor_contract=c
a=load("candidate_existing_tests",root/"tools/test_contributor_contract.py")
b=load("candidate_historical_tests",root/"tools/test_contributor_historical_rows.py")
suite=unittest.TestSuite([unittest.defaultTestLoader.loadTestsFromModule(m) for m in [a,b]])
r=unittest.TextTestRunner(verbosity=2).run(suite)
sys.exit(not r.wasSuccessful())
