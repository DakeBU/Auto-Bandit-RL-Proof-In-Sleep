from common import *
fixed(True)
labels=['root-v1-01','Tests-v1-01','full-harness-v1-01','candidate-frontier-shadow-v1-01','contributor-exact-v1-01','scoped-diff-v1-01','history-bindings-v1-01','site-build-v1-01','site-check-v1-01','registry-v1-01','browser-v1-01']
# Native helper labels have their actual names without an artificial -01 suffix.
labels[3]='candidate-frontier-shadow-v1'
for label in labels:passed(label)
main=load(RUN/'contributor-main-diagnostic-v1-01-exit.json');assert main['exit_code']!=0
raw=(RUN/'contributor-main-diagnostic-v1-01.log').read_text(encoding='utf-8')
assert 'contract' in raw.lower();missing=re.findall(r'BanditRLProof/Online\w+\.lean',raw)
tests=(RUN/'full-harness-v1-01.log').read_text(encoding='utf-8')
m=re.search(r'Ran (\d+) tests',tests);assert m,'Full test count missing'
skip=re.search(r'skipped=(\d+)',tests);assert skip,'Skip count missing'
jobs={}
for label in ['root-v1-01','Tests-v1-01']:
 mm=re.search(r'Build completed successfully \((\d+) jobs\)',(RUN/(label+'.log')).read_text(encoding='utf-8'));assert mm;jobs[label]=int(mm.group(1))
registry=load(RUN/'registry-v1.json');assert registry['source_dirty'] is False and registry['lean_verified'] is True
write(RUN/'integrated-gates-overlay-v1.json',dict(status='passed-scoped-package-gates',actual_passed_gates=labels,root_Tests_jobs=jobs,full_tests=int(m.group(1)),existing_skips=int(skip.group(1)),site_source_commit=registry['source_commit'],site_source_dirty=False,site_lean_verified=True,preserved_base_IDs_URLs=10811,new_registry_nodes=0,canonical_links=4,curated_links=4,notation_entries=3,main_relative_gate=dict(status='failed-separate-diagnostic',log='contributor-main-diagnostic-v1-01.log',exit_code=main['exit_code'],missing_changed_paths=sorted(set(missing)),required_gaps_not_waived=True),scoped_whitespace_gate='Explicit exact raw command logs/source snapshots/PDF extraction exceptions enumerated; all production/JSON/scripts/ordinarydocs checked with CRLF-aware per-command option.',ignored_runtime_pycache_preserved=True,source_package_accepted=False,chapter_complete=False,goal_complete=False,merged=False,live=False))
print('Current integrated gates/rawhistory/clean10811node registry bound; separate main-relative missing Chapter1 contracts remain REQUIRED; distinct FINAL pending.')
