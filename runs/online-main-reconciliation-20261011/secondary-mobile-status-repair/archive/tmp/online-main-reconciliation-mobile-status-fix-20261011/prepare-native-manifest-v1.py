import copy, hashlib, importlib.util, json, pathlib
ROOT = pathlib.Path(__file__).resolve().parents[2]
OUT = pathlib.Path(__file__).resolve().parent
old = ROOT / 'research-wiki/contribution-contracts/ONLINE-MAIN-MOBILE-GRID-20261011.json'
obj = copy.deepcopy(json.loads(old.read_bytes()))
obj['id'] = 'ONLINE-MAIN-MOBILE-STATUS-20261011'
obj['route'] = 'shared-library/online-source-card-mobile-status'
obj['source']['title'] = 'Measured source-card status and long-prose wrapping repair'
obj['source']['version'] = 'Prepared on clean4034; candidate CSS SHA5b126bf7c0739879b941dfddba81fef3ae3ba9819c06d24cac6b805c5c29698c'
obj['source']['anchor'] = 'ReaderV9 actual390 clipping retained; candidate plan04d3c629411e66fa235d16dc83bf8484f8815f6c38a2db296351bed3552b05c9; distinct CSS review4e78d2364214becbc8a66eb86cbe4220fb105e876078d8008ca02fcd2c7ecf03'
obj['target'] = 'Wrap source status rows/badges and diagnostic-confirmed long source-card prose and contract dd. Preserve all text, mathematical statements, proof bodies, intentional formula scrolling and inherited registry multiplicities. Simulated23-card dual-width geometry is bounded evidence only; actual new-source complete reader/gates remain pending.'
obj['reuse_plan']['searched_existing'] = ['Existing source card/status/summary/prose/contract selectors; actual V9 clipping report;23-card simulated diagnostic.']
obj['reuse_plan']['decision_reason'] = 'Reuse existing content and markup; narrowly wrap measured overflowing badges and long declaration names, without mathematical changes.'
obj['semantic_roundtrip']['remaining_semantic_delta'] = 'No mathematical delta. Candidate CSS has distinct application review, while complete actual reader verification remains pending.'
obj['graph_contribution']['visual_review'] = 'Distinct CSS review and simulated original pixels bound; actual new-source reader/pixel acceptance pending.'
obj['verification']['focused_checks'] = ['Exact reviewed insertions reconstruct original RAW when removed.', 'Simulated23 cards at1440/390 have no horizontal overflow; subsequent helper failures retained.', 'No changed mathematical source or hidden clipping; full actual new-source reader verification pending.']
obj['learning_contract']['salvage']['reason'] = 'Actual V9 statusbadge clipping and all simulated exit1 evidence retained. Preserve narrower candidate failure; helper ACTIVE case and responsive wrap initial-state defects are separately repaired, never mathematical failures or reader success.'
obj['learning_contract']['parallelism']['direction_fingerprints'] = ['mobile-source-card-status-prose-wrap-repair']
obj['learning_contract']['cross_route_blind_spot_audit']['canonical_route'] = 'Bound source badge widths and wrap long text in measured source-card prose/contract entries'
obj['learning_contract']['reader_backpressure']['exposition_evidence'] = 'Distinct CSS bounded review; actual production reader and final pixels still pending.'
target = OUT / 'native-contribution-manifest-draft-v1.json'
with target.open('x', encoding='utf-8', newline='\n') as f:
    json.dump(obj, f, indent=2, ensure_ascii=False); f.write('\n')
spec = importlib.util.spec_from_file_location('native_contract', ROOT/'tools/check_contributor_contract.py')
module = importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
data, errors = module.validate_contract(target)
assert not errors, errors
print(json.dumps(dict(path=target.relative_to(ROOT).as_posix(),sha256=hashlib.sha256(target.read_bytes()).hexdigest(),native_validation_errors=errors,installed=False)))
