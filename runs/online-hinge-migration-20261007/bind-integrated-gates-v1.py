"""Bind actual passed gates and root's actual pixel observations; do not self-certify FINAL."""
from common_v2 import *
fixed(True);b=load(RUN/'browser-v1-binding.json');image=Path(b['snapshot']);assert sha(image)==b['snapshot_sha256']
dest=RUN/'reader-first-viewport-v1.png';write(dest,image.read_bytes())
images=[dest,RUN/'source-card-01-v1.png']
write(RUN/'formula-visual-review-v1.json',dict(status='passed-actual-pixel-inspection',actor='/root',actual_view_image=True,inspected_images=[dict(path=p.as_posix(),sha256=sha(p)) for p in images],observations=['Actual desktop first viewport: source-qualified hinge title/one-example-three-branch scope/source-vs-canonical route boundary readable. No mobile/fullpage certification.','Actual full source card: hinge formula and all three margin conditions legible; full inclusive alpha segment, definition/helper binder scopes, generic-S/proper-instance distinction and z0 positive-margin boundary readable. One actual MathJax container, zero errors.'],first_viewport_view_tool_may_resize=True,sourcecard_original_dimensions=True,generated_site_unmodified=True,not_SOURCE_FINAL_acceptance=True))
labels=['root-v1-01','Tests-v1-01','full-harness-v1-01','candidate-frontier-shadow-v1','contributor-exact-v1-01','scoped-diff-v1-01','history-bindings-v1-01','site-build-v1-01','site-check-v1-01','registry-v1-01','browser-v1-01','formula-render-v1-01','source-card-renderer-syntax-v1-01']
for label in labels:passed(label)
main=load(RUN/'main-relative-required-gaps-v1.json');assert len(main['missing_required_changed_paths'])==9 and main['required_gaps_not_waived']
s=(RUN/'full-harness-v1-01.log').read_text(encoding='utf-8');tests=re.search(r'Ran (\d+) tests',s);skip=re.search(r'skipped=(\d+)',s);assert tests and skip and 'check passed' in s
jobs={}
for label in ['root-v1-01','Tests-v1-01']:
 m=re.search(r'Build completed successfully \((\d+) jobs\)',(RUN/(label+'.log')).read_text(encoding='utf-8'));assert m;jobs[label]=int(m.group(1))
registry=load(RUN/'registry-v1.json');assert registry['source_dirty'] is False and registry['lean_verified'] is True and len(registry['checks'])==15
corrections=[load(RUN/n) for n in ['API-pre-use-qualification-v2.json','reader-pre-use-clarification-v2.json','readonly-lookup-diagnostics-v1.json','readonly-template-lookup-v2.json']]
write(RUN/'integrated-gates-overlay-v1.json',dict(status='passed-scoped-package-gates',actual_passed_gates=labels,root_Tests_jobs=jobs,full_tests=int(tests.group(1)),existing_skips=int(skip.group(1)),site_source_commit=registry['source_commit'],site_source_dirty=False,site_lean_verified=True,preserved_base_IDs_URLs=10811,new_registry_nodes=0,canonical_public_nodes=15,highlight_links=4,curated_links=4,notation_entries=3,source_cards=1,main_relative_gate=main,scoped_whitespace_gate='Explicit exact raw command logs/source snapshots/PDF extraction/pre-integration MANIFEST/actual browser DOM exceptions; production/JSON/scripts/ordinary docs checked with CRLF-aware command option.',failure_repairs=[],pre_use_corrections_and_readonly_diagnostics=corrections,source_package_accepted=False,chapter_complete=False,goal_complete=False,merged=False,live=False))
print('Applicable combined/history/clean shared registry/actual firstviewport+formula pixels bound; FINAL source review pending, totalGoalACTIVE.')
