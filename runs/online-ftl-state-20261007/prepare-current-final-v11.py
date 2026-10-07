from common_v1 import *
fixed(proving=True,integrated=True)
render=load(RUN/'formula-render-v4.json');browser=load(RUN/'formula-render-v4-browser.json')
assert len(render['images'])==31 and not browser['scrollViews']
assert load(RUN/'registry-v5-exit.json')['exit_code']==0 and load(RUN/'formula-render-v4-exit.json')['exit_code']==0
for x in render['images']:assert sha(x['path'])==x['sha256']
source=(RUN/'prepare-final-review-v6.py').read_text(encoding='utf-8')
source=source.replace('currentv4fullharness+scoped/source/contributor and site-v4/registry-v5/capture-v3 separately validated','currentreader-v5fullharness+scoped/source/contributor and clean site-v4/registry-v5/capture-v4 separately validated')
write(RUN/'prepare-final-review-v7.py',source)
write(RUN/'current-final-plan-v11.json',dict(active_FINAL_freezer='prepare-final-review-v7.py',freezer_sha256=sha(RUN/'prepare-final-review-v7.py'),active_execution_selection='publication-tools-before-FINAL-v6.json',selection_sha256=sha(RUN/'publication-tools-before-FINAL-v6.json'),current_registry='registry-v5.json',current_site='tmp/online-ftl-state-site-v4',current_capture='formula-render-v4.json',all31_images_individually_viewed_by_root_with_actual_view_image=True,actual_horizontal_formula_scrollers=0,current_complete_harness_tests=472,existing_skips=7,earlier_partial_registry4_retained_not_passed=True,chapter_complete=False,goal_complete=False))
