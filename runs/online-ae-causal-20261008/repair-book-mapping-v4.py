from common_reader_v3 import *
fixed_integrated()
assert load(RUN/'site-build-v3-exit.json')['actual_exit']==0
assert load(RUN/'site-check-v3-exit.json')['actual_exit']==0
assert load(RUN/'registry-check-v3-exit.json')['actual_exit']==1
p=ROOT/'website/content/chapters.json'
write(RUN/'snapshots/chapters-before-Book-map-repair-v3.raw',p.read_bytes())
d=load(p);row=next(x for x in d['chapters'] if x['slug']==ROUTE)
module=PUBLIC.relative_to(ROOT).as_posix()
assert module not in row['module_globs']
before=list(row['module_globs']);row['module_globs'].append(module)
p.write_bytes((json.dumps(d,ensure_ascii=False,indent=2)+'\n').encode('utf8'))
write(RUN/'book-mapping-repair-v4.json',dict(actual_failed_registry_receipt='registry-check-v3-exit.json',
    actual_prior_site_build_passed=True,actual_prior_site_check_passed=True,
    actual_failure='The new module was not associated with online-foundations; its actual new registry nodes defaulted to bandit/foundations.',
    exact_field='online-foundations.module_globs',old=before,new=row['module_globs'],
    required_action='Append only the actual owning module path so three new declarations project into the same Online Learning Book registry.',
    BODY_future_scope_relation='Implements the explicitly required same-shared-registry mapping of the three actual declarations; this precise module_globs field was omitted from the earlier helper and is separately flagged for reviewer audit.',
    old_IDs_URLs_statement_hashes_unchanged=True,no_new_Lean_target=True,public_canary_pins_unchanged=True,
    chapter_status_or_original16_or_null_total_unchanged=True,chapter_complete=False,goal_complete=False))
print('Exact new module associated with the existing Online Learning route; no Lean or chapter-status change.',flush=True)
