from leaf_driver import *
guard()
write(RUN/'full-public-wrapper-failures-v3.json',dict(actual_Lean_exit=0,proof_source_changed=False,compiler_rerun=False,wrapper_v1='Successful Lean output linewrapped the longer scalar identity name/list; line-ending assertion failed.',wrapper_v2='Multiline bracket parser found all11 names but comma-space split retained indentation; postprocessing assertion failed before creating review artifacts.',repair_v3='Strip whitespace individually from comma-delimited actual axiom names; enforce exact standard set. Reuse actual successful retained compiler receipt.'))
script=(RUN/'prepare-full-body-and-canary-v2.py').read_text(encoding='utf8')
old="set(a.replace('\\n',' ').split(', '))"
assert script.count(old)==1
script=script.replace(old,"{p.strip() for p in a.split(',')}")
script=script.replace('full-public-audit-wrapper-repair-v2.json','full-public-audit-wrapper-repair-v3.json')
exec(compile(script,str(RUN/'prepare-full-body-and-canary-v2.py')+':whitespace-normalized-v3','exec'))
