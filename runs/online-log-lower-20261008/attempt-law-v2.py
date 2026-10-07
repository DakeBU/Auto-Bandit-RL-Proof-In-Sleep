from common_v1 import *
write(RUN/'law-repair-v2.json',dict(
    prior_exit=load(RUN/'law-attempt-v1-exit.json')['exit_code'],
    prior_log_sha256=sha(RUN/'law-attempt-v1.log'),
    cause='Shared measure theorem lambda inference needs explicit finite-history type in its standalone application.',
    correction='Annotate proof-local lambda parameters as List.Vector Bool T; exact public headers and definitions untouched.',
    mathematical_contract_version=1,target_changed=False))
original=(RUN/'leaves/law-v1.lean').read_text(encoding='utf-8')
addition=(RUN/'law-addition-v1.lean.txt').read_text(encoding='utf-8')
old='univ (fun v => pathWeight v.toList) (prefix_distribution T)'
new='univ (fun v : List.Vector Bool T => pathWeight v.toList) (prefix_distribution T)'
assert original.count(old)==2 and addition.count(old)==2
fixed_source=original.replace(old,new).replace('(fun v => f v.toList)\nend', '(fun v : List.Vector Bool T => f v.toList)\nend')
fixed_addition=addition.replace(old,new).replace('(fun v => f v.toList)', '(fun v : List.Vector Bool T => f v.toList)')
write(RUN/'leaves/law-v2.lean',fixed_source)
write(RUN/'law-addition-v2.lean.txt',fixed_addition)
gate('law-attempt-v2','lake','env','lean',RUN/'leaves/law-v2.lean')
print('Actual probability law chain compiled in versioned leaf; public promotion remains separate.')
