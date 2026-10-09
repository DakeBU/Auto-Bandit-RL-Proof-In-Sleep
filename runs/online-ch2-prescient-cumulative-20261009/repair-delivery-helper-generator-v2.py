from common import *
assert not (RUN/'record-acceptance-v1.py').exists()
write(RUN/'delivery-helper-preparation-failure-v1.json',dict(actual_tool_process_exit=1,command=['python','-B','-X','utf8','runs/online-ch2-prescient-cumulative-20261009/prepare-delivery-helpers-v1.py'],observed_failure='ValueError locating parent suffix: generator string interpreted backslash-n as newline. No generated acceptance/delivery helper was written and no acceptance/native/publication action ran.',repair='Version2 locates the unique suffix assignment prefix without newline-escape interpretation. All generated helper content/scope unchanged.',whole_Goal_status='ACTIVE'))
s=(RUN/'prepare-delivery-helpers-v1.py').read_text(encoding='utf8')
lines=s.splitlines()
hits=[i for i,line in enumerate(lines) if line.startswith('a=s.index("suffix = ')]
assert len(hits)==1
lines[hits[0]]="a=s.index(\"suffix = \ ".replace('\\ ', '')+"\");b=s.index('for p in docs:',a)"
# Construct the exact replacement as ordinary source; avoid any escaped newline search.
lines[hits[0]]='a=s.index("suffix = ");b=s.index(\'for p in docs:\',a)'
write(RUN/'prepare-delivery-helpers-v2.py','\n'.join(lines)+'\n')
print('Generator failure retained; exact unique-prefix repair ready.')
