from common_reviewed_v1 import *
reviewed_fixed()
assert load(RUN/'body-audit-driver-v2-exit.json')['exit_code']==1
assert load(RUN/'all-axioms-v1-exit.json')['exit_code']==0
assert PUBLIC.read_bytes()==(RUN/'public-candidate-v2.lean.raw').read_bytes()
assert CANARY.read_bytes()==(RUN/'canary-candidate-v2.lean.raw').read_bytes()
write(RUN/'audit-python-repair-v3.json',dict(failed_driver='body-audit-driver-v2',reason='Configured Python lacks str.removeprefix (Python <3.9). Thirty-four actual axioms checks completed before generator failed.',repair='Use exact checked theorem-name prefix length slicing in this local artifact generator; resume after applicable axiom gate without rerunning it.',source_or_terminal_changed=False,public_sha256=sha(PUBLIC),canary_sha256=sha(CANARY)))
s=(RUN/'audit-bodies-v2.py').read_text(encoding='utf8');s=s[s.index('# Remove only'):]
s=s.replace("rest=h.removeprefix('theorem '+short).strip()", "assert h.startswith('theorem '+short)\n rest=h[len('theorem '+short):].strip()")
prefix="from common_reviewed_v1 import *\nimport re\nreviewed_fixed()\nsys.path.insert(0,str(ROOT))\nfrom tools.abrl_lifecycle import lean_declaration_header\nPRE='BanditRL.OnlineLearning.';TEST='NoRegretSemanticsProbe.'\ntargets=load(CONTRACT/'targets-v1.json')['targets']\nactual=load(RUN/'actual-public-canary-headers-v1.json')\nreuse=load(CONTRACT/'targets-v1.json')['existing_reuse']\naudit=load(RUN/'axiom-bindings-v1.json');names=audit['names'];axioms=audit['axioms']\n"
write(RUN/'audit-bodies-v3.py',prefix+s)
gate('body-audit-driver-v3',sys.executable,'-B','-X','utf8',RUN/'audit-bodies-v3.py')
reviewed_fixed()
