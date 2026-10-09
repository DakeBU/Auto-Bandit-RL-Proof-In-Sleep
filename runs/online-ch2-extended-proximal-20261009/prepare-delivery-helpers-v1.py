from publication_guard_v1 import *
fixed()
prior = ROOT / 'runs/online-ch2-bregman-20261009'
def adapted(name):
    s = (prior / name).read_text(encoding='utf8')
    for a, b in [
        ('codex/research-online-ch2-proximal', 'codex/research-online-ch2-bregman'),
        ('71f2219fa1648094eba8aa17b50e443258f436cb', BASE),
        ('69aeeeaf58364177a06bbc10329ea328c3c13b3c', '2b929d03d7ace7c418986e429d0ccf317a2721c6'),
        ('online-ch2-bregman-delivery', 'online-ch2-extended-proximal-delivery'),
        ('PR208', 'PR209'), ('PR #208', 'PR #209'), ("'208'", "'209'"),
        ('new Bregman PR', 'new extended-loss bridge PR'),
        ('Bregman proof PR delivery', 'extended-loss proof PR delivery'),
        ('Bregman proof verification', 'extended-loss proof verification')]:
        s = s.replace(a, b)
    return s
s = adapted('deliver-v1.py')
s = s.replace("assert r['native_verdict']==r['metadata_verdict']==r['prospective_publication_prose_verdict']=='accepted-with-explicit-delta'", "assert all(r[k] in ['accepted','accepted-with-explicit-delta'] for k in ['native_verdict','metadata_verdict','prospective_publication_prose_verdict'])")
a = s.index("code,out=capture('acceptance-full-package-diff-v1'")
b = s.index('rawrows=[]', a)
s = s[:a] + "capture('acceptance-full-package-diff-v1','git','diff','--cached',BASE,'--check')\n" + s[b:]
a = s.index("full=observe('final-package-diff-full'")
b = s.index("staged=observe('final-staged-scope'", a)
s = s[:a] + "observe('final-package-diff-full',['git','diff','--cached',BASE,'--check'])\n" + s[b:]
assert 'RAW-format-review' not in s and 'expected' not in s and 'PR208' not in s
write(RUN / 'deliver-v1.py', s)
s = adapted('collect-actual-delivery-v1.py')
a = s.index("write(RUN/'actual-delivery-packet-v1.md'")
b = s.index('paths={p for d', a)
packet = '''# Actual extended-loss bridge PR delivery review

Independently inspect exact durable delivery receipts, clean delivered head equals remote and OPENdraft unmerged PR, exact title/body/base/head, parentPR209 exact65e21be78abfbd4255798e54265ce418651ef70f, two current nonempty contributor gates and scoped staging. Full current-package whitespace actual0 without exceptions; parent historical RAW unchanged. Preserve RAW/Git CRLF differences via exact snapshots. Official successful attachment tool result is durably bound. Independently hash all actual-delivery inputs before/after and trace permitted FINAL/postnative transitions. No current proof/reader/native input mutation. Actual site applies to source2b929d03d7ace7c418986e429d0ccf317a2721c6, not a later-head fresh-site claim. Prior HTTP rejection retained; local-file15pixels are not HTTP/live/mobile evidence.

Review final-evidence-delivery-v1.py: only NEW OWN RUN delivery/review artifacts and exact RAW snapshot may be committed/pushed, then ignored terminal observations compare new remote/PR head and unchanged title/body/base/draft/unmerged. No self-referential evidence loop, existing source/reader/native mutation, merge/deploy/retirement/global credentials. Three bounded accepted bridge proofs3->0/no new defs, two public canaries/one generated Test auxiliary separately inventoried, not full source/Chapter2 closure. All8forwards/general source REQUIRED/OPEN, whole16GoalACTIVE.

Create-only actual-delivery-review-v1.md/json: verdict, actual_delivery_verdict, prospective_evidence_only_commit_verdict, required_repairs, input/report SHAs and independent RAW before/after, actual delivered head/PR/official attachment bindings. Reviewer must not publish or edit inputs. Distinct staged automated requested Astra/medium, no human/external/runtime attestation.
'''
s = s[:a] + "write(RUN/'actual-delivery-packet-v1.md', " + repr(packet) + ')\n' + s[b:]
write(RUN / 'collect-actual-delivery-v1.py', s)
s = adapted('final-evidence-delivery-v1.py')
s = s.replace("assert review['verdict']=='accepted-with-explicit-delta' and not review['required_repairs']", "assert review['verdict'] in ['accepted','accepted-with-explicit-delta'] and not review['required_repairs']")
a = s.index("fixed();exc=")
b = s.index("obs('commit'", a)
s = s[:a] + "fixed()\nobs('full-package-whitespace',['git','diff','--cached',BASE,'--check'])\n" + s[b:]
assert 'RAW-format-review' not in s and 'exc=' not in s
write(RUN / 'final-evidence-delivery-v1.py', s)
for n in ['record-acceptance-v1.py', 'deliver-v1.py', 'collect-actual-delivery-v1.py', 'final-evidence-delivery-v1.py']:
    compile((RUN / n).read_text(encoding='utf8'), n, 'exec')
print('Create-only scoped delivery helpers prepared and syntax inspected; no acceptance/publication executed.')
