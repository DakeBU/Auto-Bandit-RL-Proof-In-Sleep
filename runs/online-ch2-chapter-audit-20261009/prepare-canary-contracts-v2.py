from lower_common_v1 import *

reviewed(); headers(3)
old = CONTRACT/'nonsmooth-canary-contracts-v1.json'
c = load(old)
before = c['targets'][3]['exact_header']
after = before.replace('(e0 + t • e1)', '(e0 + (3 + t) • e1)')
assert before != after
c['targets'][3]['exact_header'] = after
c['targets'][3]['statement_hash'] = statement_hash(after)
c.update(version=2, supersedes_canary_proposal=dict(path=old.relative_to(ROOT).as_posix(), sha256=sha(old)),
    explicit_delta='Only C004 scalar tangential curve is translated so t=0 is the same point e0+3e1 used by the ambient nonsmooth conjunct. The v1 proposition is true and preserved; its two derivative assertions use different base points. No production terminal changed.',
    stage='frozen v2 canary proposition proposals before any canary proof BODY')
write(CONTRACT/'nonsmooth-canary-contracts-v2.json', c)
packet=(RUN/'nonsmooth-canary-blind-packet-v1.md').read_text(encoding='utf8')
assert '(e0 + t • e1)' in packet
packet=packet.replace('(e0 + t • e1)', '(e0 + (3 + t) • e1)')
write(RUN/'nonsmooth-canary-blind-packet-v2.md', packet)
write(RUN/'nonsmooth-canary-blind-input-v2.json', dict(
    packet_path=(RUN/'nonsmooth-canary-blind-packet-v2.md').as_posix(),
    packet_sha256=sha(RUN/'nonsmooth-canary-blind-packet-v2.md'),
    scope='Only this complete neutral packet and input JSON; reconstruct all five complete types, no source/proof/repository search. Reused staged actor history disclosed.'))
text='''import BanditRLProof.OnlineNonsmoothExamples
import Tests.OnlineGradientDescentSourceCanary
open scoped InnerProductSpace
open Tests.OnlineGradientDescentSource
'''
for t in c['targets']:
    short=t['declaration'].rsplit('.',1)[-1]
    binders,prop=t['exact_header'][len('theorem '+short):].split(' :\n',1)
    text+='\n#check ('+('∀'+binders+',\n' if binders.strip() else '')+prop+')\n'
write(RUN/'nonsmooth-canary-type-probe-v2.lean', text)
code, out=capture('nonsmooth-canary-type-probe-v2','lake','env','lean',RUN/'nonsmooth-canary-type-probe-v2.lean')
assert code == 0 and 'error:' not in out
write(CONTRACT/'nonsmooth-canary-operative-version-v2.json', dict(
    operative_path='docs/contracts/online-ch2-chapter-audit-v1/nonsmooth-canary-contracts-v2.json',
    operative_sha256=sha(CONTRACT/'nonsmooth-canary-contracts-v2.json'),
    preserved_v1_sha256=sha(old), preserved_blind_v1_sha256=sha(RUN/'nonsmooth-canary-blind-receipt-v1.json'),
    production_sha256=sha(PRODUCTION), production_terminal_hashes=[t['statement_hash'] for t in reviewed()['targets']],
    actual_complete_type_probe_sha256=sha(RUN/'nonsmooth-canary-type-probe-v2.json'),
    canary_BODY_authored=False, blind_v2_pending=True, BODY_review_pending=True,
    chapter_complete=False, whole_Goal_status='ACTIVE'))
reviewed(); headers(3)
print('v2 canary types elaborated; only explicit same-point tangential delta, all production headers unchanged.')
