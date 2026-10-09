from common import *
bad=RUN/'record-acceptance-v1.py'
write(RUN/'delivery-helper-preparation-failure-v2.json',dict(command=['python','-B','-X','utf8','runs/online-ch2-prescient-cumulative-20261009/prepare-delivery-helpers-v2.py'],actual_tool_process_exit=1,observed_failure='All four prospective helper files were written; syntax compilation then rejected record-acceptance-v1.py because the generator expanded newline escapes inside one memory-digest string literal. None of these helpers was executed; no native acceptance/push/PR occurred.',invalid_helper_sha256=sha(bad),repair='Versioned record-acceptance-v2 replaces only the memory-digest write with a raw-source literal. Three other prospective helper syntax checks passed separately. Preserve invalid v1 and both generator failures.',whole_Goal_status='ACTIVE'))
s=bad.read_text(encoding='utf8')
a=s.index("write(RUN/'memory-digest-accepted-v1.md'")
b=s.index("write(RUN/'current-obligations-accepted-v1.json'",a)
replacement=r"""write(RUN/'memory-digest-accepted-v1.md','# '+TASK+'\n\n'+bound+'\n\nDistinct bounded FINAL '+sha(final)+'. Seven complete public VALUEs/standard-only axiom lists,7frozenheaders/nativefences;7selectednodes/1885coalesced directTYPE_VALUE presences/8production+5canaryVALUEpairs/four selected Eq.mprnumericbranches. Actual combinedroot/Tests/fullharness in full-harness-inspected-v1; exact math/pins unchanged after applicable gate. Clean repaired SITEv2 source '+load(RUN/'clean-candidate-site-binding-v2.json')['actual_head']+';11015oldregistryrecords+5production=11020. Actual local-file desktop14formulas/12root+distinct originals, notHTTP/live/mobile. Reader ambiguity/13field approved repair, resolver missing-field failure and two prospective helper generator failures preserved. No acceptance helper executed before acceptedFINAL. Compiler/native/semantic/site gates separate; postnative/delivery pending.\n')
"""
s=s[:a]+replacement+s[b:]
compile(s,'record-acceptance-v2.py','exec')
write(RUN/'record-acceptance-v2.py',s)
print('Only prospective memory string syntax repaired; no acceptance helper executed.')
