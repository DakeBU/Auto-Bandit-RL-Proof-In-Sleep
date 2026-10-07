"""Pre-use import adapter conserves every original shared-root byte."""
from common_v4 import *
p=RUN/'integrate-reader-v1.py';q=RUN/'integrate-reader-v2.py'
t=p.read_text(encoding='utf-8')
a="raw.rstrip(b'\\r\\n')+b'\\n'+line.encode()+b'\\n'"
b="raw+(b'' if raw.endswith(b'\\n') else b'\\n')+line.encode()+b'\\n'"
assert a in t;t=t.replace(a,b);compile(t,str(q),'exec');write(q,t)
write(RUN/'integration-root-prefix-pre-use-v2.json',dict(before_first_use=True,unused_original=p.as_posix(),effective_version=q.as_posix(),sha256=sha(q),reason='Preserve every original sharedrootTests raw byte as prefix before adding imports; avoid stripping CRLF/trailing blank lines. No executed integration failure or mathchange.',readonly_transport_diagnostic='Prior inlinePython string throughPowerShell failed parserquoting BEFOREPython started; savedhelper replaces transport, no repository/root mutation occurred.'))
print('Pre-use exactsharedrootprefixadapter prepared, no mathematical/publication mutation.')
