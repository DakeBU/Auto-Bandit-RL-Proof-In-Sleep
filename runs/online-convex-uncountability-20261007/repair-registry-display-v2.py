"""Repair actual false raw-HTML QName check; verify assembled text AND canonical href."""
from common_v2 import *
fixed(True,True);assert load(RUN/'registry-v1-01-exit.json')['exit_code']==1
p=RUN/'verify-registry-v1.py';text=p.read_text(encoding='utf-8')
old="route=(site/'chapters/online-lipschitz/index.html').read_text(encoding='utf-8');assert PRE+'convex_uncountable_nondifferentiability' in route"
new="""from html.parser import HTMLParser
class ReaderText(HTMLParser):
 def __init__(self):super().__init__();self.text=[];self.hrefs=[]
 def handle_data(self,data):self.text.append(data)
 def handle_starttag(self,tag,attrs):
  if tag=='a':self.hrefs.extend(v for k,v in attrs if k=='href')
route=(site/'chapters/online-lipschitz/index.html').read_text(encoding='utf-8')
parsed=ReaderText();parsed.feed(route)
assert PRE+'convex_uncountable_nondifferentiability' in ''.join(parsed.text)
assert '../../'+nodes['declaration:'+PRE+'convex_uncountable_nondifferentiability']['url'] in parsed.hrefs"""
assert old in text
text=text.replace(old,new).replace("RUN/'registry-v1.json'","RUN/'registry-v2.json'")
write(RUN/'verify-registry-v2.py',text)
p=RUN/'render-source-card-v1.py';text=p.read_text(encoding='utf-8').replace("RUN/'registry-v1.json'","RUN/'registry-v2.json'")
write(RUN/'render-source-card-v2.py',text)
p=RUN/'audit-scope-v1.py';text=p.read_text(encoding='utf-8').replace("RUN/'source-scope-audit-v1.json'","RUN/'source-scope-audit-v3.json'")
write(RUN/'audit-scope-v3.py',text)
write(RUN/'registry-display-repair-v2.json',dict(failed_attempt='registry-v1-01',reason='Actual complete QName has wordbreak tags in generated route HTML; literal raw string assertion produced false negative.',repair='Parse actual rendered text to reassemble QName and separately verify exact href to canonical shared node. OldIDURL preservation, two compiled native fingerprints, same Book mapping, sourcecard counts and module-name checks all retained.',old_verifier_preserved=True,current_source_reader_and_Lean_bytes_unchanged=True,applicable_current_reader_harness='full-harness-v2-01',source_package_accepted=False,chapter_complete=False,goal_complete=False))
event('repair',dict(reason='raw HTML wordbreak false-negative',repair=(RUN/'registry-display-repair-v2.json').as_posix(),targets_and_reader_unchanged=True),attempt='registry-v2')
fixed(True,True);print('Actual registry rendering assertion repaired via semantic text AND exact canonical href; all original guards preserved.')
