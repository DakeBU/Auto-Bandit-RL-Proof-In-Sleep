"""Propose a precise TeX serialization exception; no reader changes here."""
from common_v2 import *
fixed();path='website/content/readings.json';d=load(path);index=next(i for i,x in enumerate(d['readings']) if x['slug']==ROUTE);route=d['readings'][index];rows=[]
def visit(obj,pointer):
 if isinstance(obj,dict):
  for key,value in obj.items():
   ptr=pointer+'/'+key
   if key=='math' and isinstance(value,str) and '\\\\' in value:
    corrected=value.replace('\\\\','\\');assert '\\\\' not in corrected
    rows.append(dict(JSON_pointer=ptr,before=value,after=corrected,before_string_sha256=hashlib.sha256(value.encode('utf-8')).hexdigest(),after_string_sha256=hashlib.sha256(corrected.encode('utf-8')).hexdigest(),only_change='Remove one duplicate escaping backslash before existing TeX tokens; mathematical letters/indices/operators/constants and source equations unchanged'))
   else:visit(value,ptr)
 elif isinstance(obj,list):
  for i,value in enumerate(obj):visit(value,pointer+'/'+str(i))
visit(route,'/readings/'+str(index));assert rows
write(CONTRACT/'reader-scope-addendum-v3.json',dict(stage='proposed-reader-only-format-repair',Lean_contract_version=2,reader_scope_version=3,source_and_actual_Lean_statements_unchanged=True,file=path,before_live_file_sha256=sha(path),immutable_before_snapshot=RUN.joinpath('snapshots/before-website--content--readings.json.txt').relative_to(ROOT).as_posix(),rows=rows,scope='Exception to contract-v2 preserve-math-strings: ONLY these exact existing route math-field duplicate-backslash corrections. No new formula, source hypothesis, term, constant, target or proof changes.',applied=False,required_review='Distinct BODY reviewer must explicitly accept this addendum before application; FINAL must verify actual correct glyphs and pixel visibility, not just MathJax error count.',new_proofs=0,new_definitions=0,new_registry_nodes=0,chapter_complete=False,goal_complete=False))
write(CONTRACT/'reader-scope-addendum-v3.md','''# Version3 reader-scope addendum; Lean contract stays version2

Actual old online-linearization math strings contain duplicated literal backslashes. Source reviewer independently confirmed the before-reader bytes and that build_site.normalize_math_source does not collapse them. This is a serialization blocker: zero MathJax errors alone would not establish correct source formulas. The exact before/after field list is in reader-scope-addendum-v3.json, with raw file and individual string hashes.

This PROPOSED explicit exception replaces only the blanket string-preservation requirement for listed duplicate-backslash math fields of this one existing route. Remove exactly one escaping slash per duplicated token. Preserve all mathematical letters, operators, indices, signs, constants, quantifiers and equations; no line-break syntax is intended in these fields. Preserve all other formulas, other Books, curated links, source IDs/URLs and underlying registry. Actual18 Lean terminals/9defs/3abbr and whole25canaryproofs/8defs/2abbr stay unchanged. Existing source/Lean contract remains v2; reader edit scope advances to v3 without claiming new mathematics. Original v1/v2 contracts/input rows, source reviewer discovery, before snapshots and proposed repairs all remain separately preserved.

Do NOT apply before distinct BODY reviewer explicitly accepts this proposed addendum. After application run actual combined root/Tests/full harness, applicable clean local Lean-verified site, registry, and actual rendered first viewport/full source card plus algorithm/bridge/worked-example formulas. Check correct operators and notation, no literal command text or hidden title, no MathJax errors. FINAL reviewer verifies exact before/after listed changes and current live-reader raw bindings separately. No silent source rewrite or equivalence from compilation alone; no main/live, chapter or Goal completion.
''')
write(RUN/'reader-serialization-proposal-v3.json',dict(status='proposed-not-applied',source_reviewer_confirmation='Actual /root/source_reviewer message independently confirms duplicate backslashes and generator behavior; formal receipt pending',addendum=(CONTRACT/'reader-scope-addendum-v3.json').as_posix(),addendum_sha256=sha(CONTRACT/'reader-scope-addendum-v3.json'),fields=len(rows),site_reader_bytes_unchanged=True,actual_Lean_contract_version=2,reader_scope_version=3))
fixed();print('Explicit proposed reader-only serialization repair frozen:',len(rows),'fields; current reader/Lean unchanged, separate review required.')
