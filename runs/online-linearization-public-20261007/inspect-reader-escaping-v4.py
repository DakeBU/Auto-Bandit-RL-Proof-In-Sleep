"""Count actual decoded characters, not serialized JSON or repr escaping."""
from common_v2 import *
fixed();live='website/content/readings.json';snapshot=RUN/'snapshots/before-website--content--readings.json.txt'
assert sha(live)==sha(snapshot);reader=load(live);route=next(x for x in reader['readings'] if x['slug']==ROUTE);rows=[];slash=chr(92)
def visit(obj,pointer):
 if isinstance(obj,dict):
  for key,value in obj.items():
   ptr=pointer+'/'+key
   if key=='math':
    assert isinstance(value,str);runs=[dict(start=m.start(),length=len(m.group()),following_ordinals=[ord(c) for c in value[m.end():m.end()+7]]) for m in re.finditer(re.escape(slash)+'+',value)]
    rows.append(dict(JSON_pointer=ptr,decoded_value=value,decoded_UTF8_sha256=hashlib.sha256(value.encode('utf-8')).hexdigest(),backslash_runs=runs,max_run_length=max([r['length'] for r in runs],default=0),character_ordinals=[ord(c) for c in value]))
   else:visit(value,ptr)
 elif isinstance(obj,list):
  for i,value in enumerate(obj):visit(value,pointer+'/'+str(i))
visit(route,'/readings/slug=online-linearization');assert rows and all(r['max_run_length']<=1 for r in rows)
example=route['source_theorems'][0]['math'];assert example[5]==slash and ord(example[6])==114
sys.path.insert(0,str(ROOT/'website/scripts'));from build_site import normalize_math_source
normalized=normalize_math_source(example);assert normalized==slash+'['+example+slash+']'
write(RUN/'reader-escaping-verification-v4.json',dict(status='actual-decoded-single-backslashes-verified-no-serialization-repair-needed',live_path=live,live_sha256=sha(live),immutable_before_snapshot=snapshot.relative_to(ROOT).as_posix(),snapshot_sha256=sha(snapshot),fields=len(rows),rows=rows,generator_path='website/scripts/build_site.py',generator_sha256=sha('website/scripts/build_site.py'),actual_normalizer_output=normalized,example_ordinals_5_6=[ord(example[5]),ord(example[6])],no_reader_or_Lean_changes=True,failed_proposal=dict(helper=RUN.joinpath('prepare-reader-scope-v3.py').relative_to(ROOT).as_posix(),actual_exit_code=1,error='AssertionError: rows empty',guard_prevented_reader_mutation=True,reason='Review mistook raw JSON/repr escaping for duplicated decoded field characters'),original_CONTRACT_receipt_preserved=True,required_correction_review='reader-escaping-correction-v4, distinct source actor',actual_pixel_gate_still_pending=True,contract_version=2,new_proofs=0,chapter_complete=False,goal_complete=False))
fixed();print('Actual decoded fields',len(rows),'all backslash run lengths <=1; before/live raw equal; no TeX data change authorized or needed; pixels pending.')
