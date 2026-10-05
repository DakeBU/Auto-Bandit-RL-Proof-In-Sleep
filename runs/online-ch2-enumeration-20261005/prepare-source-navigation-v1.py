"""Draft navigation anchors only; inclusive source excerpts are not frozen contracts."""
from pathlib import Path
import json,hashlib,re
run=Path(__file__).parent
p=Path('tmp/online-ch2-enumeration-source20-35.txt');raw=p.read_bytes();s=raw.decode('utf-8')
assert hashlib.sha256(raw).hexdigest()=='adc5b396aa3d32dff754c77dbd05d708e967d4c88eddad78c97cf34e47e9b935'
inventory=json.loads(Path('docs/contracts/online-book-v1/source-inventory.json').read_text(encoding='utf-8'))
expected={int(re.search(r'2\.(\d+)',x['source_id']).group(1)):x for x in inventory['items'] if re.fullmatch(r'(Remark|Definition|Theorem|Lemma|Proposition|Example) 2\.\d+',x['source_id'])}
assert set(expected)==set(range(1,33))
found=[]
for n,x in expected.items():
    m=re.search(r'(?m)^'+re.escape(x['source_id'])+r'(?=\D|$)',s);assert m,x['source_id']
    physical=int(re.findall(r'PHYSICAL PAGE (\d+)',s[:m.start()])[-1]);assert physical==x['pdf_page'],x['source_id']
    found.append((m.start(),x,physical))
for a in ['Algorithm 2.1','Algorithm 2.2']:
    m=re.search(r'(?m)^'+re.escape(a)+r'(?=\D|$)',s);assert m,a
    physical=int(re.findall(r'PHYSICAL PAGE (\d+)',s[:m.start()])[-1])
    found.append((m.start(),dict(source_id=a,pdf_page=physical,printed_page=physical-12,kind='Algorithm',required=True),physical))
found.sort(key=lambda x:x[0]);rows=[]
for i,(start,x,physical) in enumerate(found):
    end=found[i+1][0] if i+1<len(found) else s.index('2.2.3',start) if '2.2.3' in s[start:] else s.index('PHYSICAL PAGE 33',start)
    fragment=s[start:end]
    rows.append(dict(source_id=x['source_id'],printed_page=physical-12,pdf_page=physical,kind=x['kind'],
        source_context_fragment=fragment,source_fragment_sha256=hashlib.sha256(fragment.encode('utf-8')).hexdigest(),
        required=x.get('required',True),historical_lean_name=x.get('lean_name'),historical_lean_names=x.get('lean_names'),
        historical_status=x.get('status','unreconciled'),statement_audit='draft:inclusive source context, not yet frozen precise semantic signature',
        reason_if_nonmathematical='Remark2.1 is pedagogical prose about the need for proof, not an excluded formal result.' if not x.get('required',True) else None))
assert len(rows)==34
result=dict(stage='source-navigation-draft',chapter=2,source_version='arXiv1912.13213v10',
    source_sha256=inventory['source_sha256'],source_extract_path=p.as_posix(),source_extract_sha256=hashlib.sha256(raw).hexdigest(),
    numbered_main_entries=32,algorithm_boxes=2,rows=rows,
    unnumbered_main_audit='Required:game/regret semantics,extended domain/indicator/epigraph,four closure bullets,interior optimality,subdifferential domain/interior facts,Lipschitz bounds,actual OSD transfer,fixed regret/units,causal convex-to-linear reduction,step-size minimization. Reconcile existing groups individually; counts stay null until precise reviewed signatures are frozen.',
    current_OGD_accepted_overlay='runs/online-ogd-migration-20261005/source-inventory-acceptance-overlay-v2.json',
    independent_exercises=[dict(source_id='Problem 2.'+str(i),printed_page=23,pdf_page=35,status='optional/planned; not default main-text completion') for i in range(1,6)],
    inverse_sqrt_boundary='Problems2.1/2.2 only:sum1/sqrt(t) and diminishing inverse-sqrt schedule are independent exercises. No formal main-text result is excluded because its proof is an exercise.',
    historical_section='2.4 pedagogical/history commentary, separate from mathematical main text',
    actual_parser_failure='Initial source-heading regex used word boundary and failed on PDF concatenation Remark2.1I; non-digit delimiter repairs heading recognition. Initial assertion was not a source gate.',
    mandatory_total=None,chapter_accepted=False,whole_book_goal='active',main_updated=False,live_updated=False)
with (run/'source-navigation-draft-v1.json').open('w',encoding='utf-8',newline='\n') as f:json.dump(result,f,ensure_ascii=False,indent=2);f.write('\n')
with (run/'00_context.md').open('w',encoding='utf-8',newline='\n') as f:f.write('Read-only completeChapter2 source enumeration draft alongside same-chapter FTL migration. Exactv10/source extract freshly verified.34 unique navigation anchors:32 numbered entries/two algorithm boxes; references are not extra declarations. Unnumbered semantic enumeration/current Lean evidence reconciliation remain required; no precise contract or chapter gate accepted here. No Chapters3-16 proof writing. Whole Goal ACTIVE; main/live unchanged.\n')
print('Fresh Chapter2 navigation draft:',len(rows),'unique anchors; mandatory total remains null, chapter incomplete.')
