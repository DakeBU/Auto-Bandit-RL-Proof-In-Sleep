"""Port three closed frozen comparison bodies into the existing shared library."""
from pathlib import Path
import hashlib,json,re,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header,_strip_lean_comments
run=Path(__file__).parent
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
freeze=load(run/'draft-freeze-v2.json')
assert load(run/'contract-binding-audit-v1.json')['status']=='passed'
for n in ['mean-zero','gap-lower','gap-unbounded']:assert load(run/(n+'-v1-01-exit.json'))['exit_code']==0
headers=load('docs/contracts/online-guessing-migration-v1/headers-native-v2.json')
scratch=run/'leaves/gap-unbounded-v1.lean'
for n,h in freeze['planned_new_headers'].items():assert hashlib.sha256(lean_declaration_header(scratch,n).encode()).hexdigest()==h
public=Path('BanditRLProof/OnlineGuessingComparison.lean');assert not public.exists()
body=re.sub(r'(?m)^#(?:check|print)\b[^\n]*\n','',scratch.read_text(encoding='utf-8'))
comment='''/-!
Derived support for Orabona v10 Example 2.14 (printed p15/PDF27), using the
actual Chapter 1 strict-prefix mean predictor (printed p4/PDF16).
On the same all-zero real labels, the mean predictor starts at 1/2 and has
cumulative square loss 1/4. The actual horizon-tuned projected OGD starts at 1
and has loss at least n/4 at T=(2*n)^2, so their gap is at least n/4-1/4 and
exceeds every real threshold at some n above every natural cutoff.
These are derived comparison refinements, not numerical results printed in the
book, an equal-initialization comparison, an every-stream/every-initialization
claim, or a minimax/Chapter 4 theorem. The horizon is known for each separate
tuned run; this is not a single horizon-independent algorithm or future-label
optimization. Zero comparator loss is optimal on this fixed stream. At n=1 the
displayed lower gap is zero. Existing source contracts and library are reused;
this module alone does not accept Chapter 1, Chapter 2 or the whole book.
-/

'''
public.write_text(comment+body,encoding='utf-8')
for p,explain in [('BanditRLProof/OnlineGuessingOGD.lean','''Orabona v10 Example 2.14, printed p15/PDF27: real labels/predictions in [0,1].
Actual projection, ambient square gradient and global square regularity are
produced. The same strict-prefix OGD recurrence with known-horizon positive
step 1/(2*sqrt T), T>0, yields derived constant 2 in the printed O(sqrt T) rate
for every feasible initial point/comparator. Unrestricted-real helper identities
do not supply an arbitrary-step regret guarantee. Existing stronger RegularLoss
is discharged on all real space, not imposed as an extra source premise.
OnlineGuessingLower and OnlineGuessingComparison give separate derived lower
and same-zero-stream comparison results; no Chapter 4 or full-chapter claim.'''),
 ('BanditRLProof/OnlineGuessingLower.lean','''Derived support for Orabona v10 Example 2.14's comparison, printed p15/PDF27.
Same actual interval square-loss OGD, initial 1, all labels 0, comparator 0;
positive n and known square horizon T=(2*n)^2, source step 1/(2*sqrt T)=1/(4*n).
Actual geometric trajectory yields regret at least n/4=sqrt T/8. The numerical
lower witness is not printed in the book, not every initialization/algorithm,
and not a Chapter 4 minimax claim. The eta identity alone also permits n=0
under total real division; no legal tuned zero-horizon guarantee follows.
OnlineGuessingComparison directly compares the source mean predictor (initial
1/2) on the same zero stream, with all initialization/horizon boundaries visible.''')]:
 old=(run/('original-'+Path(p).name+'.txt')).read_bytes();assert Path(p).read_bytes()==old
 Path(p).write_bytes(('/-!\n'+explain+'\n-/\n\n').encode()+old)
canary=Path('Tests/OnlineGuessingComparisonCanary.lean');assert not canary.exists()
canary.write_text('''import BanditRLProof

namespace Tests.OnlineGuessingComparison
open BanditRL.OnlineGradientDescent Finset

lemma actual_zero_stream_gap :
    (3/4 : ℝ) ≤
      regret unitInterval (1/16) (fun _ x => (x-0)^2) 1 0 64 -
      (∑ t ∈ range 64,
        (BanditRL.OnlineLearning.meanPredict (fun _ : ℕ => (0 : ℝ)) t)^2) := by
  have h := guessing_vs_mean_lower 4 (by omega)
  norm_num at h ⊢
  exact h

#print axioms actual_zero_stream_gap
end Tests.OnlineGuessingComparison
''',encoding='utf-8')
for p,old,new in [('BanditRLProof.lean',b'import BanditRLProof.OnlineGuessingLower',b'import BanditRLProof.OnlineGuessingComparison'),('Tests.lean',b'import Tests.OnlineGuessingLowerCanary',b'import Tests.OnlineGuessingComparisonCanary')]:
 path=Path(p);raw=path.read_bytes();assert raw.count(old)==1 and new not in raw
 newline=b'\r\n' if b'\r\n' in raw else b'\n';path.write_bytes(raw.replace(old+newline,old+newline+new+newline,1))
tokens=lambda s:re.sub(r'\s+',' ',_strip_lean_comments(s)).strip()
for p in freeze['module']:
 assert Path(p).read_bytes().endswith((run/('original-'+Path(p).name+'.txt')).read_bytes())
 assert tokens(Path(p).read_text(encoding='utf-8'))==tokens((run/('original-'+Path(p).name+'.txt')).read_text(encoding='utf-8'))
for n,row in headers.items():assert hashlib.sha256(lean_declaration_header(Path(row['file']),n).encode()).hexdigest()==row['statement_hash']
for p,h in freeze['canary'].items():assert sha(p)==h
names=['BanditRL.OnlineGradientDescent.'+n for n in headers]+['BanditRL.OnlineGradientDescent.unitInterval']
names+=['Tests.OnlineGuessingOGD.'+n for n in ['labels','losses','first_projected','second_projected','source_four_rounds']]
names+=['Tests.OnlineGuessingLower.'+n for n in ['first_state','source_lower']]+['Tests.OnlineGuessingComparison.actual_zero_stream_gap']
assert len(names)==len(set(names))==21
probe=run/'leaves/public-axioms-v1.lean';assert not probe.exists()
probe.write_text('import BanditRLProof\nimport Tests.OnlineGuessingOGDCanary\nimport Tests.OnlineGuessingLowerCanary\nimport Tests.OnlineGuessingComparisonCanary\n\n'+''.join('#check @'+n+'\n#print axioms '+n+'\n' for n in names),encoding='utf-8')
(run/'public-named-declarations-v1.json').write_text(json.dumps(dict(axiom_probe=names,public_proofs=12,public_definitions=1,canary_proofs=6,canary_definitions=2,retained_proofs=9,new_proofs=3,new_definitions=0),indent=2)+'\n',encoding='utf-8')
export=(run/'leaves/export-retained-dependencies-v1.lean').read_text(encoding='utf-8');start=export.index('def targets');end=export.index('\ndef moduleName')
targets=['BanditRL.OnlineGradientDescent.'+n for n in headers]+['BanditRL.OnlineGradientDescent.unitInterval']
export=export[:start]+'def targets : Array Name := #[\n  '+',\n  '.join('`'+n for n in targets)+']\n'+export[end:]
export=export.replace('nine retained interval square-loss/bound/comparison-substrate proofs and one domain definition','twelve interval square-loss/source comparison proofs and one domain definition')
out=run/'leaves/export-public-dependencies-v1.lean';assert not out.exists();out.write_text(export,encoding='utf-8')
binding=run/'public-port-before-gates-v1.json';assert not binding.exists()
paths=[public,canary,probe,out,Path('BanditRLProof.lean'),Path('Tests.lean')]+[Path(p) for p in freeze['module']]
binding.write_text(json.dumps(dict(stage='ported-actual-closed-scratch-bodies-public-gates-pending',rows=[dict(path=p.as_posix(),sha256=sha(p)) for p in paths],all12frozen_headers_unchanged=True,old9proof_tokens_unitInterval_unchanged=True,old2canaries_bytefixed=True,new_proofs=3,new_definitions=0,source_package_accepted=False,chapter_complete=False,goal_complete=False),indent=2)+'\n',encoding='utf-8')
print('Three closed exact bodies ported/shared root/canary;12headers retained, new public gates pending.')
