"""Freeze source intention, exact retained statements, definition and canary terminals."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from tools.abrl_lifecycle import lean_declaration_header
run=Path(__file__).parent;task='ONLINE-SUBGRADIENT-DIFFERENTIABILITY-MIGRATION-20261007'
contract=Path('docs/contracts/online-subgradient-differentiability-migration-v1')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
load=lambda p:json.loads(Path(p).read_text(encoding='utf-8'))
def write(p,x):
 p=Path(p);assert not p.exists(),p;p.parent.mkdir(parents=True,exist_ok=True)
 p.write_bytes((x.rstrip('\n')+'\n' if isinstance(x,str) else json.dumps(x,ensure_ascii=False,indent=2)+'\n').encode('utf-8'))
def gate(label,*args):subprocess.run([sys.executable,'-X','utf8',str(run/'run-command.py'),label,*args],check=True)
for label in ['retained-module-v1-01','actual-types-v1-01','local-declarations-v1-01','local-memory-v1-01','source-render-v2-01']:
 assert load(run/(label+'-exit.json'))['exit_code']==0,label
assert 'Build completed successfully (3315 jobs)' in (run/'retained-module-v1-01.log').read_text(encoding='utf-8')
public=Path('BanditRLProof/OnlineSubgradientDifferentiability.lean');canary=Path('Tests/OnlineSubgradientDifferentiabilityCanary.lean')
assert public.read_bytes()==(run/'original-OnlineSubgradientDifferentiability.lean.txt').read_bytes()
assert canary.read_bytes()==(run/'original-OnlineSubgradientDifferentiabilityCanary.lean.txt').read_bytes()
text=public.read_text(encoding='utf-8');named=load(run/'public-named-declarations-v1.json')
names=[n.rsplit('.',1)[1] for n in named['public_proofs']]
intent='''Orabona arXiv:1912.13213v10 (21June2026), printed17/PDF29 Theorem2.22 (Rockafellar25.1): f:R^d→[-infinity,+infinity] convex and FINITE AT x; f differentiable at x IFF global subdifferential is singleton, whose element is the gradient. Complete two-direction terminal and explicit derivative identity, not just uniqueness conditional on an already supplied derivative. One numbered anchor; adjacent introductory sentence about a unique differentiable-function subgradient is read in the following convex theorem's scope: differentiable arbitrary nonconvex functions need not have global supports. No separately invented performance bound. The adjacent T2.21/interior/relativefootnote were accepted in previous packages; T2.23 remains REQUIRED and is not included.

The existing complete SourceDifferentiableAt definition is ∃h:E→REAL, (coe∘h)=f EVENTUALLY at the ambient nhds x AND DifferentiableAt REAL h x. This expresses a genuinely real-valued differentiable local germ of the extended-real function, with values finite throughout some ambient neighborhood. It does not mean merely DifferentiableAt(f.toReal), differentiability within the effective domain or within its affine span, nor demand a globally finite f. A singleton indicator on REAL{1} is proper/convex/finiteat1 and has toReal identicallyzero, yet has every global support and is NOT genuinely locally real differentiable. Planned new3proof canary freezes exactly that diagnostic. Actual complete definition @type has real inner-product classes but NOT FiniteDimensional (unused binder omitted). Main11proofs all actually finite-dimensional real inner-product spaces. Derived proper/complete instances do not add a mainterminal binder. Ambient haszero/nonempty; dimension0 allowed, no positive dimension/unique support premise for forward, nonzero gradient required nowhere.

Full theorem_2_22 takes ONLY IsConvexExtended f and actual finite value witness at x, then equivalence to ∃g, SourceSubdifferential f x={g}. It does NOT assume SourceProper f, interior domain, closedness, lower semicontinuity, boundedness, Lipschitzness or differentiability of toReal. Source EReal contains both infinities. SourceSubdifferential is the shared generic global support ∀ambienty, fx+<g,y-x>≤fy; it is broader than source proper specialization, but the hypotheses of each direction here DERIVE nowherebottom/properness. Global support at finite x rules out any bottom value; finite local germ plus convexity produces affine support and therefore rules out bottom globally. Outside-neighborhood top values are permitted; no sidecondition fgloballyreal added. EffectiveDomain=fx<top includesbottom generically; all domain/interior uses here take derived noBottom. IsConvexExtended means convex REAL-HEIGHT epigraph (not blindly casting infinities to zero).

theorem_2_22_gradient separately quantifies EVERY differentiable real representative h agreeing with f nearx and states S(f,x)={gradient h x}, ensuring actual identity and independence of representative. Source hxfinite retained even when agreement already implies it. theorem_2_22_forward is an intermediate existence/singleton half, not another source theorem. No domain-restricted gradient substitution or gradientoracle is accepted as the full result.

Actual reverse DAG: singleton support at finite x→derive noBottom; supporting_functional_at_closure ORIGINAL convexdomain atx if not interior yields NONZERO normal a, Rieszd, then g+d also global support, contradict singleton→interior; properconvex localLipschitz→localbound on ALL nearby supports; continuity+closed global inequalities on a nontrivial filter→support limits; compact closedball and unique clusterpoints→every actual nearby selected support gs convergesg. Choose supports near interior using accepted ambient existence; their difference norm tendszero. Two ACTUAL global inequalities at x,y bound remainder between0 and <G(y)-g,y-x>≤‖G(y)-g‖‖y-x‖, giving Frechet littleO and HasGradientAt(toReal)g; recover actual real germ with local finite conversion. Support-selection is proof-internal/nonmeasurable, not causal algorithm or algorithm-existence claim. NeBot essential for filterlimit/cluster helper; no false empty-filter implication.

Actual forward DAG: real representative/local finiteness→accepted affine_support_of_finite_neighborhood (specified contact preserved)→derive noBottom; regularity gives interior+real differentiability. Accepted theorem_2_7 derives actual global convex first-order inequality (topqueries allowed). Actual local minimum of f.toReal-innerg and derivativezero yields every global support equals gradient via Riesz injectivity. Actual eventual representative equality gives equal gradients, then complete set extensionality; forward wraps explicitgradient; full equivalence joins reverse. Helpers with hbot/hxinterior/Lipschitz/continuous/singleton hypotheses are INTERMEDIATE interfaces, not extra source terminal assumptions. Source finiteEuclidean exact represented finiteDrealinner; no toolchain/dependency upgrade/Optlib claims.

Retain eleven actual public proofs and one complete definition, six whole existing canary proofs. Three NEW TEST-ONLY diagnostic proofs planned, zero new production mathematical proofs/definitions or canonical registry nodes. Existing canaries already instantiate actual gradient endpoint on constrained indicator at1 and nonzero quadratic slope2 at1; reversefull equivalence/HasGradient endpoint; boundary0 supports0and-1 and fullforward contradiction excludes genuine differentiability. Fresh selected compiled graph will include full definition/actual proofs and direct references; do not count allcanary nodes unless exported. New diagnostics are not extra source anchors/proofgain.

Allowed production edit after distinct CONTRACT/BODY only an ordinary leading source/scope comment (all original bytes contiguous), selected online-subgradient-differentiability subtree in three JSON readers, new meaningful diagnostic canary/Tests import, manifest. No changes to frozen proof bodies/headers/definitiontokens/shared public dependencies/oldcanary/rootBandit/pins, no duplicate wrappers. Original old20261003contracts/failed attempts/verdicts immutable and historical, no inherited fresh acceptance. Single lower route. Native runtime gates vs prompt/file conventions remain distinct; semantic-roundtrip three distinct automatedactors requestedAstra/medium with honest restricted current packets/history, no independent human/external/runtime attestation.

Exact OPENdraftPR1684cf116c2ee42caa37e5a956ebbbfddfb0bc046f2 base, main6847...unchanged. Legacy7->6 ONLYOnlineSubgradientDifferentiability AFTERgates/PR. Chapter1migration and nine OTHER main-relative legacy contracts required; Chapter2mandatorytotalnull/incomplete; Chapters3-16unenumerated; wholeGoalACTIVEunbudgeted. NoChapter3competitiveproofwriting/merge/deployment/retirement/global SGB overwrite.
'''
write(contract/'source-intent.md',intent)
defstart=text.index('def SourceDifferentiableAt');defend=text.index('\ntheorem ',defstart)
full_def=text[defstart:defend].strip()
context=dict(imports=text[:text.index('noncomputable section')],actual_prefix=text[:text.index('theorem subgradient_norm_le_lipschitz_ball')],full_definition=full_def,full_definition_tokens=re.findall(r'\S+',full_def),definition_actual_finiteDimensional_binder=False,actual_types='actual-types-v1-01.log',main_proof_classes=['NormedAddCommGroup E','InnerProductSpace REAL E','FiniteDimensional REAL E'],shared_S='∀y in entire ambient space, fx+coe(inner g(y-x))≤fy',shared_D='fx<top; includesbottom generically; uses here derive noBottom',shared_convex='convex real-height epigraph',zero_dimension_allowed=True,CompleteSpace_binder=False)
write(contract/'scoped-contexts.json',context)
headers={}
for n in names:
 h=lean_declaration_header(public,n);digest=hashlib.sha256(h.encode()).hexdigest()
 headers[n]=dict(file=public.as_posix(),statement=h,statement_hash=digest,context_hash=sha(contract/'scoped-contexts.json'))
 gate('draft-fence-'+n+'-v1',sys.executable,'-X','utf8','tools/bandit.py','statement-fence','--declaration','BanditRL.OnlineConvex.'+n,'--file',public.as_posix(),'--output',(run/('native-draft-fences/'+n+'.json')).as_posix())
 assert load(run/('native-draft-fences/'+n+'.json'))['statement_hash']==digest
write(contract/'headers.json',headers)
write(contract/'source-card.json',dict(source='https://arxiv.org/pdf/1912.13213v10',version_date='2026-06-21',PDF_SHA256='cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17',printed_pages=[17],pdf_pages=[29],numbered_anchors=['Theorem2.22'],source_unnumbered_independent_results=0,source_statement_fingerprint=sha(contract/'source-intent.md'),extraction_sha256=sha(run/'source-printed17-pdf29.txt'),boundary='Full equivalence AND exact gradient identity; helpers not separate source numbered results; T2.23 remains mandatory.'))
dag=[['singleton_subdifferential_interior','supporting_functional_at_closure/convex domain/Riesz/nonzero normal'],['subgradients_locally_bounded','local convex Lipschitz/subgradient_norm_le_lipschitz_ball'],['subgradient_limit_of_continuousAt','finite-part neighborhood/continuousAt/global inequality limits/NeBot'],['singleton_subgradient_tendsto','local bound/compactball/unique clusterpoints/limit helper'],['singleton_subdifferential_hasGradientAt','interior/noBottom/ambient existence/select G/tendsto/littleO'],['theorem_2_22_gradient','real neighborhood/affine contact/noBottom/regularity/theorem2.7/localmin uniqueness/gradient equality'],['theorem_2_22_forward','explicit gradient singleton'],['theorem_2_22','forward+singleton interior+actual HasGradient reverse+real germ']]
write(contract/'dependency-DAG-v1.json',dict(initial_dependency_frontier='11retainedproofs/freshfocus/types/localretrieval; sourcecontract/actualDAG/currentgates still pending',terminal=['theorem_2_22','theorem_2_22_gradient'],DAG=dag,single_lower_route=True,old_unpublished_singleton_continuousAt_contract='Historical scratch-only descriptor, not an actual current public declaration or additional numbered source result. Actual generic-filter tendsto helper supplies this proof dependency.'))
newcanary='''import BanditRLProof
namespace Tests.OnlineDifferentiabilityBoundary
open BanditRL.OnlineConvex Set Filter
open scoped Topology

theorem singleton_toReal_differentiable :
    DifferentiableAt ℝ (fun y : ℝ => (extendedIndicator ({1} : Set ℝ) y).toReal) 1 := by

theorem singleton_not_sourceDifferentiable :
    ¬ SourceDifferentiableAt (extendedIndicator ({1} : Set ℝ)) 1 := by

theorem singleton_global_supports (g : ℝ) :
    g ∈ SourceSubdifferential (extendedIndicator ({1} : Set ℝ)) 1 := by

end Tests.OnlineDifferentiabilityBoundary
'''
preview=run/'leaves/new-boundary-canary-headers-v1.lean.txt';write(preview,newcanary)
newheaders={}
for n in ['singleton_toReal_differentiable','singleton_not_sourceDifferentiable','singleton_global_supports']:
 h=lean_declaration_header(preview,n);newheaders[n]=dict(statement=h,statement_hash=hashlib.sha256(h.encode()).hexdigest())
write(contract/'new-canary-terminals-v1.json',dict(headers=newheaders,preview=preview.as_posix(),preview_compiled=False,fence_only_empty_body_markers=True,new_test_proofs=3,new_production_proofs=0))
write(run/'draft-freeze-v1.json',dict(stage='draft',headers={n:r['statement_hash'] for n,r in headers.items()},module={public.as_posix():sha(public)},whole_old_canary={canary.as_posix():sha(canary)},fixed_shared_files={p:sha(p) for p in ['BanditRLProof/OnlineSubgradientInterior.lean','BanditRLProof/OnlineConvexFirstOrder.lean','BanditRLProof/OnlineSubgradientBasic.lean','BanditRLProof.lean','lean-toolchain','lakefile.lean','lake-manifest.json']},Tests_root_raw_prefix=sha('Tests.lean'),complete_definition_sha256=hashlib.sha256(full_def.encode()).hexdigest(),newcanary_headers={n:r['statement_hash'] for n,r in newheaders.items()},source_package_accepted=False,chapter_complete=False,goal_complete=False))
mapping={n:'N'+str(i+1).zfill(2) for i,n in enumerate(names)}
mapping.update(SourceDifferentiableAt='R',SourceSubdifferential='S',IsConvexExtended='C',effectiveDomain='D',SourceProper='P',extendedIndicator='I')
def neutral(s):
 for old in sorted(mapping,key=len,reverse=True):
  s=re.sub(r'\b'+re.escape('BanditRL.OnlineConvex.'+old)+r'\b',mapping[old],s)
  s=re.sub(r'\b'+re.escape(old)+r'\b',mapping[old],s)
 return s
typed=(run/'actual-types-v1-01.log').read_text(encoding='utf-8');typed=typed[:typed.index('ForwardSubgradientProbe.')]
packet='''Requested distinct restricted decoder GPT-6 Astra/medium. Read ONLY this file; no filesystem search/source identity/proof bodies/verdicts/compilation. Write ONLY blind-reconstruction-v1.md and blind-receipt-v1.json in this run. Seven semantic slots for all eleven N01-N11 and complete R, emphasizing N09/N10/N11. State every hidden or derived regularity versus supplied premise; diagnose bare toReal versus genuine local real germ, ambient/domain-restricted derivative and every representative gradient. Honest prior-history limits; no human/external/runtime-model or source/Goal certification.

Supplied notation context: REAL field; EReal both infinities and real embedding; C(f) means convex REAL-height epigraph {(x,t):E×REAL |fx≤coet}; D(f)={x|fx<top}, bottom included generically. P(f) means nowherebottom plus exists a finite real value. S(f,x)={g |∀y in entire ambientE,fx+coe(innerREALg(y-x))≤fy}. I(A)(x)=0 ifx∈A/topotherwise. DifferentiableAt means ambient Frechet real differentiability. HasGradientAt is inner-product/Riesz derivative identity. All main N statements finite-dimensional real inner-product; actual R definition omits unused finiteD binder. Classes contain zero, ambient nonempty, dimensionzero possible. No probability/algorithm supplied.

Complete neutral definition, not short header only:
```lean
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
'''+neutral(full_def)+'\n```\n\nNeutral actual headers without proof bodies:\n```lean\n'+'\n\n'.join(neutral(headers[n]['statement']) for n in names)+'\n```\n\nNeutral actual @types:\n```text\n'+neutral(typed)+'\n```\n\nReconstruct logical terminal iff in N11 and singleton identity in N09. Does N11 assume globallyproper/interior/closed or only pointfinite? N04 filter is NeBot. Is R only differentiability of toReal or includes actual finite neighborhood? Could singleton indicator have smooth toReal and nevertheless fail R? Boundary and every-query support semantics explicit. Do not identify source.'
write(run/'blind-packet-v1.md',packet)
for folder in ['tasks','conversion-windows','proof-obligations']:
 write(Path(folder)/(task+'.md'),'# '+task+'\n\n'+intent+'\n\nInitial DAG: '+json.dumps(dag,ensure_ascii=False))
write(run/'10_upper_director-v1.md','Close exactly T2.22 equivalence plus explicit gradient identity via existing full producer chain, preserving all source terminal assumptions. Retained11proof1definition, no new production mathgain. Current contract and source acceptance pending; T2.23/laterChapter2/Chapter1/wholeGoal mandatory.')
write(run/'20_architect-v1.md',intent+'\n\nFinite-dimensional compactness/Riesz/filterNeBot and localfinite-germ are explicit semantic interfaces; do not add them as mainterminal hypotheses.')
write(run/'proof-obligations-v1.json',dict(stage='draft',required=[dict(name=n,statement_hash=r['statement_hash'],state='distinct-source-contract-review-pending') for n,r in headers.items()],required_full_definitions=['SourceDifferentiableAt'],numbered_anchors=1,unnumbered_independent_results=0,retained_proofs=11,new_production_proofs=0,new_canary_proofs=3,DAG=dag,chapter_total=None,source_package_accepted=False,chapter_complete=False,goal_complete=False))
image=Path('tmp/online-subgradient-differentiability-source-pdf29-v2.png')
write(run/'source-render-binding-v2.json',dict(source_pdf_sha256='cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17',pdf_page=29,printed_page=17,image=image.as_posix(),image_sha256=sha(image),actual_view_image=True,visual='Actual page29 viewed: T2.22 finiteatx/iff/singleelement/gradient, both-infinityrange. Adjacent numbered2.21/2.23 and footnote belong to their distinct scopes.',first_failure='Readonly attempted pypdfium2 under defaultPython38 raised ModuleNotFoundError; image unavailable, view_image failed. No rendering occurred. Actual Poppler pdftoppm v2 succeeded and view_image actually inspected it. No library installation/source edit; original tool transcript retains failures.'))
write(run/'draft-generated-before-use-v1.json',dict(rows=[dict(path=p.as_posix(),sha256=sha(p)) for p in [run/'blind-packet-v1.md',preview]],before_first_use=True))
gate('draft-lifecycle-v1',sys.executable,'-X','utf8','tools/bandit.py','lifecycle-event','--session',task,'--event','draft','--payload-json',json.dumps(dict(run_id=run.name,frozen_headers={n:r['statement_hash'] for n,r in headers.items()},retained_proofs=11,retained_definitions=1,new_production_proofs=0,source_package_accepted=False,chapter_complete=False,goal_complete=False)))
print('Draft frozen:11exactheaders/complete local-real definition/T2.22 equivalence+gradient/3diagnostic testterminals; distinct contract review pending.')
