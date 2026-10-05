"""Enumerate main-text unnumbered claims without promoting navigation to acceptance."""
from pathlib import Path
import hashlib,json
run=Path(__file__).parent
source=Path('tmp/online-ch2-enumeration-source20-35.txt')
raw=source.read_bytes();text=raw.decode('utf-8')
assert hashlib.sha256(raw).hexdigest()=='adc5b396aa3d32dff754c77dbd05d708e967d4c88eddad78c97cf34e47e9b935'
groups=[
('game-regret',[20,21],'Output a feasible decision before current feedback; comparator regret is the same played-loss sum minus fixed-comparator loss. Sublinear regret implies asymptotic average comparison.',
 ['BanditRLProof/OnlineLearningFoundations.lean','BanditRLProof/OnlineLearningInformation.lean','BanditRLProof/OnlineLearningAsymptotic.lean']),
('extended-domain-indicator',[21,22],'Extended domain is {x:f(x)<+infinity}, allowing minus-infinity values; indicator is zero on V and plus-infinity otherwise; finite indicator-augmented losses enforce feasible actions.',
 ['BanditRLProof/OnlineConvexExtended.lean']),
('epigraph-domain-indicator-closure',[22],'Convex epigraph implies convex effective domain; indicator convex iff V convex; convex no-minus-infinity f plus indicator of convex V is convex.',
 ['BanditRLProof/OnlineConvexExtended.lean']),
('nonnegative-combination',[22,23],'Nonnegative weighted linear combinations preserve convexity. Precise extended-real arithmetic versus finite real-function scope needs explicit reconciliation; proof-as-exercise does not make this optional.',
 ['BanditRLProof/OnlineConvexExamples.lean','BanditRLProof/OnlineConvexClosures.lean']),
('affine-composition',[22,23],'Affine precomposition preserves convexity; exact object/function codomain and assumptions require statement-level audit.',
 ['BanditRLProof/OnlineConvexClosures.lean']),
('monotone-convex-composition',[22,23],'For real-valued convex f and convex nondecreasing g, g composed with f is convex; proof left as exercise remains required.',
 ['BanditRLProof/OnlineConvexClosures.lean']),
('pointwise-supremum',[22,23],'Pointwise supremum of convex functions is convex. Empty/unbounded families and real versus extended-real supremum conventions need exact reconciliation, not silent extra boundedness.',
 ['BanditRLProof/OnlineConvexClosures.lean']),
('interior-first-order-optimality',[23],'Under Theorem2.8 regularity, a feasible interior point minimizes over V iff its ambient gradient is zero.',
 ['BanditRLProof/OnlineConvexOptimality.lean']),
('fixed-unbounded-domain-residual',[26,27],'Constant-step regret requires no finite domain diameter and retains the negative terminal distance. Variable-step proof needs distance control. Later unbounded-domain failure discussion points to Chapter5, without a separate explicit Chapter2 lower-bound statement.',
 ['BanditRLProof/OnlineGradientDescent.lean','BanditRLProof/OnlineGradientDescentSource.lean']),
('step-size-algebraic-minimization',[27],'For fixed positive distance and squared-gradient-energy coefficients, minimize A/(2 eta)+eta B/2 at sqrt(A/B), obtaining sqrt(A B). This is algebraic oracle minimization, not a causal choice of eta using future gradients; degenerate coefficients require boundary records.',
 ['BanditRLProof/OnlineOptimalStep.lean']),
('diameter-gradient-coarse-tuning',[27],'Using diameter D and gradient norm bound L, minimize D^2/(2 eta)+eta L^2 T/2 at D/(L sqrt(T)) and derive D L sqrt(T). Requires positive denominator quantities and T>=1; same real run as Algorithm2.1.',
 ['BanditRLProof/OnlineOptimalStep.lean','BanditRLProof/OnlineGradientDescentSource.lean']),
('closed-iff-lower-semicontinuous',[28],'Every real sublevel closed iff extended-real function is lower semicontinuous in the source Euclidean setting; source also states Hausdorff generalization.',
 ['BanditRLProof/OnlineClosedProper.lean']),
('subdifferential-domain',[29],'For proper convex f, subdifferential outside effective domain is empty and dom(partial f) is contained in dom f. Properness supplies a finite witness excluding impossible +infinity support.',
 ['BanditRLProof/OnlineSubgradientBasic.lean']),
('interior-subgradient-existence',[29],'A proper convex function has a subgradient at every point of the ordinary interior of its effective domain. Footnote stronger relative-interior statement is separately flagged for source-scope review; no automatic coverage claim.',
 ['BanditRLProof/OnlineSubgradientInterior.lean']),
('actual-OSD-performance-transfer',[31,32],'Replace differentiability by subdifferentiability and actual selected gradients by actual legal subgradients in the same projected updates. Inherit sharp fixed and positive nonincreasing variable-step bounds and tuning, retaining terminal terms. A single-step consumer alone is insufficient.',
 ['BanditRLProof/OnlineSubgradientDescent.lean','BanditRLProof/OnlineSubgradientPolicy.lean']),
('unit-exponents',[33],'Gradient units equal loss units divided by decision units; coherent whole-space update implies eta units decision squared divided by loss; both fixed-bound terms have loss units. Algebraic dimension representation must be distinguished from physical quantities.',
 ['BanditRLProof/OnlineUnitScaling.lean']),
('coordinate-rescaling',[33,34],'With x prime=x/1000 and unchanged loss-value units, gradient prime=1000 gradient. Uncompensated eta produces factor1000000 physical effective step; correct eta scales by1/1000000. Preserve actual policy transport and path, not universal worse-regret claims.',
 ['BanditRLProof/OnlineUnitScaling.lean']),
('convex-to-linear-causal-reduction',[34],'Summed convex regret is bounded by summed inner products and comparator regret of losses <g_t,x>. An online learner for arbitrary linear vectors can be applied using the actual legal subgradient feedback after each current played decision. Keep same trajectory and strict-prefix information; no universal optimality claim.',
 ['BanditRLProof/OnlineLinearization.lean'])]
rows=[]
for key,pages,signature,files in groups:
    for file in files:assert Path(file).is_file(),file
    fragments=[]
    for page in pages:
        start=text.index('PHYSICAL PAGE '+str(page)+'\n')
        nextmark=text.find('PHYSICAL PAGE ',start+1)
        fragment=text[start:nextmark if nextmark>=0 else len(text)]
        fragments.append(dict(pdf_page=page,printed_page=page-12,source_context_sha256=hashlib.sha256(fragment.encode()).hexdigest()))
    rows.append(dict(source_group=key,pages=fragments,proposed_source_signature=signature,
        retrieved_existing_files=files,required_audit=True,proof_left_as_exercise_is_excluded=False,
        target_contract='not yet stabilized: retrieve exact native declarations and independently reconcile semantics',
        accepted=False))
result=dict(stage='unnumbered-source-audit-draft',chapter=2,source_sha256='cef4edfa97a6e063e53e9c532717c50aa156e5bc782ea49f969b3385011a1b17',
    source_extract_path=source.as_posix(),source_extract_sha256=hashlib.sha256(raw).hexdigest(),
    source_groups=rows,group_count_is_not_theorem_or_obligation_count=True,mandatory_total=None,
    additional_review_questions=['Determine whether Chapter2 explanatory lookahead/nonpositive-energy sentence is a separate mathematical obligation or Chapter15 pointer; do not silently omit.',
        'Relative-interior footnote is a stronger formal existence claim: review its main-text versus necessary-dependency scope explicitly.',
        'Main numbered examples include performance claims; inclusive navigation fragments must be split into exact source contracts, not counted as closed by theorem number alone.'],
    independent_problems_2_1_to_2_5='optional/planned; formal main-text results whose proofs are exercises remain required',
    exact_lean_signatures_frozen=False,chapter_accepted=False,whole_goal='active')
with (run/'unnumbered-source-audit-draft-v1.json').open('w',encoding='utf-8',newline='\n') as f:json.dump(result,f,ensure_ascii=False,indent=2);f.write('\n')
print('18 unnumbered source groups identified for exact contract reconciliation; mandatory total remains null, no chapter acceptance.')
