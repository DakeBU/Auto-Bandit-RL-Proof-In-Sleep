from common import *
fixed()
import re
text=(CONTRACT/'targets-draft-v1.txt').read_text(encoding='utf8')
targets=[]
for part in text.split('-- TARGET ')[1:]:
    name,header=part.split('\n',1)
    header=header.strip()
    targets.append(dict(name=name,declaration='BanditRL.OnlinePrescientBregman.'+name,exact_header=header,statement_sha256=hashlib.sha256(header.encode('utf8')).hexdigest(),file=PUBLIC.relative_to(ROOT).as_posix()))
context='''import BanditRLProof.OnlinePrescientBregman
import BanditRLProof.OnlineGradientDescentVariable

noncomputable section
open Set Finset
namespace BanditRL.OnlinePrescientBregman
open BanditRL.OnlineBregman
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
'''
write(CONTRACT/'scoped-context-v1.txt',context)
write(CONTRACT/'targets-draft-v1.json',dict(stage='draft',targets=targets,context=context,source_card_sha256=sha(CONTRACT/'source-card-v1.json'),whole_Goal_status='ACTIVE',source_container_closed=False,chapter_complete=False,chapter_proof_total=None))
neutral=dict(instruction='Reconstruct mathematical meaning and ALL assumptions from actual Lean headers/context only. No source identity or claimed verdict. Prior related task history exists; report this limitation, do not claim absolute source blindness. Do not look at source/contracts/evidence/proofs outside this neutral packet and canonical referenced API declarations.',context=context,targets=targets,canonical_supporting_definitions=(ROOT/'BanditRLProof/OnlinePrescientBregman.lean').read_text(encoding='utf8'),loss_support_definitions={p:(ROOT/p).read_text(encoding='utf8') for p in ['BanditRLProof/OnlineClosedProper.lean','BanditRLProof/OnlineSubgradientBasic.lean'] if (ROOT/p).exists()},requested_model='GPT-6 Astra',requested_effort='medium',runtime_model_attestation=False)
write(RUN/'neutral-statement-packet-v1.json',neutral)
probe=context+'\n'
for t in targets:
    h=t['exact_header'].replace('theorem '+t['name'],'#check fun',1)
    left,sep,right=h.rpartition(' :\n')
    assert sep
    probe+=left+' =>\n'+right+'\n\n'
probe+='end BanditRL.OnlinePrescientBregman\n'
write(ROOT/'tmp/online-ch2-prescient-cumulative-types-v1.lean',probe)
capture('exact-draft-type-probe-v1','lake','env','lean','tmp/online-ch2-prescient-cumulative-types-v1.lean')
queries=[('local-cumulative-search-v1',['rg','-n','prescient|divergence_sum|weighted_potential_sum|sum_range_sub', 'BanditRLProof/OnlinePrescientBregman.lean','BanditRLProof/OnlineBregmanExtended.lean','BanditRLProof/OnlineGradientDescentVariable.lean']),('mathlib-cumulative-search-v1',['rg','-n','theorem sum_range_sub\x27|theorem le_sup\x27|theorem nonempty_range_iff|theorem DifferentiableOn.differentiableAt','.lake/packages/mathlib/Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean','.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean','.lake/packages/mathlib/Mathlib/Data/Finset/Range.lean','.lake/packages/mathlib/Mathlib/Data/Finset/Lattice/Fold.lean'])]
for label,args in queries: capture(label,*args,required=False)
write(RUN/'00_context.md','''# Bounded same-run prescient cumulative package

Whole Chapters1-16 Goal ACTIVE; Chapter2 partial, all8 forward containers REQUIRED/OPEN, Ch3-16 unenumerated/null. No progress inferred from proof counts. Current branch stacks on PR211 exact head24de0231aa067f141251aac5c20deb58e448ea66, OPEN draft/unmerged; origin/main remains separately audited.

Source SHA and extracts are pinned in source-card-v1. SourceAlgorithm15.8 reads current loss before choosing its paid prediction. Same existing Option recursion is used without modification. Five exact proposed public targets, no new definitions: shared actual per-round sum interface (two real consumers), sharp fixed/variable bounds with both negative residuals, and printed fixed/finite-max corollaries. Actual output witnesses are posthoc certificates of this particular recursion; they do not supply arbitrary desired one-step or future-aware algorithm existence.

Director/formalizer/architect/worker: root in separated phases. Required distinct automated semantic actors reuse existing osd_blind and source_reviewer; no new math workers/parallel routes. Requested Astra/medium, no runtime attestation/human/external/absolute-blindness claim. Default one lower route. Draft cannot be promoted without exact-context neutral reconstruction and anti-anchored source review. Proof search may edit only selected frozen bodies in new module and OWN records; old production/Test/pins/readers/registries/globalSGB immutable until separately reviewed integration.

Success: theorem-edge same actual Option run -> signed cumulative performance. Full source hypothesis transport/closed generator representation and Chapter2 containers remain required. No merge/deployment authorized or executed here. Sourcefixed proof-left-as-exercise is mandatory and included.
''')
write(RUN/'director-architect-draft-v1.md','''# Draft roles, obligations, conversion window

Route: online-learning Chapter2 forward dependency on Algorithm15.8/Theorem15.30, not early Chapter15 acceptance. Source card, exact headers/scoped context and real type probe are separate artifacts. Reuse canonical iterate_one_step and weighted_potential_sum; sum_range_sub\x27 handles fixed telescope. No duplicate algorithm/divergence/Abel library. Inspiration-only weapons do not certify dependencies.

DAG: iterate_one_step + actual-success/interior witnesses + DifferentiableOn.differentiableAt -> iterate_divergence_sum; this common interface -> iterate_fixed_sharp via sum_range_sub\x27 and actualinitialstate identity; same common interface -> iterate_variable_sharp via a=2B,C=2M in canonical weighted_potential_sum. Each sharp -> corresponding printed corollary via divergence_nonneg, strictconvex.convexOn and positive final denominator. Nonempty finite range uses nonempty_range_iff, max bound uses le_sup\x27. First ready lower leaf after contractreview: iterate_divergence_sum only.

Semantic signature: complete real inner-product E (generalization from finite-dimensional source); deterministic all fixed comparators u in V, actualsuccessstates0..T, sourceinteriorstates all including terminal/initial, wholecurrentlosses, EReal proper/global source supports at V, positive steps. Constanteta allows T0. VariableT>=1 and monotonicity only used pairs inside horizon; maximum ranges PREVIOUSstates0..T-1. No unnecessary bounded domain. No assumed regret/stability bound. Negative terminal retained in sharps; printedcorollaries drop it only with certified nonnegativity. Initialcenterx0 recovered from recursion at0; no requirement x0 in V/lossdomain.

Source-vs-Lean deltas for explicit review: sourcepsi:X->R represented by ambientpsi plus interior differentiability; existing locality theorem licenses divergence independence only targetinX/baseinteriorX. Generic sharp interfaces do not need convex/closedpsi or VsubsetX because ordered divergence algebra needs only actual derivatives; printedcorollaries require strictconvexonX and VsubsetX. Closedness of V/psi omitted as unused conditional theorem assumptions, NOT asserted to imply attainment/interiorpreservation. Source nonemptyV and Vsubsetfinite-domain/no-bottom imply SourceProper: this exact source-facing transport remains open; current APIs state it plus global supports explicitly. hseq encodes well-defined selected actualrun; no generalexistence from closed/strict. Stronger conditional math is reusable, not automatic full source closure. Lossdifferences are finite toReal comparisons whose finiteness is supplied by proper/support premises, never infinity subtraction. Full unconditional choiceability, sourceclosedness packaging, all chapter containers remain required/open.

Publication plan after proof gates: exactsourceattribution/formulaproof/assumptiondelta/foldedLean/dependencies/redboundary adjacent; extend shared declaration registry/source-qualified Book map, preserve old links and per-book library. LeanGraph newnodes/actual compilerVALUEparents, Overview updated affectedforward boundaryonly/Chapter2 stillpartial, Functor none-found-with-reason (this is conditional same-setting telescope, no new certified transport). results/frontier/otherBooks no-change-with-reason where unrelated. New contributionmanifest will cover affectedfiles after exact review. Do not alter old data in draft.

Independent obligations: five frozen proof terminals; nondegenerate fixed and decreasing-step canaries with realcurrentlosses/actualminima/interiority/nonzeroordereddivergences/exactprevious-statefiniteMAX and numericVALUEdependencies; declaration probes/statementfences/axiomaudit/focusedbuild/combinedrootTests/fullharness/shadow/contributor/sitebrowser; distinct semantic BODY/FINALreview. Counts are package obligations only; chapter denominator remains null.
''')
write(RUN/'draft-inputs-v1.json',dict(rows=rows([CONTRACT/'source-card-v1.json',CONTRACT/'targets-draft-v1.txt',CONTRACT/'targets-draft-v1.json',CONTRACT/'scoped-context-v1.txt',RUN/'00_context.md',RUN/'director-architect-draft-v1.md',RUN/'neutral-statement-packet-v1.json',ROOT/'tmp/online-ch2-prescient-cumulative-types-v1.lean']),source_container_closed=False,whole_Goal_status='ACTIVE'))
fixed()
print('Five draft exact targets/probe and neutral packet recorded; source review pending.')
