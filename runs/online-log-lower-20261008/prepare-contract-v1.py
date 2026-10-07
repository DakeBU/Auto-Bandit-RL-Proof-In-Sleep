from common_v1 import *
fixed()
write(RUN/'source-pixel-review-v1.json',dict(actor='/root',actual_tool='view_image(original)',path=(RUN/'source-pdf16-v1.png').as_posix(),sha256=sha(RUN/'source-pdf16-v1.png'),printed_page=4,pdf_page=16,observed='Original page actually viewed: source explicitly declines proof of minimax optimality here, states logarithmic dependence unavoidable, then Theorem1.3 with source half-initialization and4+4lnT upper bound. New harmonic1/6 is derived support, not printed theorem/constant.',independent_external_review=False))
defs='''import BanditRLProof.OnlineLearningMean
import BanditRLProof.OnlineLearningRegret
import BanditRLProof.Exp3ConditionalMoments
import Mathlib.Data.List.Count
import Mathlib.Data.Fintype.Vector
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

noncomputable section
open MeasureTheory Finset Set
namespace BanditRL.OnlineLearning.GuessingLower

/-- History is newest-first: adding b records the next revealed bit after the prediction. -/
noncomputable def polyaNext (h : List Bool) : ℝ :=
  ((h.count true : ℝ) + 1) / ((h.length : ℝ) + 2)

/-- Actual recursively generated path mass; it does not depend on a learner or seed. -/
noncomputable def pathWeight (h : List Bool) : ℝ :=
  match h with
  | [] => 1
  | b :: past => pathWeight past * (if b then polyaNext past else 1 - polyaNext past)

/-- Convert newest-first finite history into chronological labels, padded by false after its end. -/
def binaryStream (h : List Bool) (t : ℕ) : Bool :=
  (h.reverse[t]?).getD false

def binaryValues (h : List Bool) (t : ℕ) : ℝ :=
  if binaryStream h t then 1 else 0

/-- One policy of strict-past labels; no current label or future sequence is passed to A. -/
noncomputable def causalPredict (A : List Bool → ℝ) (y : ℕ → Bool) (t : ℕ) : ℝ :=
  A (List.ofFn (fun i : Fin t => y i)).reverse

/-- Actual shared comparator regret against the feasible empirical-mean hindsight minimizer. -/
noncomputable def pathRegret (A : List Bool → ℝ) (h : List Bool) : ℝ :=
  comparatorRegret (fun t x => (x - binaryValues h t)^2)
    (causalPredict A (binaryStream h)) (empiricalMean (binaryValues h) h.length) h.length

noncomputable def pathExpectation (T : ℕ) (f : List Bool → ℝ) : ℝ :=
  ∑ v : List.Vector Bool T, pathWeight v.toList * f v.toList

/-- Same finite-action Dirac law as the shared Bandit library, instantiated at binary histories. -/
noncomputable def prefixMeasure (T : ℕ) [MeasurableSpace (List.Vector Bool T)] :
    Measure (List.Vector Bool T) :=
  BanditRLProof.Exp3.finiteActionMeasure univ (fun v => pathWeight v.toList)
'''
write(CONTRACT/'planned-definitions-v1.lean.txt',defs+'\nend BanditRL.OnlineLearning.GuessingLower\n')
targets=[
 ('probability_mem','(h : List Bool)','polyaNext h ∈ Ioo (0 : ℝ) 1'),
 ('branch_mass','(h : List Bool)','pathWeight (false :: h) + pathWeight (true :: h) = pathWeight h'),
 ('pathWeight_nonneg','(h : List Bool)','0 ≤ pathWeight h'),
 ('prefix_mass_one','(T : ℕ)','(∑ v : List.Vector Bool T, pathWeight v.toList) = 1'),
 ('prefix_distribution','(T : ℕ)','BanditRLProof.Exp3.FiniteActionDistribution (univ : Finset (List.Vector Bool T)) (fun v => pathWeight v.toList)'),
 ('prefixMeasure_probability','(T : ℕ) [MeasurableSpace (List.Vector Bool T)] [MeasurableSingletonClass (List.Vector Bool T)]','IsProbabilityMeasure (prefixMeasure T)'),
 ('pathExpectation_integral','(T : ℕ) [MeasurableSpace (List.Vector Bool T)] [MeasurableSingletonClass (List.Vector Bool T)] (f : List Bool → ℝ)','(∫ v, f v.toList ∂prefixMeasure T) = pathExpectation T f'),
 ('expected_heads','(T : ℕ)','pathExpectation T (fun h => (h.count true : ℝ)) = (T : ℝ) / 2'),
 ('expected_heads_sq','(T : ℕ)','pathExpectation T (fun h => (h.count true : ℝ)^2) = (T : ℝ) * (2 * (T : ℝ) + 1) / 6'),
 ('expected_next_variance','(T : ℕ)','pathExpectation T (fun h => polyaNext h * (1 - polyaNext h)) = ((T : ℝ) + 3) / (6 * ((T : ℝ) + 2))'),
 ('causalPredict_prefix','(A : List Bool → ℝ) (y z : ℕ → Bool) (t : ℕ) (hpast : ∀ i < t, y i = z i)','causalPredict A y t = causalPredict A z t'),
 ('binary_mean_minimizer','(h : List Bool) (hpos : 0 < h.length)','empiricalMean (binaryValues h) h.length ∈ Icc (0 : ℝ) 1 ∧ ∀ u ∈ Icc (0 : ℝ) 1, (∑ t ∈ range h.length, (empiricalMean (binaryValues h) h.length - binaryValues h t)^2) ≤ ∑ t ∈ range h.length, (u - binaryValues h t)^2'),
 ('conditional_square_lower','(h : List Bool) (x : ℝ)','polyaNext h * (1 - polyaNext h) ≤ (1 - polyaNext h) * x^2 + polyaNext h * (x - 1)^2'),
 ('expected_pathRegret_lower','(A : List Bool → ℝ) (T : ℕ) (hT : 0 < T)','(harmonic (T + 1) : ℝ) / 6 ≤ pathExpectation T (pathRegret A)'),
 ('randomized_harmonic_lower','{Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Ω → List Bool → ℝ) (hA : ∀ h, Measurable (fun ω => A ω h)) (hbound : ∀ ω h, A ω h ∈ Icc (0 : ℝ) 1) (T : ℕ) (hT : 0 < T)','∃ v : List.Vector Bool T, (harmonic (T + 1) : ℝ) / 6 ≤ ∫ ω, pathRegret (A ω) v.toList ∂μ'),
 ('randomized_log_lower','{Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Ω → List Bool → ℝ) (hA : ∀ h, Measurable (fun ω => A ω h)) (hbound : ∀ ω h, A ω h ∈ Icc (0 : ℝ) 1) (T : ℕ) (hT : 0 < T)','∃ v : List.Vector Bool T, Real.log ((T : ℝ) + 2) / 6 ≤ ∫ ω, pathRegret (A ω) v.toList ∂μ')]
headers={name:'theorem '+name+' '+binders+' :\n    '+prop for name,binders,prop in targets}
write(CONTRACT/'planned-public-headers-v1.json',headers)
write(CONTRACT/'planned-statement-fingerprints-v1.json',{name:hashlib.sha256(header.encode('utf-8')).hexdigest() for name,header in headers.items()})
# These are typed proposition definitions, never theorem proofs or placeholder declarations.
shapes=defs+'\n'+''.join('def shape_'+name+' '+binders+' : Prop :=\n  '+prop+'\n\n' for name,binders,prop in targets)+'end BanditRL.OnlineLearning.GuessingLower\n'
write(RUN/'leaves/planned-types-v1.lean',shapes)
gate('planned-types-v1','lake','env','lean',RUN/'leaves/planned-types-v1.lean')
retrieval='''import BanditRLProof.Exp3ConditionalMoments
import Mathlib.Data.List.Count
import Mathlib.Data.Fintype.Vector
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Basic
#check BanditRLProof.Exp3.FiniteActionDistribution
#check BanditRLProof.Exp3.finiteActionMeasure_isProbabilityMeasure
#check BanditRLProof.Exp3.integral_finiteActionMeasure_eq_sum
#check List.count_le_length
#check List.Vector.toList_length
#check Fintype.sum_equiv
#check Fintype.sum_prod_type
#check MeasureTheory.integral_finset_sum
#check MeasureTheory.Integrable.of_bound
#check log_add_one_le_harmonic
'''
write(RUN/'leaves/current-API-types-v1.lean',retrieval)
gate('current-API-types-v1','lake','env','lean',RUN/'leaves/current-API-types-v1.lean')
native('existing-shared-regret-v1','list-lean-decls','comparatorRegret','--statement')
native('existing-shared-mean-v1','list-lean-decls','empiricalMean','--statement')
native('existing-shared-distribution-v1','list-lean-decls','finiteAction','--statement')
write(CONTRACT/'contract-v1.md','''# Required guessing logarithmic lower-bound support

Source is pinned v10, printed4/PDF16 qualitative unavoidability sentence. The source explicitly gives no minimax-optimality proof here. This package supplies separately attributed quantitative derived support, not a source-printed numbered theorem or constant. Actual planned definition text and16 exact theorem headers/type fingerprints are frozen alongside source raw hash. Type-check success is not proof compilation or source acceptance.

Objects: finite binary labels and [0,1] guesses, cumulative squared loss without a1/2factor. A maps newest-first strict-past histories to real predictions; arbitrary initial randomness is represented by Ω, probability measure μ, measurable bounded A(ω,h). Labels law is independent of A/μ/ω: actual recursive masses generated by q(h)=(count_true(h)+1)/(length(h)+2). All nonnegativity, normalization, branch consistency and first/second count moments must be proved from this process. Shared finiteActionDistribution/finiteActionMeasure reused, not assumed; actual expectation is the finite weighted sum under that normalized law, matched to the shared measure integral.

The learner producer receives only prior labels, initial seed, and its fixed policy; source comparator is actual empirical-mean hindsight minimizer in[0,1]. causalPredict_prefix and actual pathRegret/source cumulative-loss bridge are required. No hmin, moment, desired cumulative bound, stability or normalized-law assumption may replace their producers. Binary restriction is an adversary witness inside the source [0,1] class, not a restriction of learner output to binary labels. Existing OnlineGuessingLower's fixed OGD witness cannot prove this universal lower claim.

Terminal: for every probability seed law and measurable [0,1]-valued causal strategy and every T≥1, a fixed length-T binary sequence exists whose expected-seed source regret is at least H(T+1)/6, hence log(T+2)/6. Quantifier order chooses one sequence before seed realization; not a sequence depending on ω. This is cumulative expected regret, not average, high probability, almost sure or a uniform-per-seed bad sequence. Different horizons may use different bad sequences; no one infinite path good for everyT is claimed. Deterministic specializations will be supplied as public canaries/wrappers from this same producer, not assumed distributions or standalone arbitrary algorithm-existence statements. The coefficient1/6 is derived support, not a sharp minimax constant. T0 mass/moment definitions are total, but lower terminals require positiveT (H1/6 would be false atT0).

Initial mathematical dependency DAG: actual probability→path positivity/branch consistency→normalized finite law→derived first/second moments→conditional variance→same causal cumulative loss and empirical-mean minimum→actual expected regret≥harmonic→measurable/integrable seeded mixture and finite bad-sequence existence→log transport. Selected first leaf probability_mem consumes only actual List.count_le_length and real division order; one lower route. Auxiliary decomposition may grow with immutable terminal fingerprints. No literal terminal weakening or hidden seed/adversary coupling.

Allowed edits: own contract/run/task/conversion/obligations/blueprint/retrieval/contribution records; one new reusable shared public module and one test module; public/Test root imports and approved source-qualified Chapter1 reader mapping only after BODY/FINAL reviews and combined gates. Existing source/theorems/reader cards/curatedIDs/registry identities/scanner/config/toolchain/deps/globalSGB/old contracts/protectedpaths unchanged. No optional agent experiment: root director/architect/formalizer plus skill-required distinct reused blind decoder and source reviewer, requestedAstra/medium/history disclosed, no human/external/runtimeattestation. CLI enforces individual checks, not whole paper workflow.

Only C1-LOG-UNAVOIDABLE can eventually close through actual full terminal and gates.16 Chapter1 source items/proof totalnull; full regret/minimum/NoRegret/other six main-relative module audits remain required. Chapter2incomplete/null,3–16unenumerated/necessaryappendicesrequired,totalGoalACTIVE. Exact unmerged PR190 base9425fecb; no main/live/merge/deploy/retirement.
''')
write(CONTRACT/'semantic-signature-v1.json',dict(objects='Binary adversary inside[0,1]; real causal predictions; actual finite law; arbitrary independent probability seed',quantifiers='forallΩ μ A measurable bounded,forallT≥1,existslengthTsequence,then expectedωregret≥bound',hypotheses='Measurable seed outputs and pointwise[0,1] bounds; no probability-law/moment/regret/minimum certificate hypotheses',conclusion='Actual shared cumulative regret against derived empirical mean minimizer, expected over independent seed, harmonic/log lower',constants='H(T+1)/6 and log(T+2)/6 derivedsupport, not source-printed/sharp constants; no1/2 lossnormalization',information='A gets only strict-past newest-first binaryhistory and independentinitialseed; one fixed sequence chosen beforeω',boundary='T≥1 forlower;T0lawtotal;differentbadsequenceperT;notHP/AS/uniformω;no single infinitewitness;sourcequalitativeclaimnotproof',source_package_accepted=False,chapter_complete=False,goal_complete=False))
dag=[('probability_mem',['List.count_le_length','real positive division']),('branch_mass',['actual pathWeight/polyaNext definitions']),('pathWeight_nonneg',['probability_mem']),('prefix_mass_one',['branch_mass','finite vector product decomposition']),('prefix_distribution',['pathWeight_nonneg','prefix_mass_one']),('prefixMeasure_probability',['prefix_distribution','shared finiteActionMeasure probability']),('pathExpectation_integral',['prefix_distribution','shared finiteActionMeasure integral']),('expected_heads',['prefix_mass_one','actual expectation successor recurrence']),('expected_heads_sq',['expected_heads','actual expectation successor recurrence']),('expected_next_variance',['expected_heads','expected_heads_sq','prefix_mass_one']),('causalPredict_prefix',['actual finite prefix construction']),('binary_mean_minimizer',['binaryValues0or1','shared empiricalMean_mem/minimizes']),('conditional_square_lower',['square decomposition']),('expected_pathRegret_lower',['expected_next_variance','causal cumulative-loss recurrence','binary_mean_minimizer','actual shared regret bridge','derived expected optimal loss']),('randomized_harmonic_lower',['expected_pathRegret_lower','derived integrability from boundedmeasurableoutputs','finite normalized-law badsequence existence']),('randomized_log_lower',['randomized_harmonic_lower','log_add_one_le_harmonic'])]
write(CONTRACT/'dependency-DAG-v1.json',dict(nodes=[dict(name=PRE+n,depends_on=d,status='unproved') for n,d in dag],first_selected_leaf=PRE+'probability_mem',mandatory_proof_leaf_total=None,no_missing_obligation_excluded=True))
write(RUN/'10_upper_director.md','SourceClaimREQUIRED. Freeze full expected-seed terminal first, not merely deterministic/conditionalconsumer. Finite actual binarylaw route; oldOGDlowernotreuse endpoint. First leafprobability_mem is ready from actualcount≤length. One lowerroute; no chapter advancement/Goalcompletion.')
write(RUN/'20_middle_formalizer.md','Sixteen typed header obligations/8actual planneddefinitions; actualsharedRegret/mean/distribution reuse. Newest-first history stores revealedlabels, causalPredict reads strictpast only. Requiredlaw/moments/minimum/lossbridge/integrability/badsequence chain staysunproved; typedshapes nottheorems. Distinct mandatory semanticroundtrip beforebodies. Finite probability foundations against mathlib/measure-integral foundation map; globalSGB untouched.')
write(RUN/'30_lower_architect.md','First leafprobability_mem: k=counttrue≤length=n; denominatorn+2>0; numerator≥1>0 and numerator≤n+1<n+2. div_pos/div_lt_one. No regretperformancepremise. Later finite-vector cons equivalence handles normalized branching; momentrecurrences derived from that exactlaw. Add auxiliarylemmas with terminalhash fixed, returnrepair if mismatch.')
for folder in ['tasks','conversion-windows','proof-obligations','proof-blueprints','research-wiki/retrieval-index']:
 p=Path(folder)/(TASK+'.md');note='''\n\n## Version1 draft lower contract\n\nOwn source-card/contract/signature/DAG/planned8definitions/16typedheaders andactualAPIretrieval in docs/contracts/online-guessing-log-lower-v1 and runs/online-log-lower-20261008. Onlytypeschecked,no16theoremproofclaim. Firstprobability leafready, allsource-claim/candidate/rootTests/harness/axiom/canary/sharedBook/FINAL/native/PR stillpending. Original qualitativeunavoidability source printed4/PDF16; H(T+1)/6/log(T+2)/6 are proposed derivedsupport, not printedconstants. Terminalcoversmeasurableboundedrandomizedcausalstrategies withfixedsequencebeforeseed, same actualsharedregret/empirical-meanminimum. Allactual law/moments/bridge/integrability/proof obligationsrequired. Chapter1still16items/proofnull/otherauditsopen;Chapter2incomplete/3–16unenumerated/appendicesrequired/GoalACTIVE; exactOPENunmergedPR190stack/no main/live. One lowerroute/rootstagedroles plusmandatorydistinctactors.\n'''
 if p.exists():p.write_bytes(p.read_bytes()+note.encode())
 else:write(p,'# '+TASK+note)
write(RUN/'memory_digest.md','Task: `'+TASK+'`\nVersion1draft actualsource/types reviewedbyformalizeronly; no proofs/sourceacceptance. Complete law→countmoments→sourcecausalloss/minimum→seededbadsequence/log chainrequired. Firstprobabilityleafready; no source/Goal/chapterclosure.')
# Neutral decoder receives exact contexts renamed, not source identity or prior verdict.
replacements={'polyaNext':'f1','pathWeight':'f2','binaryStream':'f3','binaryValues':'f4','causalPredict':'f5','pathRegret':'f6','pathExpectation':'f7','prefixMeasure':'f8','comparatorRegret':'r','empiricalMean':'m','BanditRLProof.Exp3.FiniteActionDistribution':'P','BanditRLProof.Exp3.finiteActionMeasure':'law'}
def neutral(s):
 for a,b in sorted(replacements.items(),key=lambda x:-len(x[0])):s=s.replace(a,b)
 return s
base='''import Mathlib.Data.List.Count
import Mathlib.Data.Fintype.Vector
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic
noncomputable section
open MeasureTheory Finset Set
namespace NeutralContext
noncomputable def r {X : Type*} (loss : ℕ → X → ℝ) (p : ℕ → X) (u : X) (T : ℕ) : ℝ :=
  (∑ t ∈ range T, loss t (p t)) - ∑ t ∈ range T, loss t u
noncomputable def m (y : ℕ → ℝ) (n : ℕ) : ℝ := (∑ t ∈ range n, y t) / n
structure P {X : Type*} (arms : Finset X) (p : X → ℝ) : Prop where
  nonneg : ∀ x ∈ arms, 0 ≤ p x
  sum_eq_one : arms.sum p = 1
noncomputable def law {X : Type*} [MeasurableSpace X] (arms : Finset X) (p : X → ℝ) : Measure X :=
  arms.sum (fun x => ENNReal.ofReal (p x) • Measure.dirac x)
'''
context=defs.split('namespace BanditRL.OnlineLearning.GuessingLower\n',1)[1]
context=re.sub(r'/--.*?-/\n','',context,flags=re.S)
packet=base+neutral(context)+'\n'+''.join('def N'+str(i).zfill(2)+' '+binders+' : Prop :=\n  '+neutral(prop)+'\n\n' for i,(_,binders,prop) in enumerate(targets,1))+'end NeutralContext\n'
write(RUN/'neutral-packet-v1.lean',packet)
gate('neutral-types-v1','lake','env','lean',RUN/'neutral-packet-v1.lean')
write(RUN/'neutral-input-v1.json',dict(path=(RUN/'neutral-packet-v1.lean').as_posix(),sha256=sha(RUN/'neutral-packet-v1.lean'),number_of_targets=16,definitions_context_only=True,proofs_absent=True,reused_actor_history_must_be_disclosed=True,source_identity_not_supplied_in_packet=True))
fixed();print('Actual16 header shapes and neutral contexts typechecked; source-blind reconstruction/source CONTRACT required before proofs')
