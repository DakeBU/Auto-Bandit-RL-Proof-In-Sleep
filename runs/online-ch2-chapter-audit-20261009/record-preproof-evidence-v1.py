from common_v1 import *
import base64
fixed()
def capture(label,*args):
 tick=time.monotonic();p=subprocess.run(list(map(str,args)),cwd=str(ROOT),stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 write(RUN/(label+'.json'),dict(command=list(map(str,args)),cwd=ROOT.as_posix(),actual_exit=p.returncode,seconds=time.monotonic()-tick,
  stdout_sha256=hashlib.sha256(p.stdout).hexdigest(),stdout_base64=base64.b64encode(p.stdout).decode('ascii')))
 assert p.returncode==0,label

write(RUN/'20_architect-nonsmooth-route-v1.md','''# Finite nonsmooth example route, before proof

Three exact proposed terminal hashes remain fixed in nonsmooth-targets-draft-v1.json; source contract/repair review pending. Two source families, not three independent source results. No theorem body has been written.

Actual pinned-API probe succeeded: all three whole proposition types elaborate, and Mathlib ConvexOn.sup, ConvexOn.comp_affineMap, convexOn_univ_norm/const, DifferentiableAt.abs, not_differentiableAt_abs_zero and real-inner scalar/self APIs plus the actual full E2.27/T2.22/real-germ regularity declarations were retrieved. This does not certify any proposed proof.

Single lower route: shifted absolute is norm precomposed with an affine translation. Differentiability off its center follows from the derivative composition API; a derivative at its center composed with t↦t+c would give the impossible abs derivative at0. Hinge convexity follows from the actual existing affine convexity for slope-a/intercept1 and the constant0 via maximum. Convert global real convexity to the existing EReal epigraph convention. At margin1 the existing complete hinge support formula supplies BOTH0 and-a. An actual derivative would force that support set to a singleton by the accepted real-germ theorem; equality then forcesa0, contradicting margin1. Off margin1 the same complete formula is a singleton, and the reverse accepted equivalence constructs genuine ambient differentiability. This refines the original local-affine-neighborhood plan using exact existing producers; no target change or route proliferation.

For labels usea=y•z, real-inner scalar identity. Global differentiability whena0 is the actual constant1 function. Ifa≠0, inner(a,a) is nonzero and x=inner(a,a)⁻¹•a has inner(a,x)=1, contradicting the pointwise criterion. This constructs the necessary boundary rather than assuming one exists, permits zero dimension/labels/features and provides the explicit source qualification.

Generic pure calculus/algebra reused from pinned Mathlib; source instance interface project-local. No local derivative, legal support or convexity assumption substitutes for a producer at the terminals. Allowed future files NEW OnlineNonsmoothExamples + NEW canary and OWN records; root imports appended only after candidate validation. No old code/pin/source/reader/global frontier changes. Proposed nondegenerate canaries: actualc10 kink and off-center; positive/negative real label slopes; plane boundary and off-boundary; zero label/feature and Fin0 constant1; actual nonzero-normal global failure. Separate blind and source roles remain required. Whole Goal ACTIVE.
''')
for label,args in [
 ('trial-variable-readiness-v1',['trial-log','--task',TASK,'--role','lower','--kind','reuse-audit','--status','compiled','--notes','Current exact unchanged variable OGD types/full scoped BODY reuse: focused9107jobs actual0 plus new whole-type/value kernel actual0, seven inspected standard axiom records. Not new production mathematics or chapter acceptance.','--run-id',RUN.name,'--progress-class','retrieval-reuse','--verifier-evidence','runs/online-ch2-chapter-audit-20261009/variable-readiness-inspected-v1.json']),
 ('trial-source-enumeration-repair-v1',['trial-log','--task',TASK,'--role','reviewer','--kind','source-enumeration','--status','repair','--notes','Distinct v1 source enumeration rejected for E1-E8 precision. Version2/3 repair preserves old drafts/RAW and no old proof modifications; finite new source terminals awaiting distinct review.','--run-id',RUN.name,'--progress-class','diagnostic','--verifier-evidence','runs/online-ch2-chapter-audit-20261009/source-enumeration-review-v1.json']),
 ('trial-nonsmooth-type-retrieval-v1',['trial-log','--task',TASK,'--role','architect','--kind','type-api-retrieval','--status','available','--notes','Actual scoped reference-index/list cards/search/local-decls and exact three proposition/API #check probe actual0. No theorem body or mathematical closure. Two helper declaration-name lookup failures retained; repair qualified exact registry names without changing theorem statements.','--run-id',RUN.name,'--progress-class','retrieval-reuse','--verifier-evidence','runs/online-ch2-chapter-audit-20261009/nonsmooth-type-api-probe-v1.json'])]:
 capture(label,sys.executable,'-B','-X','utf8',RUN/'native-scoped-v1.py',*args)
write(RUN/'memory-digest-preproof-v1.md','''# OWN memory digest, before proof

Whole Chapters1–16 Goal ACTIVE. Chapter1 local complete scope/final delivery accepted097359ac on draft PR203, not main/live. Current C2branch stacked on that exact head, canonical main6847 unchanged. All source images20–35 personally reread and hashed. Existing sharp variable OGD/source package is current exact BODY/header reuse, not a new theorem.

Source enumeration v1 independently rejected for precision. Version3 source proposal preserves65 overlapping audit/navigation containers and exact current native terminal/scoped BODY/provenance join; no independent proof count inferred. Theorem2.21 and Lemma2.31 wrong root draft intentions corrected against actual original/source-review types. Chapter7FTRL pointer is historical PDF35; not a mandatory Chapter2 mathematical theorem. Other forward claims remain REQUIRED/open whole-book source dependencies, especially prescient negative Bregman movement, Chapter5 lower bounds and Chapter3/4/13 model improvements.

First finite genuinely new terminal candidate: two introductory nonsmooth families, three exact types. Abs all shifts, hinge arbitrary real label/feature and actual ambient point/global smoothness criteria. Zero effective normal means constant1; unqualified universal nonsmooth wording requires explicit separate repair review. Blind decoder complete, actual type/API retrieval0, distinct source contract/repair review pending. No production proof body yet. Future lower route uses accepted full hinge supports + differentiability singleton equivalence, not a duplicate support theorem or invented derivative assumption.

Failures retained: defaultPython38 missing pypdfium2, repaired with official bundled runtime; two source-join helper lookup errors (ambiguous short name and guessed namespace) retained, fixed by actual native index. No terminal weakening, no global SGB/frontier/memory/index mutation. All actual retrieval/role/lifecycle records OWN RUN. Chapter2 acceptance/full integrated gates/readers/PR still pending.
''')
fixed();print('Actual scoped native trials and preproof architecture/memory recorded; no production proof started.')
