# Pre-proof exact signatures: finite classical-history reset process
Date: 2026-10-09. New internal mathematical model refinement: FC-WO-reset-basis-v1.
Scope: finite computational-basis measurements, fixed normalized fresh initial state,
finite arms, one specified same-arm unitary word per classical history, exactly n
blocks. No horizon truncation, conditional estimator tail, or arbitrary POVM claim.

namespace QuantumBlockEncoding.ResetBlockProcess
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
noncomputable def basisPMF (x : EuclideanSpace ℂ ι) (hx : ‖x‖ = 1) : PMF ι
structure Plan (K D : ℕ) (ι : Type*) [Fintype ι] [DecidableEq ι] where
  arm : Fin K
  word : QuantumQueryWord.Word ι
  bounded : QuantumQueryWord.queryCount word ≤ D
noncomputable def blockPMF {K D : ℕ} (plan : Plan K D ι)
  (oracle : Fin K → Matrix.unitaryGroup ι ℂ)
  (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) : PMF ι
noncomputable def historyLaw {K D : ℕ} (policy : List ι → Plan K D ι)
  (oracle : Fin K → Matrix.unitaryGroup ι ℂ)
  (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) : ℕ → PMF (List ι)

Semantics sealed before proof code: basisPMF(j)=ENNReal.ofReal(||x_j||²), normalized
from BasisHellinger.sum_basisProbability (not a supplied probability-normality premise).
blockPMF(plan)=basisPMF of the actual evaluated word output at oracle(plan.arm),
with norm certificate derived from word unitarity. historyLaw(0)=pure []; step n+1
binds the previous classical history h, creates blockPMF(policy h) using the SAME fresh
ψ (no output-state carry), measures j, then stores h++[j]. Policy is supplied once
and applied identically for each environment; no unknown means or reflections computed.
Exact-real abstract known gates are in scope, finite-bit synthesis/known-state loading
are separate unresolved resources. Plan cap is source for this process model, exact
forward+inverse count is RULED. PMF normality/output-state norm are RULED edges.

Target consumer after signatures compile: theorem historyLaw_length_support ... :
∀ h ∈ (historyLaw policy oracle ψ hψ n).support, h.length = n.
Freeze any final additional theorem signature before proof search, recording amendments.
No manufactured estimator probability theorem is allowed.
