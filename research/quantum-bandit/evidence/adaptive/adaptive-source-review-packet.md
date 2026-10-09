# Private source comparison packet

## adaptive-information-source.md

# Private original contract: adaptive reset transcript information

Status before implementation: source/statement frozen, not proved. Original
elementary derivation, not attributed to an external paper and no novelty claim.
Inputs remain the frozen local Lean 4.29.1 / Mathlib versions in intake.md.
Owner: BanditRLlib private research adapter; no public registry or upload.

Reuse search: BanditRLProof/LowerBounds/CommonDensityOverlap.lean has measure
affinity/testing but no finite kernel Hellinger chain identity. Mathlib's finite
sums/Real.sqrt and PMF supply the classical algebra. QuantumComputinglib's
BasisHellinger and ResetBlockProcess supply actual normalized output masses and
bounded same-arm words. Searches of the pinned external source snapshots found
no directly compatible adaptive reset theorem; no external import or copy is used.

Source objects: finite outcomes iota, finite arms K (possibly zero if a policy
exists), integer D >= 0, one supplied normalized fresh pure input psi; two actual
unitary oracle families E,F. A single deterministic policy is shared by both
environments and depends only on the prior classical outcome list. Its Plan
contains an arm, chronological word of known unitaries / forward / inverse calls,
and proved syntactic query cap q <= D. No quantum state crosses a block boundary.
For n blocks a finite transcript is a nested pair: Trace(0)=Unit;
Trace(n+1)=Trace(n) x iota, ordered prior history then new outcome. The list view
recursively appends the last outcome. No alternative measurement is introduced.

Let k_E(h,j) be the existing actual computational-basis probability of evaluating
policy(h).word at E(policy(h).arm) on psi. Normalization and nonnegativity MUST be
derived from existing word unitarity, not supplied as new root premises.
The literal transcript density is p_E(0,())=1 and
p_E(n+1,(h,j))=p_E(n,h) k_E(list(h),j). This is the finite density representation
of the reset process, with an explicit PMF/list-law bridge required before claiming
an assertion about the previously defined historyLaw.

H^2(p,q)=sum_x(sqrt(p_x)-sqrt(q_x))^2, without a factor 1/2.
For arbitrary nonnegative parent densities and normalized nonnegative kernels:
H^2(p k, q l) = H^2(p,q) + sum_h sqrt(p_h q_h) H^2(k_h,l_h).
This auxiliary identity need not assume normalized parent densities.

If ||E_i-F_i||op <= eta_i, existing per-word mathematics produces
H^2(k_E(h),k_F(h)) <= D q(h) eta_arm(h)^2.
Define literal weighted trace cost C(n+1,(h,j))=C(n,h)+q(h) eta_arm(h)^2,
and C(0,())=0. It charges both forward/inverse calls, only for the arm used.
Let EC_E(n)=sum_h p_E(n,h) C(n,h), and similarly EC_F.
The intended root is H^2(p_E(n),p_F(n)) <= D/2 (EC_E(n)+EC_F(n)).
No conditional information bound, normalization, unbiasedness, independence of
estimation errors, or adaptive information chain is assumed in this root.

Proof route from the source (to be independently reconstructed): expand the joint
finite sum and square roots, use kernel normalization to obtain the exact chain
identity; use 2 sqrt(p q) <= p+q; prove the actual trace-density/expected-cost
recurrences; induct on n with the produced per-word bound. For uniform eta,
a pathwise real query horizon T bounds C by T eta^2 and yields H^2 <= D T eta^2.
Arm-local weighted costs are retained so one differing arm can support a future
K-arm testing reduction. Such a reduction is NOT proved by this contract.

Boundary: fixed finite number of computational-basis reset blocks; known unitaries
and psi are mathematical model inputs, not free synthesis/loading claims. Empty
words are allowed. Randomized policies, arbitrary POVMs, random stopping,
finite-bit runtime, algorithmic estimation, regret/PAC guarantees and minimax
lower bounds remain separate leaves. A later stopping adapter may encode halted
steps with zero-query words, but is not asserted here. No public graph changes.

## adaptive-information-clarifications.md

# Private explicit source clarifications after first topology review

The original source file and signature seals remain unchanged. This is a separate
clarification ledger, not a rewritten source or retrospectively pre-proof artifact.

1. The original phrase "real query horizon T" was ambiguous: the sealed budget
   consumer uses T : Nat, an actual integer number of oracle calls. This is a
   specialization of a real-valued budget bound, not a proof of every real-T
   variant. The user requested a count of calls. No random stopping guarantee.
2. The native root is Hellinger on nested finite traces. To connect it faithfully
   to the existing list law, need actual PMF masses equal ofReal density, hence
   toReal masses equal density, and an injective history map (with length n).
   Prove these bridges, rather than infer distance invariance from pushforward
   equality alone. The finite-trace root is not yet a literal infinite-List tsum
   Hellinger theorem; no such expression is used in the advertised statement.
3. The uniform weighted-cost bridge must use the existing historyQueryCost
   definition, not a parallel unconnected count. The append recurrence is an
   implementation ingredient. Both forward and inverse calls retain their
   original syntactic accounting.

These clarifications do not change any frozen root signature. New internal
provider proofs supply the missing bridges; they do not add root hypotheses.

## adaptive-information-signatures.txt

-- Signature seal v1. No proof search performed for these statements at sealing.
-- Trace uses universe-polymorphic PUnit at n=0 (Unit-equivalent singleton).
namespace BanditRLProof.AdaptiveTranscript
open QuantumBlockEncoding
open scoped Matrix.Norms.L2Operator

theorem finite_kernel_chain {α β : Type*} [Fintype α] [Fintype β]
    (p q : α → ℝ) (k l : α → β → ℝ)
    (hp : ∀ h, 0 ≤ p h) (hq : ∀ h, 0 ≤ q h)
    (hk : ∀ h j, 0 ≤ k h j) (hl : ∀ h j, 0 ≤ l h j)
    (hk1 : ∀ h, ∑ j, k h j = 1) (hl1 : ∀ h, ∑ j, l h j = 1) :
    BasisHellinger.hellingerSq (fun h : α × β => p h.1 * k h.1 h.2)
      (fun h : α × β => q h.1 * l h.1 h.2) =
      BasisHellinger.hellingerSq p q + ∑ h,
        Real.sqrt (p h) * Real.sqrt (q h) * BasisHellinger.hellingerSq (k h) (l h)

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K D : ℕ}

theorem density_nonneg (policy : List ι → ResetBlockProcess.Plan K D ι)
    (oracle : Fin K → Matrix.unitaryGroup ι ℂ) (ψ : EuclideanSpace ℂ ι)
    (n : ℕ) (h : Trace ι n) : 0 ≤ density policy oracle ψ n h

theorem density_normalized (policy : List ι → ResetBlockProcess.Plan K D ι)
    (oracle : Fin K → Matrix.unitaryGroup ι ℂ) (ψ : EuclideanSpace ℂ ι)
    (hψ : ‖ψ‖ = 1) (n : ℕ) : ∑ h, density policy oracle ψ n h = 1

theorem expectedCost_succ (policy : List ι → ResetBlockProcess.Plan K D ι)
    (oracle : Fin K → Matrix.unitaryGroup ι ℂ) (ψ : EuclideanSpace ℂ ι)
    (hψ : ‖ψ‖ = 1) (η : Fin K → ℝ) (n : ℕ) :
    expectedCost policy oracle ψ η (n + 1) = expectedCost policy oracle ψ η n +
      ∑ h : Trace ι n, density policy oracle ψ n h *
        ((QuantumQueryWord.queryCount (policy (history h)).word : ℝ) *
          η (policy (history h)).arm ^ 2)

theorem adaptive_hellinger_le (policy : List ι → ResetBlockProcess.Plan K D ι)
    (oracleE oracleF : Fin K → Matrix.unitaryGroup ι ℂ)
    (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) (η : Fin K → ℝ)
    (hEF : ∀ i, ‖(oracleE i : Matrix ι ι ℂ) - (oracleF i : Matrix ι ι ℂ)‖ ≤ η i)
    (n : ℕ) :
    BasisHellinger.hellingerSq (density policy oracleE ψ n) (density policy oracleF ψ n) ≤
      (D : ℝ) / 2 *
        (expectedCost policy oracleE ψ η n + expectedCost policy oracleF ψ η n)

-- Post-density, actual PMF construction requires produced density_normalized.
-- A precise PMF/list bridge signature will be frozen separately before its proof.
end BanditRLProof.AdaptiveTranscript

## adaptive-pmf-bridge-signatures.txt

-- Pre-proof bridge seal v1. Same policy/word/basis/fresh-state semantics.
namespace BanditRLProof.AdaptiveTranscript
open QuantumBlockEncoding
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K D : ℕ}

noncomputable def traceLaw (policy : List ι → ResetBlockProcess.Plan K D ι)
    (oracle : Fin K → Matrix.unitaryGroup ι ℂ) (ψ : EuclideanSpace ℂ ι)
    (hψ : ‖ψ‖ = 1) : (n : ℕ) → PMF (Trace ι n)
  | 0 => PMF.pure PUnit.unit
  | n + 1 => (traceLaw policy oracle ψ hψ n).bind fun h =>
      (ResetBlockProcess.blockPMF (policy (history h)) oracle ψ hψ).map (Prod.mk h)

theorem traceLaw_apply (policy : List ι → ResetBlockProcess.Plan K D ι)
    (oracle : Fin K → Matrix.unitaryGroup ι ℂ) (ψ : EuclideanSpace ℂ ι)
    (hψ : ‖ψ‖ = 1) (n : ℕ) (h : Trace ι n) :
    traceLaw policy oracle ψ hψ n h = ENNReal.ofReal (density policy oracle ψ n h)

theorem traceLaw_history_eq (policy : List ι → ResetBlockProcess.Plan K D ι)
    (oracle : Fin K → Matrix.unitaryGroup ι ℂ) (ψ : EuclideanSpace ℂ ι)
    (hψ : ‖ψ‖ = 1) (n : ℕ) :
    (traceLaw policy oracle ψ hψ n).map history =
      ResetBlockProcess.historyLaw policy oracle ψ hψ n

-- Conditional-law equality and normalization are produced, not extra inputs.
-- Not a claim about general POVMs or random stopping.
end BanditRLProof.AdaptiveTranscript

## adaptive-budget-signatures.txt

-- Pre-proof uniform-query horizon consumer seal v1.
namespace BanditRLProof.AdaptiveTranscript
open QuantumBlockEncoding
open scoped Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K D : ℕ}

theorem weightedCost_uniform (policy : List ι → ResetBlockProcess.Plan K D ι)
    (η : ℝ) {n : ℕ} (h : Trace ι n) :
    weightedCost policy (fun _ => η) h =
      (ResetBlockProcess.historyQueryCost policy (history h) : ℝ) * η ^ 2

theorem adaptive_hellinger_budget (policy : List ι → ResetBlockProcess.Plan K D ι)
    (oracleE oracleF : Fin K → Matrix.unitaryGroup ι ℂ)
    (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) (η : ℝ)
    (hEF : ∀ i, ‖(oracleE i : Matrix ι ι ℂ) - (oracleF i : Matrix ι ι ℂ)‖ ≤ η)
    (n T : ℕ)
    (hT : ∀ h : Trace ι n, ResetBlockProcess.historyQueryCost policy (history h) ≤ T) :
    BasisHellinger.hellingerSq
      (fun h => (traceLaw policy oracleE ψ hψ n h).toReal)
      (fun h => (traceLaw policy oracleF ψ hψ n h).toReal) ≤ (D : ℝ) * T * η ^ 2

-- The budget premise is explicit and pathwise for all finite traces, including
-- unreachable ones. It does not implement clipping/stopping; those remain open.
end BanditRLProof.AdaptiveTranscript

## adaptive-formal-packet.md

```lean
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Tactic




namespace QuantumBlockEncoding.BornStability

open scoped InnerProductSpace Matrix.Norms.L2Operator MatrixOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def probability (U P : Matrix ι ι ℂ)
    (ψ : EuclideanSpace ℂ ι) : ℝ :=
  (inner ℂ (Matrix.toEuclideanCLM (𝕜 := ℂ) U ψ)
    (Matrix.toEuclideanCLM (𝕜 := ℂ) P (Matrix.toEuclideanCLM (𝕜 := ℂ) U ψ))).re

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in

theorem effect_norm_le_one (P : Matrix ι ι ℂ) (hP : 0 ≤ P) (hPI : P ≤ 1) :
    ‖P‖ ≤ 1 :=
  by
    letI : CStarAlgebra (Matrix ι ι ℂ) := {}
    exact (CStarAlgebra.norm_le_one_iff_of_nonneg (A := Matrix ι ι ℂ) P hP).mpr hPI

theorem unitary_norm_map (U : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) (ψ : EuclideanSpace ℂ ι) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) U ψ‖ = ‖ψ‖ :=
  ContinuousLinearMap.norm_map_of_mem_unitary
    (Unitary.map_mem (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)) hU) ψ


theorem quadratic_difference_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (P : E →L[ℂ] E) (hP : ‖P‖ ≤ 1)
    (x y : E) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    |(inner ℂ x (P x)).re - (inner ℂ y (P y)).re| ≤ 2 * ‖x - y‖ := by
  have split : inner ℂ x (P x) - inner ℂ y (P y) =
      inner ℂ (x - y) (P x) + inner ℂ y (P (x - y)) := by
    simp only [map_sub, inner_sub_left, inner_sub_right]
    ring
  have hPx : ‖P x‖ ≤ 1 := by
    calc
      ‖P x‖ ≤ ‖P‖ * ‖x‖ := P.le_opNorm x
      _ ≤ 1 := by simpa [hx] using hP
  have hPxy : ‖P (x - y)‖ ≤ ‖x - y‖ := by
    calc
      _ ≤ ‖P‖ * ‖x - y‖ := P.le_opNorm _
      _ ≤ ‖x - y‖ := by nlinarith [norm_nonneg (x - y)]
  calc
    _ = |(inner ℂ x (P x) - inner ℂ y (P y)).re| := by simp
    _ ≤ ‖inner ℂ x (P x) - inner ℂ y (P y)‖ := Complex.abs_re_le_norm _
    _ ≤ ‖inner ℂ (x - y) (P x)‖ + ‖inner ℂ y (P (x - y))‖ := by
      rw [split]; exact norm_add_le _ _
    _ ≤ ‖x - y‖ * ‖P x‖ + ‖y‖ * ‖P (x - y)‖ :=
      add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ ≤ 2 * ‖x - y‖ := by rw [hy]; nlinarith [norm_nonneg (x - y)]


theorem probability_difference_le (U V P : Matrix ι ι ℂ)
    (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) (hV : V ∈ Matrix.unitaryGroup ι ℂ)
    (hP : 0 ≤ P) (hPI : P ≤ 1) {η : ℝ} (hUV : ‖U - V‖ ≤ η) :
    |probability U P ψ - probability V P ψ| ≤ 2 * η := by
  have hPc : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) P‖ ≤ 1 := by
    rw [Matrix.l2_opNorm_toEuclideanCLM]
    exact effect_norm_le_one P hP hPI
  have hd : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) U ψ - Matrix.toEuclideanCLM (𝕜 := ℂ) V ψ‖ ≤ η := by
    calc
      _ = ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (U - V) ψ‖ := by simp
      _ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (U - V)‖ * ‖ψ‖ :=
        (Matrix.toEuclideanCLM (𝕜 := ℂ) (U - V)).le_opNorm ψ
      _ ≤ η := by
        rw [hψ, mul_one, Matrix.l2_opNorm_toEuclideanCLM]
        exact hUV
  exact (quadratic_difference_le _ hPc _ _
    (by rw [unitary_norm_map U hU, hψ])
    (by rw [unitary_norm_map V hV, hψ])).trans (by linarith)



theorem probability_mem_Icc (U P : Matrix ι ι ℂ)
    (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) (hP : 0 ≤ P) (hPI : P ≤ 1) :
    probability U P ψ ∈ Set.Icc (0 : ℝ) 1 := by
  let x := Matrix.toEuclideanCLM (𝕜 := ℂ) U ψ
  have hx : ‖x‖ = 1 := (unitary_norm_map U hU ψ).trans hψ
  have hpos : (Matrix.toEuclideanCLM (𝕜 := ℂ) P).IsPositive := by
    apply (ContinuousLinearMap.isPositive_toLinearMap_iff _).mp
    rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin, Matrix.isPositive_toEuclideanLin_iff]
    exact Matrix.nonneg_iff_posSemidef.mp hP
  refine ⟨hpos.re_inner_nonneg_right x, ?_⟩
  change (inner ℂ x (Matrix.toEuclideanCLM (𝕜 := ℂ) P x)).re ≤ 1
  calc
    _ ≤ ‖inner ℂ x (Matrix.toEuclideanCLM (𝕜 := ℂ) P x)‖ := Complex.re_le_norm _
    _ ≤ ‖x‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℂ) P x‖ := norm_inner_le_norm _ _
    _ ≤ 1 := by
      have hc : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) P‖ ≤ 1 := by
        rw [Matrix.l2_opNorm_toEuclideanCLM]
        exact effect_norm_le_one P hP hPI
      have := (Matrix.toEuclideanCLM (𝕜 := ℂ) P).le_opNorm x
      rw [hx, one_mul]
      rw [hx] at this
      simpa using this.trans (by simpa using hc)

end QuantumBlockEncoding.BornStability
```

```lean
import QuantumBlockEncoding.BornStability











namespace QuantumBlockEncoding.QuantumQueryWord

open scoped Matrix.Norms.L2Operator MatrixOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]



inductive Instruction (ι : Type*) [Fintype ι] [DecidableEq ι]
  | known (gate : Matrix.unitaryGroup ι ℂ)
  | forward
  | inverse

abbrev Word (ι : Type*) [Fintype ι] [DecidableEq ι] := List (Instruction ι)

def Instruction.queryCost : Instruction ι → ℕ
  | .known _ => 0
  | .forward => 1
  | .inverse => 1

def queryCount : Word ι → ℕ
  | [] => 0
  | g :: rest => g.queryCost + queryCount rest

def forwardCount : Word ι → ℕ
  | [] => 0
  | .forward :: rest => 1 + forwardCount rest
  | _ :: rest => forwardCount rest

def inverseCount : Word ι → ℕ
  | [] => 0
  | .inverse :: rest => 1 + inverseCount rest
  | _ :: rest => inverseCount rest

def knownCount : Word ι → ℕ
  | [] => 0
  | .known _ :: rest => 1 + knownCount rest
  | _ :: rest => knownCount rest


theorem queryCount_eq (w : Word ι) : queryCount w = forwardCount w + inverseCount w := by
  induction w with
  | nil => rfl
  | cons g rest ih => cases g <;> simp [queryCount, Instruction.queryCost,
      forwardCount, inverseCount, ih] <;> omega

theorem length_eq_costs (w : Word ι) : w.length = knownCount w + queryCount w := by
  induction w with
  | nil => rfl
  | cons g rest ih => cases g <;> simp [knownCount, queryCount, Instruction.queryCost, ih] <;> omega

noncomputable def Instruction.eval (g : Instruction ι) (U : Matrix ι ι ℂ) :
    Matrix ι ι ℂ :=
  match g with
  | .known gate => gate
  | .forward => U
  | .inverse => star U

noncomputable def eval : Word ι → Matrix ι ι ℂ → Matrix ι ι ℂ
  | [], _ => 1
  | g :: rest, U => eval rest U * g.eval U

theorem Instruction.eval_unitary (g : Instruction ι) (U : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) : g.eval U ∈ Matrix.unitaryGroup ι ℂ := by
  cases g with
  | known gate => exact gate.property
  | forward => exact hU
  | inverse => exact Unitary.star_mem hU


theorem eval_unitary (w : Word ι) (U : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) : eval w U ∈ Matrix.unitaryGroup ι ℂ := by
  induction w with
  | nil => exact (Matrix.unitaryGroup ι ℂ).one_mem
  | cons g rest ih => exact (Matrix.unitaryGroup ι ℂ).mul_mem ih (g.eval_unitary U hU)


theorem eval_append (a b : Word ι) (U : Matrix ι ι ℂ) :
    eval (a ++ b) U = eval b U * eval a U := by
  induction a with
  | nil => simp [eval]
  | cons g rest ih => simp [eval, ih, mul_assoc]

theorem Instruction.eval_distance_le (g : Instruction ι) (U V : Matrix ι ι ℂ)
    {η : ℝ} (hUV : ‖U - V‖ ≤ η) :
    ‖g.eval U - g.eval V‖ ≤ (g.queryCost : ℝ) * η := by
  cases g with
  | known gate => simp [Instruction.eval, Instruction.queryCost]
  | forward => simpa [Instruction.eval, Instruction.queryCost] using hUV
  | inverse => simpa [Instruction.eval, Instruction.queryCost, ← star_sub, norm_star] using hUV



theorem eval_distance_le (w : Word ι) (U V : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) (hV : V ∈ Matrix.unitaryGroup ι ℂ)
    {η : ℝ} (hUV : ‖U - V‖ ≤ η) :
    ‖eval w U - eval w V‖ ≤ (queryCount w : ℝ) * η := by
  induction w with
  | nil => simp [eval, queryCount]
  | cons g rest ih =>
      simp only [eval]
      have split : eval rest U * g.eval U - eval rest V * g.eval V =
          (eval rest U - eval rest V) * g.eval U +
            eval rest V * (g.eval U - g.eval V) := by noncomm_ring
      rw [split]
      calc
        _ ≤ ‖(eval rest U - eval rest V) * g.eval U‖ +
            ‖eval rest V * (g.eval U - g.eval V)‖ := norm_add_le _ _
        _ = ‖eval rest U - eval rest V‖ + ‖g.eval U - g.eval V‖ := by
          rw [CStarRing.norm_mul_mem_unitary _ (g.eval_unitary U hU),
            CStarRing.norm_mem_unitary_mul _ (eval_unitary rest V hV)]
        _ ≤ (queryCount rest : ℝ) * η + (g.queryCost : ℝ) * η :=
          add_le_add ih (g.eval_distance_le U V hUV)
        _ = _ := by simp only [queryCount, Nat.cast_add]; ring


theorem bounded_eval_distance_le (w : Word ι) (U V : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) (hV : V ∈ Matrix.unitaryGroup ι ℂ)
    {η : ℝ} (hUV : ‖U - V‖ ≤ η) {D : ℕ} (hD : queryCount w ≤ D) :
    ‖eval w U - eval w V‖ ≤ (D : ℝ) * η := by
  have hη : 0 ≤ η := (norm_nonneg (U - V)).trans hUV
  exact (eval_distance_le w U V hU hV hUV).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hD) hη)



theorem probability_difference_le (w : Word ι) (U V P : Matrix ι ι ℂ)
    (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) (hV : V ∈ Matrix.unitaryGroup ι ℂ)
    (hP : 0 ≤ P) (hPI : P ≤ 1) {η : ℝ} (hUV : ‖U - V‖ ≤ η) :
    |BornStability.probability (eval w U) P ψ -
      BornStability.probability (eval w V) P ψ| ≤ 2 * (queryCount w : ℝ) * η := by
  simpa [mul_assoc] using BornStability.probability_difference_le
    (eval w U) (eval w V) P ψ hψ (eval_unitary w U hU) (eval_unitary w V hV)
    hP hPI (eval_distance_le w U V hU hV hUV)

theorem bounded_probability_difference_le (w : Word ι) (U V P : Matrix ι ι ℂ)
    (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) (hV : V ∈ Matrix.unitaryGroup ι ℂ)
    (hP : 0 ≤ P) (hPI : P ≤ 1) {η : ℝ} (hUV : ‖U - V‖ ≤ η)
    {D : ℕ} (hD : queryCount w ≤ D) :
    |BornStability.probability (eval w U) P ψ -
      BornStability.probability (eval w V) P ψ| ≤ 2 * (D : ℝ) * η := by
  simpa [mul_assoc] using BornStability.probability_difference_le
    (eval w U) (eval w V) P ψ hψ (eval_unitary w U hU) (eval_unitary w V hV)
    hP hPI (bounded_eval_distance_le w U V hU hV hUV hD)

end QuantumBlockEncoding.QuantumQueryWord
```

```lean
import QuantumBlockEncoding.QuantumQueryWord
import Mathlib.Data.Real.Sqrt









namespace QuantumBlockEncoding.BasisHellinger

open scoped Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι]


noncomputable def basisProbability (x : EuclideanSpace ℂ ι) (j : ι) : ℝ := ‖x j‖ ^ 2


noncomputable def hellingerSq (p r : ι → ℝ) : ℝ :=
  ∑ j, (Real.sqrt (p j) - Real.sqrt (r j)) ^ 2

omit [Fintype ι] in
theorem basisProbability_nonneg (x : EuclideanSpace ℂ ι) (j : ι) :
    0 ≤ basisProbability x j := sq_nonneg _

theorem sum_basisProbability (x : EuclideanSpace ℂ ι) :
    ∑ j, basisProbability x j = ‖x‖ ^ 2 :=
  (PiLp.norm_sq_eq_of_L2 (fun _ : ι => ℂ) x).symm


theorem basisProbability_normalized (x : EuclideanSpace ℂ ι) (hx : ‖x‖ = 1) :
    ∑ j, basisProbability x j = 1 := by rw [sum_basisProbability, hx]; norm_num

omit [Fintype ι] in
theorem sqrt_basisProbability (x : EuclideanSpace ℂ ι) (j : ι) :
    Real.sqrt (basisProbability x j) = ‖x j‖ := Real.sqrt_sq (norm_nonneg _)


theorem hellingerSq_basis_formula (x y : EuclideanSpace ℂ ι) :
    hellingerSq (basisProbability x) (basisProbability y) =
      ∑ j, (‖x j‖ - ‖y j‖) ^ 2 := by
  simp only [hellingerSq, sqrt_basisProbability]

theorem hellingerSq_nonneg (p r : ι → ℝ) : 0 ≤ hellingerSq p r := by
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)


theorem hellingerSq_basis_le (x y : EuclideanSpace ℂ ι) :
    hellingerSq (basisProbability x) (basisProbability y) ≤ ‖x - y‖ ^ 2 := by
  rw [hellingerSq_basis_formula, PiLp.norm_sq_eq_of_L2 (fun _ : ι => ℂ)]
  apply Finset.sum_le_sum
  intro j _
  have h := abs_norm_sub_norm_le (x j) (y j)
  have hs := (sq_le_sq₀ (abs_nonneg (‖x j‖ - ‖y j‖))
    (norm_nonneg (x j - y j))).mpr h
  simpa only [sq_abs, PiLp.sub_apply] using hs

variable [DecidableEq ι]

noncomputable def wordOutput (w : QuantumQueryWord.Word ι) (U : Matrix ι ι ℂ)
    (ψ : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι :=
  Matrix.toEuclideanCLM (𝕜 := ℂ) (QuantumQueryWord.eval w U) ψ


theorem wordOutput_norm (w : QuantumQueryWord.Word ι) (U : Matrix ι ι ℂ)
    (ψ : EuclideanSpace ℂ ι) (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    ‖wordOutput w U ψ‖ = ‖ψ‖ :=
  BornStability.unitary_norm_map _ (QuantumQueryWord.eval_unitary w U hU) ψ

theorem wordOutput_probability_normalized (w : QuantumQueryWord.Word ι)
    (U : Matrix ι ι ℂ) (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    ∑ j, basisProbability (wordOutput w U ψ) j = 1 := by
  apply basisProbability_normalized
  rw [wordOutput_norm w U ψ hU, hψ]


theorem wordOutput_distance_le (w : QuantumQueryWord.Word ι) (U V : Matrix ι ι ℂ)
    (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) (hV : V ∈ Matrix.unitaryGroup ι ℂ)
    {η : ℝ} (hUV : ‖U - V‖ ≤ η) :
    ‖wordOutput w U ψ - wordOutput w V ψ‖ ≤ (QuantumQueryWord.queryCount w : ℝ) * η := by
  calc
    _ = ‖Matrix.toEuclideanCLM (𝕜 := ℂ)
        (QuantumQueryWord.eval w U - QuantumQueryWord.eval w V) ψ‖ := by simp [wordOutput]
    _ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℂ)
        (QuantumQueryWord.eval w U - QuantumQueryWord.eval w V)‖ * ‖ψ‖ :=
      (Matrix.toEuclideanCLM (𝕜 := ℂ)
        (QuantumQueryWord.eval w U - QuantumQueryWord.eval w V)).le_opNorm ψ
    _ ≤ _ := by
      rw [hψ, mul_one, Matrix.l2_opNorm_toEuclideanCLM]
      exact QuantumQueryWord.eval_distance_le w U V hU hV hUV


theorem word_hellingerSq_le (w : QuantumQueryWord.Word ι) (U V : Matrix ι ι ℂ)
    (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) (hV : V ∈ Matrix.unitaryGroup ι ℂ)
    {η : ℝ} (hUV : ‖U - V‖ ≤ η) :
    hellingerSq (basisProbability (wordOutput w U ψ)) (basisProbability (wordOutput w V ψ))
      ≤ (QuantumQueryWord.queryCount w : ℝ) ^ 2 * η ^ 2 := by
  have hd := wordOutput_distance_le w U V ψ hψ hU hV hUV
  have hη : 0 ≤ η := (norm_nonneg (U - V)).trans hUV
  calc
    _ ≤ ‖wordOutput w U ψ - wordOutput w V ψ‖ ^ 2 := hellingerSq_basis_le _ _
    _ ≤ ((QuantumQueryWord.queryCount w : ℝ) * η) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hη)).mpr hd
    _ = _ := by ring



theorem bounded_word_hellingerSq_le (w : QuantumQueryWord.Word ι) (U V : Matrix ι ι ℂ)
    (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) (hV : V ∈ Matrix.unitaryGroup ι ℂ)
    {η : ℝ} (hUV : ‖U - V‖ ≤ η) {D : ℕ} (hD : QuantumQueryWord.queryCount w ≤ D) :
    hellingerSq (basisProbability (wordOutput w U ψ)) (basisProbability (wordOutput w V ψ))
      ≤ (D : ℝ) * (QuantumQueryWord.queryCount w : ℝ) * η ^ 2 := by
  have hD' : (QuantumQueryWord.queryCount w : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  calc
    _ ≤ (QuantumQueryWord.queryCount w : ℝ) ^ 2 * η ^ 2 :=
      word_hellingerSq_le w U V ψ hψ hU hV hUV
    _ = ((QuantumQueryWord.queryCount w : ℝ) * (QuantumQueryWord.queryCount w : ℝ)) *
        η ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hD' (Nat.cast_nonneg _)) (sq_nonneg η)

end QuantumBlockEncoding.BasisHellinger
```

```lean
import QuantumBlockEncoding.BasisHellinger
import Mathlib.Probability.ProbabilityMassFunction.Constructions











namespace QuantumBlockEncoding.ResetBlockProcess

open scoped Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]



noncomputable def basisPMF (x : EuclideanSpace ℂ ι) (hx : ‖x‖ = 1) : PMF ι :=
  PMF.ofFintype (fun j => ENNReal.ofReal (BasisHellinger.basisProbability x j)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg
      (fun j _ => BasisHellinger.basisProbability_nonneg x j)]
    rw [BasisHellinger.basisProbability_normalized x hx, ENNReal.ofReal_one])

theorem basisPMF_apply (x : EuclideanSpace ℂ ι) (hx : ‖x‖ = 1) (j : ι) :
    basisPMF x hx j = ENNReal.ofReal (BasisHellinger.basisProbability x j) := rfl



structure Plan (K D : ℕ) (ι : Type*) [Fintype ι] [DecidableEq ι] where
  arm : Fin K
  word : QuantumQueryWord.Word ι
  bounded : QuantumQueryWord.queryCount word ≤ D



noncomputable def blockPMF {K D : ℕ} (plan : Plan K D ι)
    (oracle : Fin K → Matrix.unitaryGroup ι ℂ)
    (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) : PMF ι :=
  basisPMF (BasisHellinger.wordOutput plan.word (oracle plan.arm) ψ) (by
    rw [BasisHellinger.wordOutput_norm plan.word (oracle plan.arm) ψ
      (oracle plan.arm).property, hψ])

theorem blockPMF_apply {K D : ℕ} (plan : Plan K D ι)
    (oracle : Fin K → Matrix.unitaryGroup ι ℂ)
    (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) (j : ι) :
    blockPMF plan oracle ψ hψ j = ENNReal.ofReal
      (BasisHellinger.basisProbability
        (BasisHellinger.wordOutput plan.word (oracle plan.arm) ψ) j) := rfl



noncomputable def historyLaw {K D : ℕ} (policy : List ι → Plan K D ι)
    (oracle : Fin K → Matrix.unitaryGroup ι ℂ)
    (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) : ℕ → PMF (List ι)
  | 0 => PMF.pure []
  | n + 1 => (historyLaw policy oracle ψ hψ n).bind fun h =>
      (blockPMF (policy h) oracle ψ hψ).bind fun j => PMF.pure (h ++ [j])



theorem historyLaw_length_support {K D : ℕ}
    (policy : List ι → Plan K D ι)
    (oracle : Fin K → Matrix.unitaryGroup ι ℂ)
    (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) (n : ℕ) :
    ∀ h ∈ (historyLaw policy oracle ψ hψ n).support, h.length = n := by
  induction n with
  | zero =>
      intro h hh
      have heq : h = [] := (PMF.mem_support_pure_iff [] h).mp hh
      simp [heq]
  | succ n ih =>
      intro h hh
      obtain ⟨previous, hprevious, hblock⟩ := (PMF.mem_support_bind_iff _ _ h).mp hh
      obtain ⟨j, _, hout⟩ := (PMF.mem_support_bind_iff _ _ h).mp hblock
      have heq : h = previous ++ [j] := (PMF.mem_support_pure_iff _ h).mp hout
      simp [heq, ih previous hprevious]



def historyQueryCost {K D : ℕ} (policy : List ι → Plan K D ι) (h : List ι) : ℕ :=
  (Finset.range h.length).sum
    (fun t => QuantumQueryWord.queryCount (policy (h.take t)).word)

theorem historyQueryCost_le {K D : ℕ} (policy : List ι → Plan K D ι) (h : List ι) :
    historyQueryCost policy h ≤ h.length * D := by
  unfold historyQueryCost
  calc
    _ ≤ (Finset.range h.length).sum (fun _ => D) :=
      Finset.sum_le_sum (fun t _ => (policy (h.take t)).bounded)
    _ = _ := by simp

theorem historyLaw_queryCost_le {K D : ℕ}
    (policy : List ι → Plan K D ι)
    (oracle : Fin K → Matrix.unitaryGroup ι ℂ)
    (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) (n : ℕ) :
    ∀ h ∈ (historyLaw policy oracle ψ hψ n).support,
      historyQueryCost policy h ≤ n * D := by
  intro h hh
  have hlength := historyLaw_length_support policy oracle ψ hψ n h hh
  simpa only [hlength] using historyQueryCost_le policy h


theorem historyLaw_queryCost_le_budget {K D : ℕ}
    (policy : List ι → Plan K D ι)
    (oracle : Fin K → Matrix.unitaryGroup ι ℂ)
    (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) (n : ℕ)
    {T : ℕ} (hT : n * D ≤ T) :
    ∀ h ∈ (historyLaw policy oracle ψ hψ n).support,
      historyQueryCost policy h ≤ T := by
  intro h hh
  exact (historyLaw_queryCost_le policy oracle ψ hψ n h hh).trans hT

end QuantumBlockEncoding.ResetBlockProcess
```

```lean
import QuantumBlockEncoding.ResetBlockProcess
import Mathlib.Tactic

namespace BanditRLProof.AdaptiveTranscript

open QuantumBlockEncoding
open scoped Matrix.Norms.L2Operator

theorem hellingerSq_expand {α : Type*} [Fintype α] (p q : α → ℝ)
    (hp : ∀ h, 0 ≤ p h) (hq : ∀ h, 0 ≤ q h) :
    BasisHellinger.hellingerSq p q =
      (∑ h, p h) + (∑ h, q h) - 2 * ∑ h, Real.sqrt (p h) * Real.sqrt (q h) := by
  unfold BasisHellinger.hellingerSq
  calc
    _ = ∑ h, (p h + q h - 2 * (Real.sqrt (p h) * Real.sqrt (q h))) := by
      apply Finset.sum_congr rfl
      intro h _
      nlinarith [Real.sq_sqrt (hp h), Real.sq_sqrt (hq h)]
    _ = _ := by simp [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]

theorem finite_kernel_chain {α β : Type*} [Fintype α] [Fintype β]
    (p q : α → ℝ) (k l : α → β → ℝ)
    (hp : ∀ h, 0 ≤ p h) (hq : ∀ h, 0 ≤ q h)
    (hk : ∀ h j, 0 ≤ k h j) (hl : ∀ h j, 0 ≤ l h j)
    (hk1 : ∀ h, ∑ j, k h j = 1) (hl1 : ∀ h, ∑ j, l h j = 1) :
    BasisHellinger.hellingerSq (fun h : α × β => p h.1 * k h.1 h.2)
      (fun h : α × β => q h.1 * l h.1 h.2) =
      BasisHellinger.hellingerSq p q + ∑ h,
        Real.sqrt (p h) * Real.sqrt (q h) * BasisHellinger.hellingerSq (k h) (l h) := by
  have row (h : α) :
      (∑ j, (Real.sqrt (p h * k h j) - Real.sqrt (q h * l h j)) ^ 2) =
        (Real.sqrt (p h) - Real.sqrt (q h)) ^ 2 +
          Real.sqrt (p h) * Real.sqrt (q h) * BasisHellinger.hellingerSq (k h) (l h) := by
    change BasisHellinger.hellingerSq (fun j => p h * k h j)
      (fun j => q h * l h j) = _
    rw [hellingerSq_expand _ _ (fun j => mul_nonneg (hp h) (hk h j))
      (fun j => mul_nonneg (hq h) (hl h j))]
    simp_rw [Real.sqrt_mul (hp h), Real.sqrt_mul (hq h)]
    have cross : (∑ j, Real.sqrt (p h) * Real.sqrt (k h j) *
        (Real.sqrt (q h) * Real.sqrt (l h j))) =
        Real.sqrt (p h) * Real.sqrt (q h) * ∑ j, Real.sqrt (k h j) * Real.sqrt (l h j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [cross, ← Finset.mul_sum, ← Finset.mul_sum, hk1 h, hl1 h,
      hellingerSq_expand _ _ (hk h) (hl h), hk1 h, hl1 h]
    nlinarith [Real.sq_sqrt (hp h), Real.sq_sqrt (hq h)]
  unfold BasisHellinger.hellingerSq
  rw [Fintype.sum_prod_type]
  simp_rw [row]
  rw [Finset.sum_add_distrib]
  rfl

universe u

def Trace (ι : Type u) : ℕ → Type u
  | 0 => PUnit
  | n + 1 => Trace ι n × ι

instance traceFintype {ι : Type*} [Fintype ι] (n : ℕ) : Fintype (Trace ι n) :=
  match n with
  | 0 => inferInstanceAs (Fintype PUnit)
  | n + 1 => @instFintypeProd (Trace ι n) ι (traceFintype n) inferInstance

def history {ι : Type*} : {n : ℕ} → Trace ι n → List ι
  | 0, _ => []
  | _ + 1, h => history h.1 ++ [h.2]

theorem history_length {ι : Type*} {n : ℕ} (h : Trace ι n) : (history h).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [history, ih]

theorem history_injective {ι : Type*} (n : ℕ) : Function.Injective (history (ι := ι) (n := n)) := by
  induction n with
  | zero => intro a b _; cases a; cases b; rfl
  | succ n ih =>
      intro a b hab
      have lengths : (history a.1).length = (history b.1).length := by rw [history_length, history_length]
      obtain ⟨ha, hb⟩ := List.append_inj hab lengths
      exact Prod.ext (ih ha) (List.singleton_inj.mp hb)

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K D : ℕ}

noncomputable def kernel (policy : List ι → ResetBlockProcess.Plan K D ι)
    (oracle : Fin K → Matrix.unitaryGroup ι ℂ) (ψ : EuclideanSpace ℂ ι)
    (h : List ι) (j : ι) : ℝ :=
  BasisHellinger.basisProbability
    (BasisHellinger.wordOutput (policy h).word (oracle (policy h).arm) ψ) j

noncomputable def density (policy : List ι → ResetBlockProcess.Plan K D ι)
    (oracle : Fin K → Matrix.unitaryGroup ι ℂ) (ψ : EuclideanSpace ℂ ι) :
    (n : ℕ) → Trace ι n → ℝ
  | 0, _ => 1
  | n + 1, h => density policy oracle ψ n h.1 * kernel policy oracle ψ (history h.1) h.2

noncomputable def weightedCost (policy : List ι → ResetBlockProcess.Plan K D ι)
    (η : Fin K → ℝ) : {n : ℕ} → Trace ι n → ℝ
  | 0, _ => 0
  | _ + 1, h => weightedCost policy η h.1 +
      (QuantumQueryWord.queryCount (policy (history h.1)).word : ℝ) *
        η (policy (history h.1)).arm ^ 2

noncomputable def expectedCost (policy : List ι → ResetBlockProcess.Plan K D ι)
    (oracle : Fin K → Matrix.unitaryGroup ι ℂ) (ψ : EuclideanSpace ℂ ι)
    (η : Fin K → ℝ) (n : ℕ) : ℝ :=
  ∑ h : Trace ι n, density policy oracle ψ n h * weightedCost policy η h

theorem kernel_nonneg (policy : List ι → ResetBlockProcess.Plan K D ι)
    (oracle : Fin K → Matrix.unitaryGroup ι ℂ) (ψ : EuclideanSpace ℂ ι)
    (h : List ι) (j : ι) : 0 ≤ kernel policy oracle ψ h j :=
  BasisHellinger.basisProbability_nonneg _ _

theorem kernel_normalized (policy : List ι → ResetBlockProcess.Plan K D ι)
    (oracle : Fin K → Matrix.unitaryGroup ι ℂ) (ψ : EuclideanSpace ℂ ι)
    (hψ : ‖ψ‖ = 1) (h : List ι) : ∑ j, kernel policy oracle ψ h j = 1 :=
  BasisHellinger.wordOutput_probability_normalized (policy h).word
    (oracle (policy h).arm) ψ hψ (oracle (policy h).arm).property

theorem density_nonneg (policy : List ι → ResetBlockProcess.Plan K D ι)
    (oracle : Fin K → Matrix.unitaryGroup ι ℂ) (ψ : EuclideanSpace ℂ ι)
    (n : ℕ) (h : Trace ι n) : 0 ≤ density policy oracle ψ n h := by
  induction n with
  | zero => exact zero_le_one
  | succ n ih => exact mul_nonneg (ih h.1) (kernel_nonneg _ _ _ _ _)

theorem density_normalized (policy : List ι → ResetBlockProcess.Plan K D ι)
    (oracle : Fin K → Matrix.unitaryGroup ι ℂ) (ψ : EuclideanSpace ℂ ι)
    (hψ : ‖ψ‖ = 1) (n : ℕ) : ∑ h, density policy oracle ψ n h = 1 := by
  induction n with
  | zero => simp [Trace, density]
  | succ n ih =>
      change (∑ h : Trace ι n × ι,
        density policy oracle ψ n h.1 * kernel policy oracle ψ (history h.1) h.2) = 1
      rw [Fintype.sum_prod_type]
      simp_rw [← Finset.mul_sum, kernel_normalized policy oracle ψ hψ, mul_one]
      exact ih

theorem expectedCost_succ (policy : List ι → ResetBlockProcess.Plan K D ι)
    (oracle : Fin K → Matrix.unitaryGroup ι ℂ) (ψ : EuclideanSpace ℂ ι)
    (hψ : ‖ψ‖ = 1) (η : Fin K → ℝ) (n : ℕ) :
    expectedCost policy oracle ψ η (n + 1) = expectedCost policy oracle ψ η n +
      ∑ h : Trace ι n, density policy oracle ψ n h *
        ((QuantumQueryWord.queryCount (policy (history h)).word : ℝ) *
          η (policy (history h)).arm ^ 2) := by
  unfold expectedCost
  change (∑ h : Trace ι n × ι,
      (density policy oracle ψ n h.1 * kernel policy oracle ψ (history h.1) h.2) *
        (weightedCost policy η h.1 +
          (QuantumQueryWord.queryCount (policy (history h.1)).word : ℝ) *
            η (policy (history h.1)).arm ^ 2)) = _
  rw [Fintype.sum_prod_type, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro h _
  calc
    _ = density policy oracle ψ n h *
        (weightedCost policy η h + (QuantumQueryWord.queryCount (policy (history h)).word : ℝ) *
          η (policy (history h)).arm ^ 2) * ∑ j, kernel policy oracle ψ (history h) j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by rw [kernel_normalized policy oracle ψ hψ, mul_one]; ring

theorem kernel_hellinger_le (policy : List ι → ResetBlockProcess.Plan K D ι)
    (oracleE oracleF : Fin K → Matrix.unitaryGroup ι ℂ)
    (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) (η : Fin K → ℝ)
    (hEF : ∀ i, ‖(oracleE i : Matrix ι ι ℂ) - (oracleF i : Matrix ι ι ℂ)‖ ≤ η i)
    (h : List ι) :
    BasisHellinger.hellingerSq (kernel policy oracleE ψ h) (kernel policy oracleF ψ h) ≤
      (D : ℝ) * ((QuantumQueryWord.queryCount (policy h).word : ℝ) *
        η (policy h).arm ^ 2) := by
  have bound := BasisHellinger.bounded_word_hellingerSq_le (policy h).word
    (oracleE (policy h).arm) (oracleF (policy h).arm) ψ hψ
    (oracleE (policy h).arm).property (oracleF (policy h).arm).property
    (hEF (policy h).arm) (policy h).bounded
  simpa only [kernel, mul_assoc] using bound

theorem adaptive_hellinger_le (policy : List ι → ResetBlockProcess.Plan K D ι)
    (oracleE oracleF : Fin K → Matrix.unitaryGroup ι ℂ)
    (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) (η : Fin K → ℝ)
    (hEF : ∀ i, ‖(oracleE i : Matrix ι ι ℂ) - (oracleF i : Matrix ι ι ℂ)‖ ≤ η i)
    (n : ℕ) :
    BasisHellinger.hellingerSq (density policy oracleE ψ n) (density policy oracleF ψ n) ≤
      (D : ℝ) / 2 *
        (expectedCost policy oracleE ψ η n + expectedCost policy oracleF ψ η n) := by
  induction n with
  | zero => simp [expectedCost, weightedCost, density, Trace, BasisHellinger.hellingerSq]
  | succ n ih =>
      change BasisHellinger.hellingerSq
        (fun h : Trace ι n × ι => density policy oracleE ψ n h.1 *
          kernel policy oracleE ψ (history h.1) h.2)
        (fun h : Trace ι n × ι => density policy oracleF ψ n h.1 *
          kernel policy oracleF ψ (history h.1) h.2) ≤ _
      rw [finite_kernel_chain _ _ _ _ (density_nonneg policy oracleE ψ n)
        (density_nonneg policy oracleF ψ n)
        (fun h => kernel_nonneg policy oracleE ψ (history h))
        (fun h => kernel_nonneg policy oracleF ψ (history h))
        (fun h => kernel_normalized policy oracleE ψ hψ (history h))
        (fun h => kernel_normalized policy oracleF ψ hψ (history h))]
      let step : Trace ι n → ℝ := fun h =>
        (QuantumQueryWord.queryCount (policy (history h)).word : ℝ) *
          η (policy (history h)).arm ^ 2
      have hstep :
          (∑ h : Trace ι n, Real.sqrt (density policy oracleE ψ n h) *
            Real.sqrt (density policy oracleF ψ n h) *
            BasisHellinger.hellingerSq (kernel policy oracleE ψ (history h))
              (kernel policy oracleF ψ (history h))) ≤
          (D : ℝ) / 2 * ((∑ h, density policy oracleE ψ n h * step h) +
            ∑ h, density policy oracleF ψ n h * step h) := by
        calc
          _ ≤ ∑ h : Trace ι n, (D : ℝ) / 2 *
              (density policy oracleE ψ n h * step h + density policy oracleF ψ n h * step h) := by
            apply Finset.sum_le_sum
            intro h _
            have hinfo := kernel_hellinger_le policy oracleE oracleF ψ hψ η hEF (history h)
            have ha := Real.sq_sqrt (density_nonneg policy oracleE ψ n h)
            have hb := Real.sq_sqrt (density_nonneg policy oracleF ψ n h)
            have ham : 2 * Real.sqrt (density policy oracleE ψ n h) *
                Real.sqrt (density policy oracleF ψ n h) ≤
                density policy oracleE ψ n h + density policy oracleF ψ n h := by
              nlinarith [sq_nonneg (Real.sqrt (density policy oracleE ψ n h) -
                Real.sqrt (density policy oracleF ψ n h))]
            have hs : 0 ≤ step h := mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
            have hmul := mul_le_mul_of_nonneg_left hinfo
              (mul_nonneg (Real.sqrt_nonneg (density policy oracleE ψ n h))
                (Real.sqrt_nonneg (density policy oracleF ψ n h)))
            have ham' := mul_le_mul_of_nonneg_right ham (mul_nonneg (Nat.cast_nonneg D) hs)
            change _ ≤ (D : ℝ) * step h at hinfo
            change _ ≤ Real.sqrt (density policy oracleE ψ n h) *
              Real.sqrt (density policy oracleF ψ n h) * ((D : ℝ) * step h) at hmul
            nlinarith
          _ = _ := by rw [← Finset.mul_sum, Finset.sum_add_distrib]
      have he := expectedCost_succ policy oracleE ψ hψ η n
      have hf := expectedCost_succ policy oracleF ψ hψ η n
      change expectedCost policy oracleE ψ η (n + 1) =
        expectedCost policy oracleE ψ η n + ∑ h, density policy oracleE ψ n h * step h at he
      change expectedCost policy oracleF ψ η (n + 1) =
        expectedCost policy oracleF ψ η n + ∑ h, density policy oracleF ψ n h * step h at hf
      rw [he, hf]
      exact (add_le_add ih hstep).trans_eq (by ring)

noncomputable def traceLaw (policy : List ι → ResetBlockProcess.Plan K D ι)
    (oracle : Fin K → Matrix.unitaryGroup ι ℂ) (ψ : EuclideanSpace ℂ ι)
    (hψ : ‖ψ‖ = 1) : (n : ℕ) → PMF (Trace ι n)
  | 0 => PMF.pure PUnit.unit
  | n + 1 => (traceLaw policy oracle ψ hψ n).bind fun h =>
      (ResetBlockProcess.blockPMF (policy (history h)) oracle ψ hψ).map (Prod.mk h)

open scoped Classical in
theorem map_pair_apply {α β : Type*} [Fintype β]
    (p : PMF β) (a : α) (h : α × β) :
    p.map (Prod.mk a) h = if h.1 = a then p h.2 else 0 := by
  classical
  rcases h with ⟨x, y⟩
  by_cases ha : x = a
  · subst x
    simp [PMF.map_apply, tsum_fintype]
  · simp [PMF.map_apply, tsum_fintype, Prod.mk.injEq, ha]

theorem traceLaw_apply (policy : List ι → ResetBlockProcess.Plan K D ι)
    (oracle : Fin K → Matrix.unitaryGroup ι ℂ) (ψ : EuclideanSpace ℂ ι)
    (hψ : ‖ψ‖ = 1) (n : ℕ) (h : Trace ι n) :
    traceLaw policy oracle ψ hψ n h = ENNReal.ofReal (density policy oracle ψ n h) := by
  classical
  induction n with
  | zero => cases h; simp [traceLaw, density]
  | succ n ih =>
      change ((traceLaw policy oracle ψ hψ n).bind fun previous =>
        (ResetBlockProcess.blockPMF (policy (history previous)) oracle ψ hψ).map (Prod.mk previous)) h = _
      rw [PMF.bind_apply, tsum_fintype]
      simp_rw [map_pair_apply, mul_ite, mul_zero]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [ih, ResetBlockProcess.blockPMF_apply, ← ENNReal.ofReal_mul
        (density_nonneg policy oracle ψ n h.1)]
      rfl

theorem traceLaw_history_eq (policy : List ι → ResetBlockProcess.Plan K D ι)
    (oracle : Fin K → Matrix.unitaryGroup ι ℂ) (ψ : EuclideanSpace ℂ ι)
    (hψ : ‖ψ‖ = 1) (n : ℕ) :
    (traceLaw policy oracle ψ hψ n).map history =
      ResetBlockProcess.historyLaw policy oracle ψ hψ n := by
  induction n with
  | zero => simp [traceLaw, ResetBlockProcess.historyLaw, PMF.pure_map, history]
  | succ n ih =>
      calc
        _ = (traceLaw policy oracle ψ hψ n).bind fun h =>
            (ResetBlockProcess.blockPMF (policy (history h)) oracle ψ hψ).map
              (fun j => history h ++ [j]) := by
          simp only [traceLaw, PMF.map_bind, PMF.map_comp]
          rfl
        _ = ((traceLaw policy oracle ψ hψ n).map history).bind fun h =>
            (ResetBlockProcess.blockPMF (policy h) oracle ψ hψ).bind fun j =>
              PMF.pure (h ++ [j]) := by
          rw [PMF.bind_map]
          rfl
        _ = _ := by rw [ih]; rfl

theorem traceLaw_toReal (policy : List ι → ResetBlockProcess.Plan K D ι)
    (oracle : Fin K → Matrix.unitaryGroup ι ℂ) (ψ : EuclideanSpace ℂ ι)
    (hψ : ‖ψ‖ = 1) (n : ℕ) (h : Trace ι n) :
    (traceLaw policy oracle ψ hψ n h).toReal = density policy oracle ψ n h := by
  rw [traceLaw_apply, ENNReal.toReal_ofReal (density_nonneg policy oracle ψ n h)]

theorem historyLaw_apply_at_trace (policy : List ι → ResetBlockProcess.Plan K D ι)
    (oracle : Fin K → Matrix.unitaryGroup ι ℂ) (ψ : EuclideanSpace ℂ ι)
    (hψ : ‖ψ‖ = 1) (n : ℕ) (h : Trace ι n) :
    ResetBlockProcess.historyLaw policy oracle ψ hψ n (history h) =
      ENNReal.ofReal (density policy oracle ψ n h) := by
  classical
  rw [← traceLaw_history_eq, PMF.map_apply, tsum_fintype]
  simp only [(history_injective n).eq_iff, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  exact traceLaw_apply _ _ _ _ _ _

theorem historyQueryCost_append (policy : List ι → ResetBlockProcess.Plan K D ι)
    (h : List ι) (j : ι) :
    ResetBlockProcess.historyQueryCost policy (h ++ [j]) =
      ResetBlockProcess.historyQueryCost policy h + QuantumQueryWord.queryCount (policy h).word := by
  unfold ResetBlockProcess.historyQueryCost
  simp only [List.length_append, List.length_singleton, Finset.sum_range_succ]
  congr 1
  · apply Finset.sum_congr rfl
    intro t ht
    rw [List.take_append_of_le_length (Nat.le_of_lt (Finset.mem_range.mp ht))]
  · simp

theorem weightedCost_uniform (policy : List ι → ResetBlockProcess.Plan K D ι)
    (η : ℝ) {n : ℕ} (h : Trace ι n) :
    weightedCost policy (fun _ => η) h =
      (ResetBlockProcess.historyQueryCost policy (history h) : ℝ) * η ^ 2 := by
  induction n with
  | zero => simp [weightedCost, history, ResetBlockProcess.historyQueryCost]
  | succ n ih =>
      change weightedCost policy (fun _ => η) h.1 +
        (QuantumQueryWord.queryCount (policy (history h.1)).word : ℝ) * η ^ 2 =
        (ResetBlockProcess.historyQueryCost policy (history h.1 ++ [h.2]) : ℝ) * η ^ 2
      rw [ih, historyQueryCost_append, Nat.cast_add]
      ring

theorem expectedCost_le (policy : List ι → ResetBlockProcess.Plan K D ι)
    (oracle : Fin K → Matrix.unitaryGroup ι ℂ) (ψ : EuclideanSpace ℂ ι)
    (hψ : ‖ψ‖ = 1) (η : Fin K → ℝ) (n : ℕ) (B : ℝ)
    (hB : ∀ h : Trace ι n, weightedCost policy η h ≤ B) :
    expectedCost policy oracle ψ η n ≤ B := by
  calc
    _ ≤ ∑ h : Trace ι n, density policy oracle ψ n h * B :=
      Finset.sum_le_sum fun h _ => mul_le_mul_of_nonneg_left (hB h) (density_nonneg _ _ _ _ _)
    _ = B := by rw [← Finset.sum_mul, density_normalized policy oracle ψ hψ n, one_mul]

theorem adaptive_hellinger_budget (policy : List ι → ResetBlockProcess.Plan K D ι)
    (oracleE oracleF : Fin K → Matrix.unitaryGroup ι ℂ)
    (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) (η : ℝ)
    (hEF : ∀ i, ‖(oracleE i : Matrix ι ι ℂ) - (oracleF i : Matrix ι ι ℂ)‖ ≤ η)
    (n T : ℕ)
    (hT : ∀ h : Trace ι n, ResetBlockProcess.historyQueryCost policy (history h) ≤ T) :
    BasisHellinger.hellingerSq
      (fun h => (traceLaw policy oracleE ψ hψ n h).toReal)
      (fun h => (traceLaw policy oracleF ψ hψ n h).toReal) ≤ (D : ℝ) * T * η ^ 2 := by
  simp_rw [traceLaw_toReal]
  have hcost (h : Trace ι n) : weightedCost policy (fun _ => η) h ≤ (T : ℝ) * η ^ 2 := by
    rw [weightedCost_uniform]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hT h) (sq_nonneg η)
  have he := expectedCost_le policy oracleE ψ hψ (fun _ => η) n _ hcost
  have hf := expectedCost_le policy oracleF ψ hψ (fun _ => η) n _ hcost
  calc
    _ ≤ (D : ℝ) / 2 * (expectedCost policy oracleE ψ (fun _ => η) n +
        expectedCost policy oracleF ψ (fun _ => η) n) :=
      adaptive_hellinger_le policy oracleE oracleF ψ hψ (fun _ => η) hEF n
    _ ≤ (D : ℝ) / 2 * ((T : ℝ) * η ^ 2 + (T : ℝ) * η ^ 2) :=
      mul_le_mul_of_nonneg_left (add_le_add he hf) (by positivity)
    _ = _ := by ring

end BanditRLProof.AdaptiveTranscript
```

## adaptive-blind-reconstruction.md

﻿# Blind semantic reconstruction of AdaptiveTranscript

Actor identity: `/root/adaptive_blind_decode`, the same distinct blind semantic decoder continuing an additional decoding pass.

Input packet: `C:/qb261009/bandit/.private/attempts/2026-10-09/adaptive-formal-packet.md`.

Exact current packet SHA256: `DB2F1189D0132BFB6467CAEC516409482D9B0011F7B4847591D1BC073C91A935`.

Scope: this is a transparent additional blind decoding pass by the same actor. Only the current formal packet and this actor's prior reconstruction were read for the refresh. The first reconstruction is preserved as `adaptive-blind-reconstruction-v1.md`, retaining its original packet hash `0340E6CFBECAA1E58EE84BFA1D9B85F9FB299FB1A4E8B7C5FA22485F18784E3B`. This refresh does not claim a fresh actor, fresh initial blindness, or a pre-proof chronology. It records the terms' mathematical meaning, hypotheses, and boundaries without identifying an originating source, giving an approval verdict, or reporting an independent Lean compilation.

Revision scope: the current packet adds `history_length`, `history_injective`, and `historyLaw_apply_at_trace`. Their statements and displayed proof terms are decoded below. The statements and hypotheses of `finite_kernel_chain`, `adaptive_hellinger_le`, `traceLaw_apply`, `traceLaw_history_eq`, and `adaptive_hellinger_budget` retain the meanings reconstructed in the first pass. This refresh strengthens the trace/list bridge description and removes the earlier observation that no named history-length theorem was present. The probability convention, reset model, cost interpretation, zero cases, and all-terminal-trace budget requirement are unchanged.

## Objects and notation

Let I denote the finite type `ι`, equipped with decidable equality where the matrix and process definitions require it. States lie in the finite dimensional complex Euclidean space indexed by I. The matrix norm in the packet is the Euclidean L2 operator norm. Let K and D be natural numbers. An oracle environment A assigns a unitary matrix A_i to each arm i in `Fin K`.

A `QuantumQueryWord.Word I` is a finite list of instructions. A known instruction contains a unitary matrix and costs zero oracle queries. A forward instruction applies U and costs one query; an inverse instruction applies `star U`, the adjoint and hence inverse of a unitary U, and also costs one query. Thus the query count is the forward count plus the inverse count. Known gates count toward word length but do not count toward query cost. A word can have arbitrarily many known gates despite its query bound.

Evaluation applies the list in temporal order: `eval (g :: rest) U = eval rest U * g.eval U`, so the head gate acts first on a column state. In particular, concatenating words a and b has evaluation `eval b U * eval a U`. Every instruction and evaluated word is unitary when U is unitary.

A `ResetBlockProcess.Plan K D I` contains an arm a, a word w, and a proof that the word query count is at most D. One block uses the selected arm's same unitary at every forward occurrence and its adjoint at every inverse occurrence. A block does not mix several arm oracles within its word.

The policy is a total deterministic function

`policy : List I -> Plan K D I`.

It can choose both its next arm and its next word, including the known gates in that word, from the entire preceding list of outcomes. The same policy function and the same initial state are used in the two environments being compared.

For a history h, write a(h) for the selected arm, w(h) for the selected word, and c(h) for its query count. We have `0 <= c(h) <= D` for every list h, including histories of zero probability.

## Reset block probabilities and adaptivity

Fix a state psi satisfying `norm psi = 1`. The block output under environment A at history h is

`x_A(h) = eval(w(h), A_(a(h))) psi`.

The real kernel is

`k_A(h,j) = |x_A(h)_j|^2`.

It is the distribution of a measurement in the fixed coordinate basis. It is nonnegative for any psi, and it has sum one when psi is normalized, since word evaluation is unitary. The corresponding `blockPMF` assigns `ENNReal.ofReal(k_A(h,j))` to outcome j.

Every block starts from the same psi. The new history selects a new plan, but neither `kernel` nor `blockPMF` takes a postmeasurement quantum state from the preceding block. There is consequently a classical memory of measurement outcomes, with a reset quantum input at each block. This supports classical adaptation across blocks and coherent sequences of gates within each block. It does not describe a quantum state carried coherently across blocks, nor further measurements and feedback inside a single word.

The outcomes are not asserted to be independent or identically distributed. The kernel at the next step depends on the previous outcomes through the policy. At a fixed common history, however, the two environments use the same plan. That common-history comparison is what permits the one-block stability estimate to enter the adaptive argument.

The policy has no explicit random seed or stochastic action-selection kernel. Randomness comes from the block measurement kernels. Independently randomized policies would need an additional representation or extension. The formal arguments also assume a fixed oracle matrix for each arm; they do not describe an oracle that changes with time or history.

## Finite traces and their densities

`Trace I 0` is `PUnit`, with its sole empty trace. Recursively, `Trace I (n+1) = Trace I n x I`. An element therefore stores exactly n chronologically ordered measurement outcomes as nested pairs. Its finite type instance is built recursively. The function `history` converts it to a list by appending the newest outcome.

The added `history_length` explicitly proves `(history h).length = n` for every `h : Trace I n`. Its induction has the empty case and the append-singleton step. It needs no finite-type, decidable-equality, policy, oracle, normalization, or support hypothesis.

The added `history_injective n` proves that `history : Trace I n -> List I` is injective at each fixed horizon. Equal history lists imply equal traces. At the successor step, `history_length` gives equal prefix lengths; `List.append_inj` separates equality of the prefixes from equality of the final singleton lists. The induction hypothesis and singleton injectivity identify both pair components. This theorem also needs no finite-type or probabilistic assumptions. It excludes collisions when converting fixed-length traces to list histories, including traces with zero probability. It is not a separately stated surjectivity theorem onto all length-n lists, and it does not make the map onto all lists of arbitrary lengths.

For a trace z = (j_1,...,j_n), let h_t = [j_1,...,j_t] and h_0 = []. The density is

`p_A,n(z) = product_(t=0,...,n-1) k_A(h_t,j_(t+1))`.

The empty density is 1. The recursive definition is exactly previous density times the next kernel value. All densities are nonnegative without a normalization hypothesis. With `norm psi = 1`, the sum over all length-n traces is 1, using normalization of every kernel row. These are real point probabilities on a finite trace space, rather than densities against a separately introduced continuous measure.

The definitions of `kernel`, `density`, `weightedCost`, and `expectedCost` do not themselves take a proof that psi is normalized. Their probability-law interpretation and the relevant comparison theorems do require it. Unnormalized inputs remain syntactically available in those definitions but are not thereby probability distributions.

## Hellinger convention and exact finite kernel chain rule

The packet defines

`H2(p,q) = sum_x (sqrt(p(x)) - sqrt(q(x)))^2`.

There is no factor 1/2. For nonnegative normalized p and q this is

`H2(p,q) = 2 - 2 * sum_x sqrt(p(x))sqrt(q(x))`.

Thus it is twice the squared Hellinger convention that includes 1/2, and its range for probability laws is from 0 to 2. Any numerical comparison with that other convention must adjust the factor. The range statement follows mathematically from the displayed definitions; the packet does not contain a separately named range theorem. All square roots are Lean's real square root. Nonnegativity hypotheses are essential to the expansion used here; allowing arbitrary real arguments to the definition does not turn them into probability masses.

`hellingerSq_expand` says, for arbitrary nonnegative finite p and q,

`H2(p,q) = sum p + sum q - 2 * sum sqrt(p)sqrt(q)`.

The theorem `finite_kernel_chain` has finite types alpha and beta, nonnegative functions p,q on alpha, and nonnegative rows k(h,-),l(h,-) on beta whose sums are each exactly one for every h. Define joint masses

`P(h,j) = p(h)k(h,j)` and `Q(h,j) = q(h)l(h,j)`.

Its conclusion is the exact identity

`H2(P,Q) = H2(p,q) + sum_h sqrt(p(h))sqrt(q(h)) H2(k(h,-),l(h,-))`.

Importantly, this theorem does not assume that p and q themselves have total mass one. The normalization assumptions concern the conditional rows. It is valid for the finite nonnegative base masses supplied. Nor does it require positive p, positive q, a common support, or an absolute-continuity relation. If one base mass is zero at h, the conditional contribution at that history is zero. There are no divisions by history probabilities or likelihood ratios.

The proof expands each row, factors square roots of nonnegative products, and uses row sums one. It then sums over alpha. It does not invoke an independence assumption or a bound on the number of nonzero rows.

## Costs and the one-block bound

For an arm error profile eta, define the path cost

`W_eta(z) = sum_(t=0,...,n-1) c(h_t) * eta_(a(h_t))^2`.

This is precisely `weightedCost`. Its summands are nonnegative regardless of the signs of eta. It counts oracle calls weighted by squared arm error. It is not the squared total query count, not the number of blocks, not the number of gates, and not an expected cost until it is averaged with a law.

`expectedCost policy A psi eta n` is

`C_A,eta(n) = sum_z p_A,n(z) W_eta(z)`.

The same path-cost function is averaged under two possibly different transcript laws. `expectedCost_succ` proves that the increment is

`sum_(h in Trace I n) p_A,n(h) c(history(h)) eta_(a(history(h)))^2`.

Here a trace in the summation is the prefix at the start of the next block. Normalization of the next kernel removes the final outcome from the incremental expectation.

The query-word terms first give an operator difference bound of c times the oracle difference, then a state difference bound using the common unit input. The basis measurement Hellinger quantity is at most the squared state difference. For a selected arm satisfying

`norm(E_i - F_i) <= eta_i`,

the one-block bound is at most `c(h)^2 eta_(a(h))^2`. Since `c(h) <= D`, `kernel_hellinger_le` gives

`H2(k_E(h,-),k_F(h,-)) <= D * c(h) * eta_(a(h))^2`.

All compared oracle matrices are unitary by their types. Known gates are the same at a common history and contribute no error in the word telescoping argument. There is no extra positivity condition on eta in the theorem signature. The oracle-distance hypothesis implies `eta_i >= 0` for each arm, since a norm is nonnegative. The cost definitions and the later arithmetic use squares.

## Adaptive expected-cost theorem

The complete hypothesis set of `adaptive_hellinger_le` is: a finite outcome type with decidable equality; natural K,D; a total policy into bounded plans; two environments E,F of unitary arm matrices; the common state psi with norm one; a real error profile eta; the bound `norm(E_i-F_i) <= eta_i` for every arm; and a natural fixed horizon n.

Its conclusion is

`H2(p_E,n,p_F,n) <= (D/2) * (C_E,eta(n) + C_F,eta(n))`.

Equivalently the right side is D times the average of the two expected weighted costs. It is not a bound in terms of just one environment's expected cost. No equality between those two expectations is assumed.

At the induction step, the exact kernel chain rule adds a conditional term weighted by `sqrt(p_E,n(h))sqrt(p_F,n(h))`. The one-block bound controls that conditional Hellinger term. The arithmetic inequality

`2 sqrt(p_E,n(h))sqrt(p_F,n(h)) <= p_E,n(h) + p_F,n(h)`

replaces the geometric overlap weight by the arithmetic mean. The cost increment identity in each environment then closes induction. Thus the factor 1/2 on the right comes from this arithmetic-mean step; it is not a hidden factor in the definition of `H2`.

The proof permits arbitrary history dependence of the shared policy and includes histories that have mass under only one environment. A zero mass causes the appropriate summands to vanish. There is no required lower bound on outcome probabilities and no common-support assumption.

## PMF bridge and relation to list histories

`traceLaw` is a genuine PMF on `Trace I n`. It starts as the point mass on the sole empty trace. At each step it binds the preceding trace law, samples the selected block PMF, and maps outcome j to the pair (preceding trace,j).

`map_pair_apply` states that mapping a PMF by `j -> (a,j)` gives mass p(h.second) when h.first = a and zero otherwise. This makes only the matching predecessor contribute in the point-mass computation.

`traceLaw_apply` proves for every trace z, including zero-probability traces,

`traceLaw(A,n)(z) = ENNReal.ofReal(p_A,n(z))`.

`traceLaw_toReal` then proves

`(traceLaw(A,n)(z)).toReal = p_A,n(z)`.

This conversion is exact because the real density is nonnegative and `ofReal` produces the finite mass represented by it. It is not an approximation or an unproved identification of two different distributions.

`traceLaw_history_eq` proves equality of PMFs after applying the trace-to-list map:

`traceLaw(A,n).map history = ResetBlockProcess.historyLaw(A,n)`.

The right-hand process starts from [] and appends a sampled outcome at each step under the same policy and reset block distribution. The theorem therefore connects the finite trace representation to the list-history process. It is equality of these laws, not an assertion that all lists have positive probability.

The added `historyLaw_apply_at_trace` gives the pointwise list-history bridge. Under the same finite-type and decidable-equality instances, total policy, unitary environment, and normalized input, for every natural n and every `z : Trace I n` it states

`ResetBlockProcess.historyLaw(A,n)(history(z)) = ENNReal.ofReal(p_A,n(z))`.

It imposes no support or positive-mass condition on z. Its displayed proof rewrites the list law using `traceLaw_history_eq`, expands the mapped PMF as a sum over finite traces, and uses `history_injective n` to leave only the unique matching trace z. `traceLaw_apply` then identifies that trace's mass with `ofReal` of its density. Thus conversion to a list does not merge masses from different traces at this fixed horizon. This is a direct pointwise equality in addition to the pushforward equality. Taking `.toReal` would also give the density using nonnegativity, but that extra list-mass conversion is an immediate derivation rather than a separately named theorem here.

The supplied final Hellinger statement remains formulated on finite traces. The three additions do not state a Hellinger invariance theorem, a general data-processing theorem, or a separate Hellinger bound over the full list type. They also do not weaken the terminal budget premise to a support-only premise. They supply exact length, injectivity, and pointwise probability bridges between the existing representations.

## Uniform error and the pathwise budget corollary

`historyQueryCost policy h` sums the query count of the plan at each prefix `h.take t`, for `0 <= t < h.length`. The appended-outcome lemma proves that appending j adds exactly the cost of the plan chosen from the preceding h.

For a constant error eta, `weightedCost_uniform` proves

`W_eta(z) = historyQueryCost(policy,history(z)) * eta^2`.

`expectedCost_le` states that if `W_eta(z) <= B` for every length-n trace, then `C_A,eta(n) <= B`. It allows any real B in the signature; the all-trace bound and normalization supply what is needed.

`adaptive_hellinger_budget` takes a real scalar eta, the uniform arm distance assumption `norm(E_i-F_i) <= eta` for every arm, natural n,T, and the hypothesis

`for every z : Trace I n, historyQueryCost(policy,history(z)) <= T`.

Its conclusion is

`H2(traceLaw(E,n).toReal, traceLaw(F,n).toReal) <= D * T * eta^2`.

The displayed `.toReal` denotes pointwise conversion of the PMF's masses, precisely as in its Lean statement. The proof bounds each environment's weighted expectation by `T eta^2` and applies the adaptive expected-cost theorem. The two equal upper bounds cancel the factor 1/2.

The budget assumption quantifies over every length-n trace, not only the support under E, not only the support under F, and not merely paths common to both. It includes hypothetical histories of zero probability under both environments. It is a condition at the chosen terminal horizon. It does not require this total budget at every longer horizon or at every list length. Since path costs are nonnegative, a terminal budget also bounds its prefixes when they can be extended to terminal traces; under a normalized state the outcome type is inhabited, so finite prefixes do have such extensions. This inference does not weaken the theorem's explicit all-terminal-trace premise.

The ambient `historyLaw_length_support` says only that supported list histories have length n. Its `historyLaw_queryCost_le` and `historyLaw_queryCost_le_budget` bound costs on that support using `n*D` (and `n*D <= T`, respectively). Those support statements have different quantifiers from the all-trace hypothesis of the adaptive budget theorem. One must not substitute a support-only bound for the stated hypothesis without a further argument or a different theorem. The expected-cost argument could mathematically be adapted to bounds on the relevant supports, but that weakening is not the supplied statement.

A sufficient direct all-trace condition is `n*D <= T`: `history_length` now explicitly supplies the length n of every trace history, and `historyQueryCost_le` bounds its cost by `n*D` from the per-block cap. T may also be smaller if the policy's sum of costs is bounded more tightly along every terminal trace. The theorem does not require `T = n*D`, and n is a block horizon rather than a query budget. There is no stopping-time result or variable-length transcript law in these statements.

## Zero cases and absent explicit positivity hypotheses

- **K = 0.** An arm would have to inhabit `Fin 0`. No plan exists, and a total policy cannot exist because `List I` contains []. The theorem signatures do not explicitly require `K > 0`, but their policy argument prevents a concrete instance with K = 0. This remains so at n = 0: the zero-step laws do not evaluate a plan, yet the signatures still demand a policy. Empty oracle families alone do not make the process instantiable.
- **D = 0.** Every plan's query count is zero. Its word can contain known gates but cannot contain forward or inverse calls. Kernels are therefore independent of the oracle environment at every common history, although the policy may still adapt its known gates to outcomes. The transcript laws in the two environments coincide, weighted costs vanish, and the Hellinger upper bounds are zero. A zero query cap does not prohibit blocks or known gates.
- **n = 0.** There is one trace, its density is 1 in both environments, its weighted cost is 0, and its law is a point mass. Both expected costs and Hellinger discrepancy are 0. `historyQueryCost [] = 0`; the terminal budget premise holds for any natural T, including 0, provided the other required data exist.
- **T = 0.** The budget theorem still applies. Its premise forces the complete horizon-n path cost to be zero on every terminal trace. The conclusion is zero Hellinger discrepancy. This does not assert that all policy words at histories beyond that horizon are query-free.
- **eta = 0.** The uniform norm bound forces the two arm matrices to agree arm by arm, so the laws agree and the upper bound is zero. For an arm profile, a zero eta component similarly forces equality for that arm; the cost weighting retains the nonzero error components.
- **Empty I.** The raw finite type declarations allow it, but a complex Euclidean state on an empty coordinate type has norm zero. No psi with norm one exists, so the normalized-law theorem hypotheses exclude this case. No separate nonempty assumption is printed.

## What the terms establish and what they leave open

The terms establish a finite-horizon stability bound for full measurement-outcome transcripts of deterministic, history-adaptive reset-block protocols, comparing two fixed unitary oracle families under the same policy, coordinate basis, and normalized pure input. They retain arm-dependent errors in the expected-cost theorem and specialize to a uniform error and an all-trace total query budget in the final corollary.

They do not state a regret bound, a sample-complexity lower bound, or a bandit/RL reward or transition model. There are no mixed input states, noisy nonunitary channels, general POVM kernels, coherently retained inter-block memories, changing oracle environments, oracle-dependent differing policies, or arbitrary stopping times in the process definition. Known unitaries can supply basis rotations within a word, but this is not a separately formalized general measurement model.

The transcript records measurement outcomes. Arm choices and words are deterministic functions of the prefixes, so they can be reconstructed from those outcomes and the fixed policy. The packet does not explicitly introduce a separate transcript type recording actions, a postprocessed output law, or a data-processing theorem for Hellinger discrepancy. Such additional claims require additional formal statements or derivations.

The matrix difference is measured in operator norm; the comparison is not phase-invariant at the hypothesis level. In particular, an error bound between raw unitary matrices may be conservative even when their measurement behavior agrees. The supplied estimate is an upper bound and is not asserted to be sharp. It can exceed the intrinsic probability-law maximum 2, since no clipping by that maximum is included.

Finally, the reset mechanism is encoded by always applying the new word to psi. The packet gives no resource accounting for physical state preparation, resetting, measurement, known gates, or elapsed time. D and T count only the specified forward and inverse oracle instructions. The reconstruction describes the supplied statements; it does not infer publication readiness, source identity, or successful compilation from their presence.

## Exact artifact bindings

```json
{
  "adaptive-information-source.md": "0e06332befd03e2e0fab0d4c1cb22ac226eb690cdc025d3f88426f155cbd5624",
  "adaptive-information-clarifications.md": "4950f4078776899572e2befe1835a475783b27d135a7e92c1769aa5dcbf96ee9",
  "adaptive-information-signatures.txt": "609141dc8302cbf3f8507ad9f4dd0b8b3c3c4e7696be4ef1378d8a22a75e555d",
  "adaptive-pmf-bridge-signatures.txt": "ce886c59d30972342287c03987847f7308ced6251ae9b22952e9612494241181",
  "adaptive-budget-signatures.txt": "f1ee78c230ffca27bf10d0be14875086380b6c8c9e1855b417cf77aab7ac449e",
  "adaptive-formal-packet.md": "db2f1189d0132bfb6467caec516409482d9b0011f7b4847591d1bc073c91a935",
  "adaptive-blind-reconstruction.md": "054dd496a94bec0792eb4f5e8ec02e85a330697e196bb28f757c564fd0ae5680"
}
```
