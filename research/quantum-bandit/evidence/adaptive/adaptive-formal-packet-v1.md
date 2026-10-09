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
