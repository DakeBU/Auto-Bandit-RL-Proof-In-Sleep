import BanditRLProof.OFULGaussianMixture

/-!
# Spectral Gaussian mixture identity for OFUL

This module transports the compiled independent-coordinate Gaussian
quadratic-exponential identity through the orthonormal eigenbasis of a real
positive-semidefinite matrix. It then collects the spectral product and
coordinate quadratic form as `det (1 + A)` and `(1 + A)⁻¹`.
-/

namespace BanditRLProof.OFUL

open MeasureTheory ProbabilityTheory Real Matrix WithLp
open scoped ENNReal NNReal ProbabilityTheory InnerProductSpace

variable {Feature : Type*} [Fintype Feature] [DecidableEq Feature]

omit [DecidableEq Feature] in
private theorem inner_sum_smul_orthonormalBasis
    (b : OrthonormalBasis Feature Real (EuclideanSpace Real Feature))
    (x : Feature -> Real) (i : Feature) :
    ⟪b i, ∑ j, x j • b j⟫_ℝ = x i := by
  rw [b.sum_repr_symm, ← b.repr_apply_apply]
  simp

omit [DecidableEq Feature] in
private theorem inner_sum_smul_orthonormalBasis_left
    (b : OrthonormalBasis Feature Real (EuclideanSpace Real Feature))
    (score : EuclideanSpace Real Feature) (x : Feature -> Real) :
    ⟪score, ∑ i, x i • b i⟫_ℝ =
      ∑ i, ⟪score, b i⟫_ℝ * x i := by
  rw [inner_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [real_inner_smul_right]
  ring

private theorem inner_toEuclideanCLM_sum_eigenvectorBasis
    (A : Matrix Feature Feature Real) (hA : A.PosSemidef)
    (x : Feature -> Real) :
    let b := hA.isHermitian.eigenvectorBasis
    let v : EuclideanSpace Real Feature := ∑ i, x i • b i
    ⟪v, Matrix.toEuclideanCLM (𝕜 := Real) A v⟫_ℝ =
      ∑ i, hA.isHermitian.eigenvalues i * x i ^ 2 := by
  dsimp only
  let b := hA.isHermitian.eigenvectorBasis
  let v : EuclideanSpace Real Feature := ∑ i, x i • b i
  have hsumcoord (y : Feature → Real) (i : Feature) :
      ⟪b i, ∑ j, y j • b j⟫_ℝ = y i := by
    calc
      ⟪b i, ∑ j, y j • b j⟫_ℝ =
          b.repr (∑ j, y j • b j) i :=
        (b.repr_apply_apply (∑ j, y j • b j) i).symm
      _ = y i := by
        rw [b.sum_repr_symm]
        simp
  have hcoord (i : Feature) : ⟪b i, v⟫_ℝ = x i := by
    exact hsumcoord x i
  have heigen (i : Feature) :
      Matrix.toEuclideanCLM (𝕜 := Real) A (b i) =
        hA.isHermitian.eigenvalues i • b i := by
    apply WithLp.ofLp_injective
    simpa only [Matrix.ofLp_toEuclideanCLM, WithLp.ofLp_smul] using
      hA.isHermitian.mulVec_eigenvectorBasis i
  have hAv :
      Matrix.toEuclideanCLM (𝕜 := Real) A v =
        ∑ i, (hA.isHermitian.eigenvalues i * x i) • b i := by
    dsimp [v]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [map_smul, heigen]
    simp only [smul_smul]
    ring_nf
  have hcoordLeft (i : Feature) : ⟪v, b i⟫_ℝ = x i := by
    rw [real_inner_comm, hcoord]
  have hcoordA :
      ∀ i : Feature,
        ⟪b i, Matrix.toEuclideanCLM (𝕜 := Real) A v⟫_ℝ =
          hA.isHermitian.eigenvalues i * x i := by
    intro i
    rw [hAv]
    exact hsumcoord (fun j => hA.isHermitian.eigenvalues j * x j) i
  change
    ⟪v, Matrix.toEuclideanCLM (𝕜 := Real) A v⟫_ℝ =
      ∑ i, hA.isHermitian.eigenvalues i * x i ^ 2
  calc
    ⟪v, Matrix.toEuclideanCLM (𝕜 := Real) A v⟫_ℝ =
        ∑ i, ⟪v, b i⟫_ℝ *
          ⟪b i, Matrix.toEuclideanCLM (𝕜 := Real) A v⟫_ℝ :=
      (OrthonormalBasis.sum_inner_mul_inner b v
        (Matrix.toEuclideanCLM (𝕜 := Real) A v)).symm
    _ = ∑ i, hA.isHermitian.eigenvalues i * x i ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hcoordLeft, hcoordA]
      ring

/--
The standard-Gaussian quadratic-exponential integral in the orthonormal
eigenbasis of a positive-semidefinite matrix.

This is the explicit spectral-coordinate transport bridge from the diagonal
product identity. The following lemmas collect its right-hand side into
matrix determinant and inverse-quadratic notation.
-/
theorem integral_exp_inner_sub_quadratic_stdGaussian_eigenvalues
    (A : Matrix Feature Feature Real) (hA : A.PosSemidef)
    (score : EuclideanSpace Real Feature) :
    integral
        (ProbabilityTheory.stdGaussian
          (EuclideanSpace Real Feature))
        (fun z : EuclideanSpace Real Feature =>
          Real.exp
            (⟪score, z⟫_ℝ -
              ⟪z, Matrix.toEuclideanCLM (𝕜 := Real) A z⟫_ℝ / 2)) =
      (Finset.univ.prod (fun i =>
        Real.sqrt (1 + hA.isHermitian.eigenvalues i)))⁻¹ *
        Real.exp
          (Finset.univ.sum (fun i =>
            ⟪score, hA.isHermitian.eigenvectorBasis i⟫_ℝ ^ 2 /
              (2 * (1 + hA.isHermitian.eigenvalues i)))) := by
  let b := hA.isHermitian.eigenvectorBasis
  have hgauss :
      ProbabilityTheory.stdGaussian (EuclideanSpace Real Feature) =
        (Measure.pi (fun _ : Feature =>
          ProbabilityTheory.gaussianReal 0 1)).map
            (fun x : Feature → Real => ∑ i, x i • b i) :=
    ProbabilityTheory.stdGaussian_eq_map_pi_orthonormalBasis b
  rw [hgauss]
  rw [MeasureTheory.integral_map]
  · have hpoint :
        (fun x : Feature → Real =>
          Real.exp
            (⟪score, ∑ i, x i • b i⟫_ℝ -
              ⟪∑ i, x i • b i,
                Matrix.toEuclideanCLM (𝕜 := Real) A
                  (∑ i, x i • b i)⟫_ℝ / 2)) =
          (fun x : Feature → Real =>
            Real.exp
              (Finset.univ.sum (fun i =>
                ⟪score, b i⟫_ℝ * x i -
                  hA.isHermitian.eigenvalues i * (x i) ^ 2 / 2))) := by
        funext x
        congr 1
        calc
          ⟪score, ∑ i, x i • b i⟫_ℝ -
                ⟪∑ i, x i • b i,
                  Matrix.toEuclideanCLM (𝕜 := Real) A
                    (∑ i, x i • b i)⟫_ℝ / 2 =
              (∑ i, ⟪score, b i⟫_ℝ * x i) -
                (∑ i, hA.isHermitian.eigenvalues i * x i ^ 2) / 2 :=
            congrArg₂ (fun linear quadratic => linear - quadratic / 2)
              (inner_sum_smul_orthonormalBasis_left b score x)
              (inner_toEuclideanCLM_sum_eigenvectorBasis A hA x)
          _ = Finset.univ.sum (fun i =>
                ⟪score, b i⟫_ℝ * x i -
                  hA.isHermitian.eigenvalues i * (x i) ^ 2 / 2) := by
            rw [Finset.sum_sub_distrib, Finset.sum_div]
    rw [hpoint]
    exact
      integral_exp_sum_linear_sub_diagonal_quadratic_pi_gaussianReal_eq
        (fun i => ⟪score, b i⟫_ℝ)
        hA.isHermitian.eigenvalues
        hA.eigenvalues_nonneg
  · exact (by fun_prop :
      Measurable (fun x : Feature → Real => ∑ i, x i • b i)).aemeasurable
  · fun_prop

/--
The determinant of `1 + A` is the product of one plus the eigenvalues of a
real positive-semidefinite matrix.
-/
theorem det_one_add_posSemidef_eq_prod_eigenvalues
    (A : Matrix Feature Feature Real) (hA : A.PosSemidef) :
    Matrix.det (1 + A) =
      Finset.univ.prod (fun i =>
        1 + hA.isHermitian.eigenvalues i) := by
  let eigenvalues := hA.isHermitian.eigenvalues
  let U := hA.isHermitian.eigenvectorUnitary
  change Matrix.det (1 + A) =
    Finset.univ.prod (fun i => 1 + eigenvalues i)
  have hspec :
      A = Unitary.conjStarAlgAut Real (Matrix Feature Feature Real) U
        (Matrix.diagonal eigenvalues) := by
    exact hA.isHermitian.spectral_theorem
  calc
    Matrix.det (1 + A) =
        Matrix.det
          (1 + Unitary.conjStarAlgAut Real
            (Matrix Feature Feature Real) U
            (Matrix.diagonal eigenvalues)) := by rw [hspec]
    _ = Matrix.det
          (Unitary.conjStarAlgAut Real
            (Matrix Feature Feature Real) U
            (1 + Matrix.diagonal eigenvalues)) := by
      rw [map_add, map_one]
    _ = Finset.univ.prod (fun i => 1 + eigenvalues i) := by
      rw [Unitary.conjStarAlgAut_apply, Matrix.det_mul,
        Matrix.det_mul]
      have hone_diag :
          1 + Matrix.diagonal eigenvalues =
            Matrix.diagonal (fun i => 1 + eigenvalues i) := by
        ext i j
        by_cases hij : i = j
        · subst j
          simp
        · simp [hij]
      rw [hone_diag, Matrix.det_diagonal]
      have hdetU :
          Matrix.det (U : Matrix Feature Feature Real) *
              Matrix.det (star (U : Matrix Feature Feature Real)) =
            1 := by
        rw [← Matrix.det_mul]
        have hunit :
            (U : Matrix Feature Feature Real) *
                star (U : Matrix Feature Feature Real) =
              1 :=
          Unitary.coe_mul_star_self U
        rw [hunit, Matrix.det_one]
      calc
        Matrix.det (U : Matrix Feature Feature Real) *
              (∏ i, (1 + eigenvalues i)) *
              Matrix.det (star (U : Matrix Feature Feature Real)) =
            (∏ i, (1 + eigenvalues i)) *
              (Matrix.det (U : Matrix Feature Feature Real) *
                Matrix.det (star (U : Matrix Feature Feature Real))) := by
          ring
        _ = ∏ i, (1 + eigenvalues i) := by
          rw [hdetU, mul_one]

private theorem toEuclideanCLM_one_add_posSemidef_inv_eigenvectorBasis
    (A : Matrix Feature Feature Real) (hA : A.PosSemidef)
    (i : Feature) :
    Matrix.toEuclideanCLM (𝕜 := Real) (1 + A)⁻¹
        (hA.isHermitian.eigenvectorBasis i) =
      (1 + hA.isHermitian.eigenvalues i)⁻¹ •
        hA.isHermitian.eigenvectorBasis i := by
  let b := hA.isHermitian.eigenvectorBasis
  let eigenvalue : Real := 1 + hA.isHermitian.eigenvalues i
  have heigenvalue_pos : 0 < eigenvalue := by
    dsimp [eigenvalue]
    linarith [hA.eigenvalues_nonneg i]
  have hBpos : (1 + A).PosDef :=
    Matrix.PosDef.one.add_posSemidef hA
  have hBaction :
      (1 + A).mulVec (b i) = eigenvalue • b i := by
    dsimp [b, eigenvalue]
    rw [Matrix.add_mulVec, Matrix.one_mulVec,
      hA.isHermitian.mulVec_eigenvectorBasis]
    ext j
    simp [Pi.add_apply, Pi.smul_apply]
    ring
  have hb :
      (b i : Feature → Real) =
        eigenvalue⁻¹ • (1 + A).mulVec (b i) := by
    rw [hBaction, smul_smul]
    field_simp
    simp
  apply WithLp.ofLp_injective
  simpa only [Matrix.ofLp_toEuclideanCLM, WithLp.ofLp_smul] using
    (show
      (1 + A)⁻¹ *ᵥ (b i : Feature → Real) =
        eigenvalue⁻¹ • (b i : Feature → Real) by
      calc
        (1 + A)⁻¹ *ᵥ (b i : Feature → Real) =
            (1 + A)⁻¹ *ᵥ
              (eigenvalue⁻¹ • (1 + A).mulVec (b i)) := by
          rw [← hb]
        _ = eigenvalue⁻¹ •
              ((1 + A)⁻¹ *ᵥ ((1 + A).mulVec (b i))) := by
          rw [Matrix.mulVec_smul]
        _ = eigenvalue⁻¹ •
              (((1 + A)⁻¹ * (1 + A)).mulVec (b i)) := by
          rw [Matrix.mulVec_mulVec]
        _ = eigenvalue⁻¹ • (b i : Feature → Real) := by
          rw [Matrix.nonsing_inv_mul (1 + A)
              ((1 + A).isUnit_iff_isUnit_det.mp hBpos.isUnit),
            Matrix.one_mulVec])

/--
The inverse quadratic form of `1 + A` equals its spectral-coordinate sum.
-/
theorem dotProduct_one_add_posSemidef_inv_mulVec_eq_sum_eigenvalues
    (A : Matrix Feature Feature Real) (hA : A.PosSemidef)
    (score : EuclideanSpace Real Feature) :
    score ⬝ᵥ (1 + A)⁻¹.mulVec score =
      Finset.univ.sum (fun i =>
        ⟪score, hA.isHermitian.eigenvectorBasis i⟫_ℝ ^ 2 /
          (1 + hA.isHermitian.eigenvalues i)) := by
  let b := hA.isHermitian.eigenvectorBasis
  let coefficient : Feature → Real :=
    fun i => ⟪score, b i⟫_ℝ
  let inverseEigenvalue : Feature → Real :=
    fun i => (1 + hA.isHermitian.eigenvalues i)⁻¹
  have hscore :
      score = ∑ i, coefficient i • b i := by
    calc
      score = ∑ i, ⟪b i, score⟫_ℝ • b i :=
        (b.sum_repr' score).symm
      _ = ∑ i, coefficient i • b i := by
        apply Finset.sum_congr rfl
        intro i hi
        congr 1
        dsimp [coefficient]
        rw [real_inner_comm]
  have hinvScore :
      Matrix.toEuclideanCLM (𝕜 := Real) (1 + A)⁻¹ score =
        ∑ i, (coefficient i * inverseEigenvalue i) • b i := by
    rw [hscore, map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [map_smul,
      toEuclideanCLM_one_add_posSemidef_inv_eigenvectorBasis A hA i]
    simp only [smul_smul]
    dsimp [inverseEigenvalue]
  have hcoordInv (i : Feature) :
      ⟪b i,
        Matrix.toEuclideanCLM (𝕜 := Real) (1 + A)⁻¹ score⟫_ℝ =
          coefficient i * inverseEigenvalue i := by
    rw [hinvScore]
    exact inner_sum_smul_orthonormalBasis b
      (fun j => coefficient j * inverseEigenvalue j) i
  rw [← Matrix.inner_toEuclideanCLM]
  calc
    ⟪score,
        Matrix.toEuclideanCLM (𝕜 := Real) (1 + A)⁻¹ score⟫_ℝ =
      ∑ i, ⟪score, b i⟫_ℝ *
        ⟪b i,
          Matrix.toEuclideanCLM (𝕜 := Real) (1 + A)⁻¹ score⟫_ℝ :=
      (OrthonormalBasis.sum_inner_mul_inner b score
        (Matrix.toEuclideanCLM (𝕜 := Real) (1 + A)⁻¹ score)).symm
    _ = Finset.univ.sum (fun i =>
        ⟪score, hA.isHermitian.eigenvectorBasis i⟫_ℝ ^ 2 /
          (1 + hA.isHermitian.eigenvalues i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hcoordInv]
      dsimp [b, coefficient, inverseEigenvalue]
      ring

/--
Exact standard-Gaussian quadratic-exponential identity for an arbitrary real
positive-semidefinite matrix.

This closes the orthonormal spectral transport from the diagonal-coordinate
Gaussian mixture leaf. Transport from a nonstandard initial covariance and
the stochastic Tonelli/Markov assembly remain separate obligations.
-/
theorem integral_exp_inner_sub_quadratic_stdGaussian_det
    (A : Matrix Feature Feature Real) (hA : A.PosSemidef)
    (score : EuclideanSpace Real Feature) :
    integral
        (ProbabilityTheory.stdGaussian
          (EuclideanSpace Real Feature))
        (fun z : EuclideanSpace Real Feature =>
          Real.exp
            (⟪score, z⟫_ℝ -
              ⟪z, Matrix.toEuclideanCLM (𝕜 := Real) A z⟫_ℝ / 2)) =
      (Real.sqrt (Matrix.det (1 + A)))⁻¹ *
        Real.exp
          (score ⬝ᵥ (1 + A)⁻¹.mulVec score / 2) := by
  rw [integral_exp_inner_sub_quadratic_stdGaussian_eigenvalues
    A hA score]
  have heigenvalue_nonneg :
      ∀ i : Feature, 0 ≤ 1 + hA.isHermitian.eigenvalues i := by
    intro i
    linarith [hA.eigenvalues_nonneg i]
  have heigenvalue_ne :
      ∀ i : Feature, 1 + hA.isHermitian.eigenvalues i ≠ 0 := by
    intro i
    exact ne_of_gt (by linarith [hA.eigenvalues_nonneg i])
  have hsqrtDet :
      Real.sqrt (Matrix.det (1 + A)) =
        Finset.univ.prod (fun i =>
          Real.sqrt (1 + hA.isHermitian.eigenvalues i)) := by
    rw [det_one_add_posSemidef_eq_prod_eigenvalues A hA]
    exact Real.sqrt_prod Finset.univ
      (fun i hi => heigenvalue_nonneg i)
  have hquadratic :=
    dotProduct_one_add_posSemidef_inv_mulVec_eq_sum_eigenvalues
      A hA score
  have hsum :
      Finset.univ.sum (fun i =>
          ⟪score, hA.isHermitian.eigenvectorBasis i⟫_ℝ ^ 2 /
            (2 * (1 + hA.isHermitian.eigenvalues i))) =
        Finset.univ.sum (fun i =>
          ⟪score, hA.isHermitian.eigenvectorBasis i⟫_ℝ ^ 2 /
            (1 + hA.isHermitian.eigenvalues i)) / 2 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    field_simp [heigenvalue_ne i]
  rw [hsqrtDet, hquadratic, hsum]

end BanditRLProof.OFUL
