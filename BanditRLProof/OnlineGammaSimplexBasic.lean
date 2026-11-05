import Mathlib

open Finset Set
open scoped BigOperators
namespace BanditRL.OnlineGamma
noncomputable section

def simplexLogFactor (x : ℝ) : ℝ := x * Real.log x - Real.log (Real.Gamma (x + 1/2))

def simplexGammaProduct (n : ℕ) (x : Fin n → ℝ) : ℝ :=
  ∏ i, (x i) ^ (x i) / Real.Gamma (x i + 1/2)

def nonnegativeMassSimplex (n : ℕ) (T : ℝ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = T}

def massSimplexVertex {n : ℕ} (T : ℝ) (j : Fin n) : Fin n → ℝ := Pi.single j T

theorem continuousOn_simplexLogFactor_and_zero :
  ContinuousOn simplexLogFactor (Ici (0 : ℝ)) ∧ simplexLogFactor 0 = -Real.log (Real.Gamma (1/2)) := by
  constructor
  · intro x hx
    have hp : 0 < x + 1/2 := by have := hx.out; linarith
    have hg := (Real.differentiableAt_Gamma (s := x + 1/2) (fun n => by
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith)).continuousAt
    have hs : ContinuousAt (fun y : ℝ => y + 1/2) x :=
      continuousAt_id.add continuousAt_const
    have hgs : ContinuousAt (fun y : ℝ => Real.Gamma (y + 1/2)) x := ContinuousAt.comp (f := fun y : ℝ => y + 1/2) (x := x) hg hs
    have hls : ContinuousAt (fun y : ℝ => Real.log (Real.Gamma (y + 1/2))) x :=
      ContinuousAt.comp (f := fun y : ℝ => Real.Gamma (y + 1/2)) (x := x) (Real.continuousAt_log (Real.Gamma_pos_of_pos hp).ne') hgs
    exact (Real.continuous_mul_log.continuousAt.sub hls).continuousWithinAt
  · simp [simplexLogFactor]

theorem simplexGammaProduct_pos_and_log :
  ∀ (n : ℕ) (x : Fin n → ℝ), (∀ i, 0 ≤ x i) →
    0 < simplexGammaProduct n x ∧ Real.log (simplexGammaProduct n x) = ∑ i, simplexLogFactor (x i) := by
  intro n x hx
  have hg (i : Fin n) : 0 < Real.Gamma (x i + 1/2) :=
    Real.Gamma_pos_of_pos (by have := hx i; linarith)
  have hp (i : Fin n) : 0 < (x i) ^ (x i) := by
    rcases (hx i).eq_or_lt with h | h
    · simp [← h]
    · exact Real.rpow_pos_of_pos h _
  have hq (i : Fin n) : 0 < (x i) ^ (x i) / Real.Gamma (x i + 1/2) :=
    div_pos (hp i) (hg i)
  constructor
  · exact Finset.prod_pos (fun i _ => hq i)
  · unfold simplexGammaProduct
    rw [Real.log_prod (fun i _ => (hq i).ne')]
    apply Finset.sum_congr rfl
    intro i _
    rw [Real.log_div (hp i).ne' (hg i).ne']
    unfold simplexLogFactor
    rcases (hx i).eq_or_lt with h | h
    · simp [← h]
    · rw [Real.log_rpow h]

theorem convexOn_le_sum_massSimplexVertex :
  ∀ (n : ℕ) (T : ℝ), 1 ≤ n → 1 ≤ T →
    ∀ (G : (Fin n → ℝ) → ℝ), ConvexOn ℝ (nonnegativeMassSimplex n T) G →
      ∀ x ∈ nonnegativeMassSimplex n T, G x ≤ ∑ j, (x j / T) * G (massSimplexVertex T j) := by
  intro n T _hn hT G hG x hx
  obtain ⟨hxpos, hmass⟩ := hx
  have ht : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hver (j : Fin n) : massSimplexVertex T j ∈ nonnegativeMassSimplex n T := by
    constructor
    · intro i
      simp only [massSimplexVertex, Pi.single_apply]
      split <;> positivity
    · simp [massSimplexVertex, Pi.single_apply]
  have hweights : ∑ j, x j / T = 1 := by rw [← Finset.sum_div, hmass, div_self ht.ne']
  have hdecomp : ∑ j, (x j / T) • massSimplexVertex T j = x := by
    funext i
    simp [Finset.sum_apply, Pi.smul_apply, massSimplexVertex, Pi.single_apply,
      smul_eq_mul, mul_ite, div_mul_cancel₀ _ ht.ne']
  have h := hG.map_sum_le (t := Finset.univ) (w := fun j => x j / T)
    (p := fun j => massSimplexVertex T j) (fun j _ => div_nonneg (hxpos j) ht.le)
    hweights (fun j _ => hver j)
  simpa only [hdecomp, smul_eq_mul] using h

end
end BanditRL.OnlineGamma
