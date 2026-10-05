import BanditRLProof

noncomputable section
open Set BanditRL.OnlineConvex
namespace Tests.OnlineConvexClosures

def shift : ℝ →ᵃ[ℝ] ℝ := AffineMap.id ℝ ℝ + AffineMap.const ℝ ℝ 1

theorem shifted_indicator_convex :
    IsConvexExtended (fun x => extendedIndicator (Ici (0 : ℝ)) (shift x)) :=
  convex_comp_affine _ ((convex_indicator_iff _).mpr (convex_Ici 0)) shift

theorem shifted_values :
    extendedIndicator (Ici (0 : ℝ)) (shift (-2)) = ⊤ ∧
    extendedIndicator (Ici (0 : ℝ)) (shift 0) = 0 := by
  norm_num [extendedIndicator, shift]

example : IsConvexExtended (fun x : ℝ => ((‖AffineMap.const ℝ ℝ (2 : ℝ) x‖ : ℝ) : EReal)) :=
  convex_comp_affine _ (example_2_6 (E := ℝ)) (AffineMap.const ℝ ℝ 2)

def family (i : Bool) : ℝ → EReal := if i then extendedIndicator (Ici 0) else extendedIndicator (Iic 2)

theorem family_convex : ∀ i, IsConvexExtended (family i) := by
  intro i
  cases i <;> simp only [family, Bool.false_eq_true, ↓reduceIte]
  · exact (convex_indicator_iff _).mpr (convex_Iic 2)
  · exact (convex_indicator_iff _).mpr (convex_Ici 0)

theorem supremum_convex : IsConvexExtended (fun x => ⨆ i, family i x) :=
  convex_iSup family family_convex

theorem supremum_values : (⨆ i, family i (1 : ℝ)) = 0 ∧
    (⨆ i, family i (3 : ℝ)) = ⊤ := by
  norm_num [family, iSup_bool_eq, extendedIndicator]

example : IsConvexExtended (fun x : ℝ => ⨆ i : Empty, (fun _ : Empty => (0 : EReal)) i) :=
  convex_iSup _ (fun i => nomatch i)

def outer (x : ℝ) : ℝ := inner ℝ (3 : ℝ) x + 0

theorem outer_monotone : Monotone outer := by
  intro x y hxy
  change x * 3 + 0 ≤ y * 3 + 0
  nlinarith

theorem composed_norm_convex : IsConvexExtended (fun x : ℝ => (outer ‖x‖ : EReal)) :=
  convex_comp_monotone norm outer (example_2_6 (E := ℝ)) (example_2_5 3 0) outer_monotone

example : outer ‖(-2 : ℝ)‖ = 6 := by
  change |(-2 : ℝ)| * 3 + 0 = 6
  norm_num

#print axioms BanditRL.OnlineConvex.convex_comp_affine
#print axioms BanditRL.OnlineConvex.convex_iSup
#print axioms BanditRL.OnlineConvex.convex_comp_monotone
#print axioms shifted_indicator_convex
#print axioms supremum_convex
#print axioms composed_norm_convex
end Tests.OnlineConvexClosures
