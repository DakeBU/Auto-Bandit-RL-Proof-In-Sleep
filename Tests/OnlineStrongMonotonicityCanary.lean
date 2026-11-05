import BanditRLProof.OnlineStrongMonotonicity

noncomputable section
open Set

namespace BanditRL.OnlineConvex.SupportCarrierCanary
open BanditRL.OnlineConvex.SupportCarrierExample

theorem finite_midpoint_without_support :
    leftPoint ∈ supported ∧ rightPoint ∈ supported ∧
    ((1/2 : ℝ) • leftPoint + (1/2 : ℝ) • rightPoint : Plane) = 0 ∧
    objective (0 : Plane) = 1 ∧ (0 : Plane) ∉ supported ∧ ¬ Convex ℝ supported := by
  obtain ⟨_,hl,hr,h0,hn⟩ := support_carrier
  obtain ⟨hm,_,_,_,hv,_,_⟩ := interpolation_fails
  exact ⟨hl,hr,hm,hm ▸ hv,h0,hn⟩

def normalAt (p : Plane) (b : ℝ) : Plane :=
  (WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).symm (fun i => if i=0 then 2*p 0 else b)

private theorem normal_mem {p : Plane} (hp : p 1=0) (hx : 1≤|p 0|) {b:ℝ} (hb:b≤0) :
    normalAt p b ∈ SourceSubdifferential objective p := by
  apply (all_supports p _).mpr
  exact Or.inr ⟨hp,hx,by simp [normalAt],by simpa [normalAt] using hb⟩

theorem distinct_endpoint_normals_sharp_pair :
    normalAt rightPoint 0 ∈ SourceSubdifferential objective rightPoint ∧
    normalAt rightPoint (-1) ∈ SourceSubdifferential objective rightPoint ∧
    normalAt rightPoint 0 ≠ normalAt rightPoint (-1) ∧
    normalAt leftPoint (-2) ∈ SourceSubdifferential objective leftPoint ∧
    2 * ‖rightPoint-leftPoint‖^2 ≤
      inner ℝ (normalAt rightPoint (-1) - normalAt leftPoint (-2)) (rightPoint-leftPoint) ∧
    inner ℝ (normalAt rightPoint (-1) - normalAt leftPoint (-2)) (rightPoint-leftPoint) = 8 := by
  have r0 : rightPoint 0=1 := by norm_num [rightPoint]
  have r1 : rightPoint 1=0 := by norm_num [rightPoint]
  have l0 : leftPoint 0= -1 := by change -rightPoint 0= -1;rw [r0]
  have l1 : leftPoint 1=0 := by change -rightPoint 1=0;rw [r1];norm_num
  have nr := normal_mem (p:=rightPoint) r1 (by rw [r0];norm_num) (b:=-1) (by norm_num)
  have nl := normal_mem (p:=leftPoint) l1 (by rw [l0];norm_num) (b:=-2) (by norm_num)
  refine ⟨normal_mem r1 (by rw [r0];norm_num) le_rfl,nr,?_,nl,
    every_pair_strongly_monotone rightPoint support_carrier.2.2.1 leftPoint support_carrier.2.1 _ nr _ nl,?_⟩
  · intro hh
    have h := congrArg (fun x : Plane => x 1) hh
    norm_num [normalAt] at h
  · have hr (a b : ℝ) : inner ℝ a b = a*b := by
      exact RCLike.inner_apply' a b
    simp only [PiLp.inner_apply, Fin.sum_univ_two, PiLp.sub_apply, hr]
    norm_num [normalAt,r0,r1,l0,l1]

end BanditRL.OnlineConvex.SupportCarrierCanary

namespace BanditRL.OnlineConvex.RepairedCarrierCanary

abbrev Line := EuclideanSpace ℝ (Fin 1)
def point (r : ℝ) : Line := EuclideanSpace.single 0 r
def chart : Line ≃ₗ[ℝ] Line :=
  LinearEquiv.smulOfUnit (Units.mk0 (2 : ℝ) (by norm_num))
def carrier : Set Line := {p | (0 : ℝ) ≤ p 0 ∧ p 0 ≤ 1}
def squareValue (p : Line) : EReal := ((p 0 ^ 2 : ℝ) : EReal)
def absoluteValue (p : Line) : EReal := ((|p 0| : ℝ) : EReal)
abbrev support (f : Line → EReal) (p : Line) : Set Line :=
  SourceSubdifferential (fun u => f (chart.symm u)) (chart p)
abbrev chord (f : Line → EReal) (k : ℝ) : Prop :=
  ∀ x ∈ carrier, ∀ y ∈ carrier, ∀ a : ℝ, 0 < a → a < 1 →
    f (a • x + (1-a) • y) ≤
      (a : EReal) * f x + ((1-a : ℝ) : EReal) * f y -
        (((k/2)*a*(1-a)*‖x-y‖^2 : ℝ) : EReal)
abbrev monotoneSupports (f : Line → EReal) (k : ℝ) : Prop :=
  ∀ p ∈ carrier, ∀ q ∈ carrier, ∀ g ∈ support f p, ∀ j ∈ support f q,
    k * ‖p-q‖^2 ≤ inner ℝ (g-j) (chart (p-q))


private theorem point_zero_coord (r : ℝ) : point r 0 = r := by simp [point]
private theorem chart_coord (v : Line) : chart v 0 = 2 * v 0 := by rfl
private theorem scalar_inner (a b : ℝ) : inner ℝ a b = a*b := by
  exact RCLike.inner_apply' a b
private theorem line_inner (a b : Line) : inner ℝ a b = a 0 * b 0 := by
  simp only [PiLp.inner_apply, Fin.sum_univ_one, scalar_inner]
private theorem line_sq (x : Line) : ‖x‖ ^ 2 = (x 0)^2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_one]

private theorem support_scalar (F : ℝ → ℝ) (p g : Line) :
    support (fun z : Line => (F (z 0) : EReal)) p g ↔
      ∀ z : Line, F (p 0) + g 0 * (2 * (z 0-p 0)) ≤ F (z 0) := by
  constructor
  · intro hg z
    have hh := hg (chart z)
    simpa only [chart.symm_apply_apply,← chart.map_sub,line_inner,chart_coord,
      PiLp.sub_apply,mul_sub,← EReal.coe_add,EReal.coe_le_coe_iff] using hh
  · intro hg u
    obtain ⟨z,rfl⟩ := chart.surjective u
    simpa only [chart.symm_apply_apply,← chart.map_sub,line_inner,chart_coord,
      PiLp.sub_apply,mul_sub,← EReal.coe_add,EReal.coe_le_coe_iff] using hg z

private theorem finite_facts (F : Line → ℝ) (hf : ConvexOn ℝ Set.univ F) :
    SourceProper (fun z => (F z:EReal)) ∧ IsConvexExtended (fun z => (F z:EReal)) := by
  have hb (z : Line) := EReal.coe_ne_bot (F z)
  refine ⟨⟨hb,0,F 0,rfl⟩,(convexExtended_iff_toReal _ hb).mpr ?_⟩
  simpa [effectiveDomain] using hf

private theorem interval_convex : Convex ℝ carrier := by
  intro x hx y hy a b ha hb hab
  change 0 ≤ a*x 0+b*y 0 ∧ a*x 0+b*y 0 ≤ 1
  refine ⟨add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1),?_⟩
  linarith only [mul_le_mul_of_nonneg_left hx.2 ha, mul_le_mul_of_nonneg_left hy.2 hb,hab]

private theorem square_mix (a b x y : ℝ) (h : a+b=1) :
    (a*x+b*y)^2 = a*x^2+b*y^2-a*b*(x-y)^2 := by
  rw [show b=1-a by linarith];ring

private theorem square_chord : chord squareValue 2 := by
  intro x _ y _ a ha hb
  rw [line_sq]
  change (((a*x 0+(1-a)*y 0)^2:ℝ):EReal) ≤ _
  simp only [squareValue,PiLp.sub_apply,← EReal.coe_mul,← EReal.coe_add,← EReal.coe_sub,EReal.coe_le_coe_iff]
  rw [square_mix _ _ _ _ (by ring)]
  norm_num

private theorem square_support (p : Line) : point (p 0) ∈ support squareValue p := by
  apply (support_scalar (fun r => r^2) _ _).mpr
  intro z
  rw [point_zero_coord]; nlinarith [sq_nonneg (z 0-p 0)]

private theorem abs_support_pos (p : Line) (hp : 0 ≤ p 0) :
    point (1/2) ∈ support absoluteValue p := by
  apply (support_scalar abs _ _).mpr
  intro z
  rw [abs_of_nonneg hp,point_zero_coord]
  linarith only [le_abs_self (z 0)]

theorem scaled_square :
    monotoneSupports squareValue 2 ∧
    point 1 ∈ support squareValue (point 1) ∧
    point 0 ∈ support squareValue (point 0) ∧
    (2 : ℝ) * ‖point 1-point 0‖^2 =
      inner ℝ (point 1-point 0) (chart (point 1-point 0)) ∧
    inner ℝ (point 1-point 0) (chart (point 1-point 0)) = 2 ∧
    (2 : ℝ) * ‖chart (point 1-point 0)‖^2 = 8 := by
  have hcv : ConvexOn ℝ Set.univ (fun p : Line => (p 0)^2) := by
    refine ⟨convex_univ,?_⟩;intro x _ y _ a b ha hb hab
    change (a*x 0+b*y 0)^2 ≤ a*(x 0)^2+b*(y 0)^2
    rw [square_mix a b _ _ hab]
    exact sub_le_self _ (mul_nonneg (mul_nonneg ha hb) (sq_nonneg _))
  have facts := finite_facts _ hcv
  have parent := (SupportCarrierExample.convex_carrier_equivalence 1 chart squareValue carrier 2
    facts.1 facts.2 interval_convex (by norm_num) (fun p _ => ⟨_,square_support p⟩)).mp square_chord
  refine ⟨parent,by simpa [point_zero_coord] using square_support (point 1),
    by simpa [point_zero_coord] using square_support (point 0),?_,?_,?_⟩ <;>
    simp only [line_sq,line_inner,chart_coord,PiLp.sub_apply,point_zero_coord] <;> norm_num

theorem zero_absolute :
    chord absoluteValue 0 ∧
    point ((1 : ℝ)/2) ∈ support absoluteValue (point 0) ∧
    point (-(1 : ℝ)/2) ∈ support absoluteValue (point 0) ∧
    point ((1 : ℝ)/2) ≠ point (-(1 : ℝ)/2) ∧
    (∀ z ∈ carrier, absoluteValue (point 0) +
      (inner ℝ (point (-1)) (chart (z-point 0)) : EReal) ≤ absoluteValue z) ∧
    point (-1) ∉ support absoluteValue (point 0) ∧
    absoluteValue (((1 : ℝ)/2) • point 1 + ((1 : ℝ)/2) • point 0) =
      (((1 : ℝ)/2) : EReal) := by
  have hcv : ConvexOn ℝ Set.univ (fun p : Line => |p 0|) := by
    refine ⟨convex_univ,?_⟩;intro x _ y _ a b ha hb _
    change |a*x 0+b*y 0| ≤ a*|x 0|+b*|y 0|
    simpa [abs_mul,abs_of_nonneg ha,abs_of_nonneg hb] using abs_add_le (a*x 0) (b*y 0)
  have facts := finite_facts _ hcv
  have hm : monotoneSupports absoluteValue 0 := by
    intro p _ q _ g hg j hj
    have h := (support_scalar abs p g).mp hg q
    have k := (support_scalar abs q j).mp hj p
    rw [zero_mul,line_inner,chart_coord]
    change 0 ≤ (g 0-j 0)*(2*(p 0-q 0))
    linarith only [h,k]
  have parent := (SupportCarrierExample.convex_carrier_equivalence 1 chart absoluteValue carrier 0
    facts.1 facts.2 interval_convex le_rfl (fun p hp => ⟨_,abs_support_pos p hp.1⟩)).mpr hm
  refine ⟨parent,abs_support_pos (point 0) (by simp [point_zero_coord]),?_,?_,?_,?_,?_⟩
  · apply (support_scalar abs _ _).mpr
    intro z
    simp only [point_zero_coord,abs_zero,sub_zero,zero_add]
    linarith only [neg_le_abs (z 0)]
  · intro eq
    have hh := congrArg (fun v : Line => v 0) eq
    norm_num [point_zero_coord] at hh
  · intro z hz
    simp only [absoluteValue,line_inner,chart_coord,PiLp.sub_apply,point_zero_coord,
      abs_zero,EReal.coe_zero,zero_add,EReal.coe_le_coe_iff,sub_zero]
    rw [abs_of_nonneg hz.1]; linarith only [hz.1]
  · intro hg
    have bad := (support_scalar abs _ _).mp hg (point (-1))
    norm_num [point_zero_coord] at bad
  · change ((↑(|(1/2:ℝ)*point 1 0+(1/2)*point 0 0|) : EReal)) = _
    norm_num [point_zero_coord]
    change ((↑((1:ℝ)/2)):EReal) = (↑((2:ℝ)⁻¹):EReal)
    rw [one_div]

end BanditRL.OnlineConvex.RepairedCarrierCanary
