import BanditRLProof.OnlineStrongConvexSubgradientIff

noncomputable section
open Set
namespace BanditRL.OnlineConvex.SupportCarrierExample

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def halfPlane : Set Plane := {p | 0 ≤ p 1}
def boundaryValue (p : Plane) : ℝ := max (p 0 ^ 2) 1
def finiteValue (p : Plane) : ℝ :=
  if p 1 = 0 then boundaryValue p else (p 0 ^ 2 + p 1 ^ 2)
open scoped Classical in
def objective (p : Plane) : EReal :=
  if p ∈ halfPlane then (finiteValue p : EReal) else ⊤
def supported : Set Plane := {p | (SourceSubdifferential objective p).Nonempty}
def rightPoint : Plane := (WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).symm (fun i => if i = 0 then 1 else 0)
def leftPoint : Plane := -rightPoint


private theorem half_convex : Convex ℝ halfPlane := by
  intro x hx y hy a b ha hb hab
  change 0 ≤ a * x 1 + b * y 1
  exact add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)

private theorem square_mix (x y a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    (a*x+b*y)^2 ≤ a*x^2+b*y^2 := by
  have hb' : b = 1-a := by linarith
  subst b
  nlinarith [mul_nonneg (mul_nonneg ha hb) (sq_nonneg (x-y))]

private theorem base_lower (p : Plane) : p 0 ^ 2 + p 1 ^ 2 ≤ finiteValue p := by
  by_cases h : p 1 = 0
  · simp [finiteValue,boundaryValue,h]
  · simp [finiteValue,h]

private theorem finite_convex : ConvexOn ℝ halfPlane finiteValue := by
  rw [convexOn_iff_forall_pos]
  refine ⟨half_convex, ?_⟩
  intro x hx y hy a b ha hb hab
  let m := a • x + b • y
  have hm (i : Fin 2) : m i = a * x i + b * y i := rfl
  have hx1 : 0 ≤ x 1 := hx
  have hy1 : 0 ≤ y 1 := hy
  change finiteValue m ≤ a * finiteValue x + b * finiteValue y
  by_cases hz : m 1 = 0
  · have hz' := (hm 1).symm.trans hz
    have hax := mul_nonneg ha.le hx1
    have hby := mul_nonneg hb.le hy1
    have ex : x 1 = 0 := (mul_eq_zero.mp (show a*x 1=0 by linarith)).resolve_left ha.ne'
    have ey : y 1 = 0 := (mul_eq_zero.mp (show b*y 1=0 by linarith)).resolve_left hb.ne'
    simp only [finiteValue,hz,ex,ey,if_true,boundaryValue,hm]
    apply max_le
    · exact (square_mix _ _ _ _ ha.le hb.le hab).trans
        (add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ha.le)
          (mul_le_mul_of_nonneg_left (le_max_left _ _) hb.le))
    · have ux := mul_le_mul_of_nonneg_left (le_max_right (x 0 ^ 2) (1:ℝ)) ha.le
      have uy := mul_le_mul_of_nonneg_left (le_max_right (y 0 ^ 2) (1:ℝ)) hb.le
      linarith
  · rw [show finiteValue m = m 0 ^ 2 + m 1 ^ 2 by simp [finiteValue,hz],hm 0,hm 1]
    change (a*x 0+b*y 0)^2+(a*x 1+b*y 1)^2 ≤ a*finiteValue x+b*finiteValue y
    calc
      _ ≤ (a*(x 0)^2+b*(y 0)^2)+(a*(x 1)^2+b*(y 1)^2) :=
        add_le_add (square_mix _ _ _ _ ha.le hb.le hab) (square_mix _ _ _ _ ha.le hb.le hab)
      _ = a*((x 0)^2+(x 1)^2)+b*((y 0)^2+(y 1)^2) := by ring
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (base_lower x) ha.le)
        (mul_le_mul_of_nonneg_left (base_lower y) hb.le)

private theorem objective_on {x : Plane} (hx : x ∈ halfPlane) :
    objective x = (finiteValue x : EReal) := by simp [objective,hx]

private theorem zero_mem : (0 : Plane) ∈ halfPlane := by change (0 : ℝ) ≤ 0; exact le_rfl

theorem carrier_and_convexity :
    SourceProper objective ∧ IsConvexExtended objective ∧
    effectiveDomain objective = halfPlane ∧ ConvexOn ℝ halfPlane finiteValue := by
  classical
  have nb (x : Plane) : objective x ≠ ⊥ := by
    by_cases hx : x ∈ halfPlane
    · rw [objective_on hx]; exact EReal.coe_ne_bot _
    · simp [objective,hx]
  have dom : effectiveDomain objective = halfPlane := by
    ext x
    by_cases hx : x ∈ halfPlane <;> simp [effectiveDomain,objective,hx]
  have hp : SourceProper objective := ⟨nb,0,finiteValue 0,objective_on zero_mem⟩
  refine ⟨hp,(convexExtended_iff_toReal objective nb).mpr ?_,dom,finite_convex⟩
  rw [dom]
  apply finite_convex.congr
  intro x hx
  simp [objective_on hx]

private theorem right_fst : rightPoint 0 = 1 := by norm_num [rightPoint]
private theorem right_snd : rightPoint 1 = 0 := by norm_num [rightPoint]
private theorem point_mid : (1/2 : ℝ) • leftPoint + (1/2 : ℝ) • rightPoint = 0 := by
  simp [leftPoint]
private theorem sep_sq : ‖leftPoint - rightPoint‖ ^ 2 = 4 := by
  rw [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_two]
  change ((-rightPoint 0)-rightPoint 0)^2+((-rightPoint 1)-rightPoint 1)^2=4
  norm_num [right_fst,right_snd]
private theorem obj_right : objective rightPoint = 1 := by
  have h : rightPoint ∈ halfPlane := by change 0 ≤ rightPoint 1; rw [right_snd]
  rw [objective_on h]
  norm_num [finiteValue,boundaryValue,right_fst,right_snd]
private theorem obj_left : objective leftPoint = 1 := by
  have x : leftPoint 0 = -1 := by change -rightPoint 0 = -1; rw [right_fst]
  have y : leftPoint 1 = 0 := by change -rightPoint 1 = 0; rw [right_snd]; norm_num
  have h : leftPoint ∈ halfPlane := by change 0 ≤ leftPoint 1; rw [y]
  rw [objective_on h]
  norm_num [finiteValue,boundaryValue,x,y]
private theorem obj_zero : objective 0 = 1 := by
  rw [objective_on zero_mem]
  norm_num [finiteValue,boundaryValue]

theorem interpolation_fails :
    let m := (1 / 2 : ℝ) • leftPoint + (1 / 2 : ℝ) • rightPoint;
    let r := ((1 / 2 : ℝ) : EReal) * objective leftPoint +
      ((1 / 2 : ℝ) : EReal) * objective rightPoint -
      ((((2 : ℝ) / 2) * (1 / 2) * (1 / 2) * ‖leftPoint - rightPoint‖ ^ 2 : ℝ) : EReal);
    m = 0 ∧ objective leftPoint = 1 ∧ objective rightPoint = 1 ∧
    ‖leftPoint - rightPoint‖ ^ 2 = 4 ∧ objective m = 1 ∧ r = 0 ∧ ¬ (objective m ≤ r) := by
  dsimp only
  rw [point_mid,obj_left,obj_right,sep_sq,obj_zero]
  norm_num
  have half_sum : (((1/2 : ℝ) : EReal) + ((1/2 : ℝ) : EReal)) = 1 := by
    rw [← EReal.coe_add]
    norm_num
  rw [half_sum]
  have h : (1 : EReal) - 1 = 0 :=
    EReal.sub_self (x := (1 : EReal)) (EReal.coe_ne_top 1) (EReal.coe_ne_bot 1)
  exact ⟨h, lt_of_eq_of_lt h (by exact_mod_cast (zero_lt_one : (0:ℝ) < 1))⟩


open Filter
open scoped Topology

private def xy (s t : ℝ) : Plane :=
  (WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).symm (fun i => if i = 0 then s else t)
private theorem xy_fst (s t : ℝ) : xy s t 0 = s := by simp [xy]
private theorem xy_snd (s t : ℝ) : xy s t 1 = t := by simp [xy]
private theorem inner_coords (g q p : Plane) :
    inner ℝ g (q-p) = g 0 * (q 0-p 0) + g 1 * (q 1-p 1) := by
  have hreal (a b : ℝ) : inner ℝ a b = a * b := by
    exact RCLike.inner_apply' a b
  simp only [PiLp.inner_apply,Fin.sum_univ_two,PiLp.sub_apply]
  exact congrArg₂ (· + ·) (hreal _ _) (hreal _ _)

private theorem support_at_positive_query {p g : Plane} (hp : p ∈ halfPlane)
    (hg : g ∈ SourceSubdifferential objective p) (s t : ℝ) (ht : 0 < t) :
    finiteValue p + g 0*(s-p 0) + g 1*(t-p 1) ≤ s^2+t^2 := by
  have hq : xy s t ∈ halfPlane := by change 0 ≤ xy s t 1; simpa [xy_snd] using ht.le
  have h := hg (xy s t)
  rw [objective_on hp,objective_on hq,← EReal.coe_add,EReal.coe_le_coe_iff,inner_coords] at h
  simpa [finiteValue,xy_fst,xy_snd,ht.ne',add_assoc] using h

private theorem support_boundary_trace {p g : Plane} (hp : p ∈ halfPlane)
    (hg : g ∈ SourceSubdifferential objective p) (s : ℝ) :
    finiteValue p + g 0*(s-p 0) + g 1*(0-p 1) ≤ s^2 := by
  let L := fun t : ℝ => finiteValue p + g 0*(s-p 0) + g 1*(t-p 1)
  let R := fun t : ℝ => s^2+t^2
  have hL : Continuous L := by dsimp [L]; fun_prop
  have hR : Continuous R := by dsimp [R]; fun_prop
  have hlim : L 0 ≤ R 0 :=
    le_of_tendsto_of_tendsto (hL.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ) ≤ 𝓝 0))
      (hR.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      (Filter.eventually_of_mem self_mem_nhdsWithin (fun t ht => support_at_positive_query hp hg s t ht))
  simpa [L,R] using hlim

private theorem boundary_necessary {p g : Plane} (hy : p 1 = 0)
    (hg : g ∈ SourceSubdifferential objective p) :
    1 ≤ |p 0| ∧ g 0 = 2*p 0 ∧ g 1 ≤ 0 := by
  have hp : p ∈ halfPlane := by change 0 ≤ p 1; rw [hy]
  have atSelf := support_boundary_trace hp hg (p 0)
  have ub : finiteValue p ≤ p 0 ^ 2 := by simpa [hy] using atSelf
  have lb : p 0 ^ 2 ≤ finiteValue p := by simpa [hy] using base_lower p
  have eqf := le_antisymm ub lb
  have h1 : 1 ≤ finiteValue p := by simp [finiteValue,hy,boundaryValue]
  have habs : 1 ≤ |p 0| := by
    by_contra! bad
    have hs := abs_lt.mp bad
    nlinarith [mul_pos (sub_pos.mpr hs.2) (show 0 < 1+p 0 by linarith [hs.1])]
  have hor := support_boundary_trace hp hg (g 0 / 2)
  rw [eqf,hy] at hor
  have gx : g 0 = 2*p 0 := by nlinarith [sq_nonneg (g 0-2*p 0)]
  refine ⟨habs,gx,?_⟩
  by_contra! up
  have vert := support_at_positive_query hp hg (p 0) (g 1 / 2) (by linarith)
  rw [eqf,hy] at vert
  nlinarith [sq_pos_of_pos up]

private theorem interior_necessary {p g : Plane} (hy : 0 < p 1)
    (hg : g ∈ SourceSubdifferential objective p) : g = (2:ℝ) • p := by
  have hp : p ∈ halfPlane := hy.le
  have fval : finiteValue p = p 0 ^ 2 + p 1 ^ 2 := by simp [finiteValue,hy.ne']
  have hor := support_at_positive_query hp hg (g 0/2) (p 1) hy
  rw [fval] at hor
  have gx : g 0 = 2*p 0 := by nlinarith [sq_nonneg (g 0-2*p 0)]
  let k := fun t : ℝ => t^2 - g 1 * t
  have hm : IsLocalMin k (p 1) := by
    filter_upwards [lt_mem_nhds hy] with t ht
    have hv := support_at_positive_query hp hg (p 0) t ht
    rw [fval] at hv
    change (p 1)^2-g 1*p 1 ≤ t^2-g 1*t
    linarith
  have hd : HasDerivAt k (2 * p 1 - g 1) (p 1) := by
    dsimp [k]
    convert ((hasDerivAt_id (p 1)).pow 2).sub ((hasDerivAt_id (p 1)).const_mul (g 1)) using 1
    simp
  have gy := hm.hasDerivAt_eq_zero hd
  ext i
  fin_cases i
  · exact gx
  · change g 1 = 2*p 1
    linarith

private theorem support_sufficient {p g : Plane}
    (hs : (0 < p 1 ∧ g = (2:ℝ) • p) ∨
      (p 1 = 0 ∧ 1 ≤ |p 0| ∧ g 0 = 2*p 0 ∧ g 1 ≤ 0)) :
    g ∈ SourceSubdifferential objective p := by
  intro q
  by_cases hq : q ∈ halfPlane
  · have hq1 : 0 ≤ q 1 := hq
    have hp : p ∈ halfPlane := hs.elim (fun h => h.1.le) (fun h => le_of_eq h.1.symm)
    rw [objective_on hp,objective_on hq,← EReal.coe_add,EReal.coe_le_coe_iff,inner_coords]
    apply le_trans _ (base_lower q)
    rcases hs with ⟨h,rfl⟩ | ⟨h,ha,gx,gy⟩
    · simp only [finiteValue,h.ne',if_false]
      change p 0 ^ 2 + p 1 ^ 2 + (2*p 0*(q 0-p 0)+2*p 1*(q 1-p 1)) ≤ _
      nlinarith [sq_nonneg (q 0-p 0),sq_nonneg (q 1-p 1)]
    · have hsq : 1 ≤ p 0 ^ 2 := by nlinarith [sq_abs (p 0),mul_nonneg (sub_nonneg.mpr ha) (show 0 ≤ |p 0|+1 by positivity)]
      simp only [finiteValue,h,if_true,boundaryValue,max_eq_left hsq,gx,sub_zero]
      nlinarith [sq_nonneg (q 0-p 0),sq_nonneg (q 1),mul_nonpos_of_nonpos_of_nonneg gy hq1]
  · simp [objective,hq]
theorem all_supports (p g : Plane) :
    g ∈ SourceSubdifferential objective p ↔
      (0 < p 1 ∧ g = (2 : ℝ) • p) ∨
      (p 1 = 0 ∧ 1 ≤ |p 0| ∧ g 0 = 2 * p 0 ∧ g 1 ≤ 0) := by
  constructor
  · intro hg
    have hp := subgradient_point_finite objective carrier_and_convexity.1 p g hg
    rw [carrier_and_convexity.2.2.1] at hp
    have hy : 0 ≤ p 1 := hp
    rcases hy.eq_or_lt with h | h
    · exact Or.inr ⟨h.symm,boundary_necessary h.symm hg⟩
    · exact Or.inl ⟨h,interior_necessary h hg⟩
  · exact support_sufficient


theorem support_carrier :
    supported = {p : Plane | 0 < p 1 ∨ (p 1 = 0 ∧ 1 ≤ |p 0|)} ∧
    leftPoint ∈ supported ∧ rightPoint ∈ supported ∧
    (0 : Plane) ∉ supported ∧ ¬ Convex ℝ supported := by
  have dom : supported = {p : Plane | 0 < p 1 ∨ (p 1 = 0 ∧ 1 ≤ |p 0|)} := by
    ext p
    change (∃ g, g ∈ SourceSubdifferential objective p) ↔ _
    constructor
    · rintro ⟨g,hg⟩
      rcases (all_supports p g).mp hg with h | h
      · exact Or.inl h.1
      · exact Or.inr ⟨h.1,h.2.1⟩
    · intro hp
      refine ⟨(2 : ℝ) • p,(all_supports p _).mpr ?_⟩
      rcases hp with h | ⟨h,ha⟩
      · exact Or.inl ⟨h,rfl⟩
      · refine Or.inr ⟨h,ha,rfl,?_⟩
        change 2 * p 1 ≤ 0
        rw [h, mul_zero]
  have hx : leftPoint ∈ supported := by
    rw [dom]
    right
    change -rightPoint 1 = 0 ∧ 1 ≤ |-rightPoint 0|
    norm_num [right_snd,right_fst]
  have hy : rightPoint ∈ supported := by
    rw [dom]
    right
    exact ⟨right_snd,by norm_num [right_fst]⟩
  have hz : (0 : Plane) ∉ supported := by
    rw [dom]
    change ¬ ((0 : ℝ) < 0 ∨ ((0 : ℝ) = 0 ∧ 1 ≤ |(0 : ℝ)|))
    norm_num
  refine ⟨dom,hx,hy,hz,?_⟩
  intro hconv
  apply hz
  rw [← point_mid]
  exact hconv hx hy (by norm_num : 0 ≤ (1/2 : ℝ)) (by norm_num) (by norm_num)

private theorem support_normal_data {p g : Plane} (hg : g ∈ SourceSubdifferential objective p) :
    g 0 = 2 * p 0 ∧ 0 ≤ p 1 ∧ g 1 ≤ 2 * p 1 ∧ (g 1 - 2 * p 1) * p 1 = 0 := by
  rcases (all_supports p g).mp hg with ⟨hp,rfl⟩ | ⟨hp,_,hg0,hg1⟩
  · change 2 * p 0 = 2 * p 0 ∧ 0 ≤ p 1 ∧ 2 * p 1 ≤ 2 * p 1 ∧ _ = 0
    exact ⟨rfl,hp.le,le_rfl,by change (2 * p 1 - 2 * p 1) * p 1 = 0; ring⟩
  · exact ⟨hg0,le_of_eq hp.symm,by simpa [hp] using hg1,by rw [hp,mul_zero]⟩

theorem every_pair_strongly_monotone :
    ∀ p ∈ supported, ∀ q ∈ supported, ∀ g ∈ SourceSubdifferential objective p,
      ∀ h ∈ SourceSubdifferential objective q,
        2 * ‖p - q‖ ^ 2 ≤ inner ℝ (g - h) (p - q) := by
  intro p _ q _ g hg h hh
  obtain ⟨g0,py,g1,gorth⟩ := support_normal_data hg
  obtain ⟨h0,qy,h1,horth⟩ := support_normal_data hh
  have crossG := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr g1) qy
  have crossH := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h1) py
  rw [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_two,inner_coords]
  change 2 * ((p 0 - q 0)^2 + (p 1 - q 1)^2) ≤
    (g 0 - h 0) * (p 0 - q 0) + (g 1 - h 1) * (p 1 - q 1)
  rw [g0,h0]
  nlinarith only [gorth,horth,crossG,crossH]

theorem concrete_converse_counterexample :
    SourceProper objective ∧ IsConvexExtended objective ∧
    (∀ p ∈ supported, ∀ q ∈ supported, ∀ g ∈ SourceSubdifferential objective p,
      ∀ h ∈ SourceSubdifferential objective q,
        2 * ‖p - q‖ ^ 2 ≤ inner ℝ (g - h) (p - q)) ∧
    ¬ (∀ x ∈ supported, ∀ y ∈ supported, ∀ a : ℝ, 0 < a → a < 1 →
      objective (a • x + (1 - a) • y) ≤
        (a : EReal) * objective x + ((1 - a : ℝ) : EReal) * objective y -
          ((((2 : ℝ) / 2) * a * (1-a) * ‖x-y‖ ^ 2 : ℝ) : EReal)) := by
  refine ⟨carrier_and_convexity.1,carrier_and_convexity.2.1,every_pair_strongly_monotone,?_⟩
  intro chord
  have bound := chord leftPoint support_carrier.2.1 rightPoint support_carrier.2.2.1
    (1/2 : ℝ) (by norm_num) (by norm_num)
  rw [show 1 - (1/2 : ℝ) = 1/2 by norm_num] at bound
  obtain ⟨_,_,_,_,_,_,hfail⟩ := interpolation_fails
  exact hfail bound

theorem convex_carrier_equivalence {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (d : ℕ) (e : E ≃ₗ[ℝ] EuclideanSpace ℝ (Fin d))
    (f : E → EReal) (V : Set E) (lam : ℝ)
    (hf : SourceProper f) (hconv : IsConvexExtended f) (hV : Convex ℝ V) (hlam : 0 ≤ lam)
    (hsub : ∀ p ∈ V, (SourceSubdifferential (fun u => f (e.symm u)) (e p)).Nonempty) :
    (∀ x ∈ V, ∀ y ∈ V, ∀ a : ℝ, 0 < a → a < 1 →
      f (a • x + (1 - a) • y) ≤
        (a : EReal) * f x + ((1 - a : ℝ) : EReal) * f y -
          (((lam / 2) * a * (1-a) * ‖x-y‖ ^ 2 : ℝ) : EReal)) ↔
    (∀ p ∈ V, ∀ q ∈ V, ∀ g ∈ SourceSubdifferential (fun u => f (e.symm u)) (e p),
      ∀ h ∈ SourceSubdifferential (fun u => f (e.symm u)) (e q),
        lam * ‖p-q‖ ^ 2 ≤ inner ℝ (g-h) (e (p-q))) := by
  classical
  rw [stronglyConvex_iff_sourceSubgradient_growth d e f V lam hf hV hlam hsub]
  constructor
  · intro growth p hp q hq g hg h hh
    have a := growth p hp q hq g hg
    have b := growth q hq p hp h hh
    rw [show q-p = -(p-q) by abel,map_neg,inner_neg_right,norm_neg] at a
    rw [inner_sub_left]
    linarith
  · intro mono p hp q hq g hg
    let v := q-p
    let K := lam*‖v‖^2
    let L := inner ℝ g (e v)
    let F := fun u : E => (f u).toReal
    have hfcoord : SourceProper (fun u => f (e.symm u)) := by
      refine ⟨fun u => hf.1 _,?_⟩
      obtain ⟨u,a,ha⟩ := hf.2
      exact ⟨e u,a,by simpa using ha⟩
    have finite (u : E) (hu : u ∈ V) : (F u:EReal)=f u := by
      obtain ⟨j,hj⟩ := hsub u hu
      have hd := subgradient_point_finite _ hfcoord (e u) j hj
      have ht : f u < ⊤ := by simpa [effectiveDomain] using hd
      exact EReal.coe_toReal ht.ne (hf.1 u)
    have minor (a b : E) (ha : a∈V) (hb : b∈V) (j : EuclideanSpace ℝ (Fin d))
        (hj : j ∈ SourceSubdifferential (fun u => f (e.symm u)) (e a)) :
        F a + inner ℝ j (e (b-a)) ≤ F b := by
      have z := hj (e b)
      simp only [e.symm_apply_apply,←map_sub] at z
      rw [←finite a ha,←finite b hb,←EReal.coe_add,EReal.coe_le_coe_iff] at z
      exact z
    have discrete (N : ℕ) (hN : 0<N) :
        F p + L + K/2 * (1-1/(N:ℝ)) ≤ F q := by
      let δ : ℝ := 1/(N:ℝ)
      have nr : (0:ℝ)<N := by exact_mod_cast hN
      have δpos : 0<δ := by dsimp [δ];positivity
      have unit : (N:ℝ)*δ=1 := by dsimp [δ];field_simp
      let s (i : ℕ) := (i:ℝ)*δ
      let a (i : ℕ) := p+s i • v
      have smem (i : ℕ) (hi : i≤N) : a i∈V := by
        have il : (i:ℝ)≤N := by exact_mod_cast hi
        have si : 0≤s i := mul_nonneg (Nat.cast_nonneg _) δpos.le
        have sl : s i≤1 := unit ▸ mul_le_mul_of_nonneg_right il δpos.le
        have ht := hV hp hq (sub_nonneg.mpr sl) si (show (1-s i)+s i=1 by ring)
        convert ht using 1
        dsimp [a,v]
        module
      have a0 : a 0=p := by simp [a,s]
      have aN : a N=q := by simp [a,s,unit,v]
      have inc (i : ℕ) : a (i+1)-a i=δ • v := by dsimp [a,s];push_cast;module
      have step (i : ℕ) (hi : i<N) :
          F (a i) + δ*(L+s i*K) ≤ F (a (i+1)) := by
        have ha := smem i hi.le
        have hb := smem (i+1) hi
        obtain ⟨j,hj,hdir⟩ : ∃ j ∈ SourceSubdifferential (fun u => f (e.symm u)) (e (a i)),
            L+s i*K ≤ inner ℝ j (e v) := by
          by_cases iz : i=0
          · subst i;rw [a0];exact ⟨g,hg,by simp [s,L]⟩
          · obtain ⟨j,hj⟩ := hsub _ ha
            refine ⟨j,hj,?_⟩
            have si : 0<s i := mul_pos (by exact_mod_cast Nat.pos_of_ne_zero iz) δpos
            have h := mono (a i) ha p hp j hj g hg
            rw [show a i-p=s i • v by dsimp [a];abel,norm_smul,Real.norm_eq_abs,abs_of_pos si,
                map_smul,real_inner_smul_right,inner_sub_left] at h
            apply (mul_le_mul_iff_right₀ si).mp
            dsimp [K,L]; nlinarith only [h]
        have z := minor _ _ ha hb j hj
        rw [inc,map_smul,real_inner_smul_right] at z
        exact (add_le_add_right (mul_le_mul_of_nonneg_left hdir δpos.le) _).trans z
      have partialSum (i : ℕ) (hi : i ≤ N) :
          F p + s i*L + ((i:ℝ)*((i:ℝ)-1)/2)*δ^2*K ≤ F (a i) := by
        induction i with
        | zero => simp [s,a0]
        | succ i ih =>
          have h := step i hi
          have prev := ih (Nat.le_of_succ_le hi)
          dsimp [s] at h prev ⊢
          push_cast
          linarith only [h,prev]
      have sumN := partialSum N le_rfl
      rw [aN] at sumN
      have coeff : ((N:ℝ)*((N:ℝ)-1)/2)*δ^2 = (1-1/(N:ℝ))/2 := by
        dsimp [δ]; field_simp
      change F p + ((N:ℝ)*δ)*L + _ ≤ F q at sumN
      rw [unit,one_mul,coeff] at sumN
      linarith
    have bound : F p + L + K/2 ≤ F q := by
      by_contra! bad
      let gap := F p+L+K/2-F q
      have gp : 0<gap := sub_pos.mpr bad
      obtain ⟨n,hn⟩ := exists_nat_gt (max (K/(2*gap)) 0)
      have nn : (0:ℝ)<n := (le_max_right _ _).trans_lt hn
      have hn' : 0<n := by exact_mod_cast nn
      have h := discrete n hn'
      have hk := (div_lt_iff₀ (show 0<2*gap by positivity)).mp ((le_max_left _ _).trans_lt hn)
      have hgap : K/(2*(n:ℝ)) < gap := (div_lt_iff₀ (by positivity)).mpr (by linarith only [hk])
      dsimp [gap] at hgap
      have residual : K/2 * (1-1/(n:ℝ)) = K/2 - K/(2*(n:ℝ)) := by
        field_simp [ne_of_gt nn]
      rw [residual] at h
      linarith only [h,hgap]
    change F p+L+(lam/2)*‖v‖^2 ≤ F q
    dsimp [K] at bound
    linarith

end BanditRL.OnlineConvex.SupportCarrierExample
