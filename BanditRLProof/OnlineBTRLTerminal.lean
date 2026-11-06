import BanditRLProof.OnlineSubgradientInterior
import BanditRLProof.OnlineCumulativePotential
import BanditRLProof.OnlineStrongConvexMinimum
import BanditRLProof.OnlineStrongConvexAttainment

noncomputable section
attribute [local instance] Classical.propDecidable
open Set Finset
open BanditRL.OnlineConvex
namespace BanditRL.OnlineBTRL

/-- A real extension for evaluating a source regularizer. All uses in the regret bound are in X. -/
def regularizerValue {E : Type*} (X : Set E) (psi : ℕ → X → ℝ) (n : ℕ) : E → ℝ :=
  Function.extend Subtype.val (psi n) (fun _ => 0)

/-- Source inclusive objective on its given carrier. -/
def sourceInclusive {E : Type*} (X : Set E) (psi : ℕ → X → ℝ)
    (loss : ℕ → E → EReal) (n : ℕ) (w : X) : EReal :=
  (psi n w : EReal) + ∑ i ∈ range (n + 1), loss i w.val

/-- Restriction to the feasible set, extended by top outside it. -/
def feasibleInclusive {E : Type*} (X V : Set E) (hVX : V ⊆ X)
    (psi : ℕ → X → ℝ) (loss : ℕ → E → EReal) (n : ℕ) (v : E) : EReal :=
  if hv : v ∈ V then sourceInclusive X psi loss n ⟨v, hVX hv⟩ else ⊤

private theorem feasible_closed {E : Type*} [TopologicalSpace E] (X V : Set E) (hVX : V ⊆ X)
    (hV : IsClosed V) (psi : ℕ → X → ℝ) (loss : ℕ → E → EReal) (n : ℕ)
    (hc : SourceClosed (sourceInclusive X psi loss n)) :
    SourceClosed (feasibleInclusive X V hVX psi loss n) := by
  intro c
  let j : V → X := fun v => ⟨v.val, hVX v.property⟩
  have hj : Continuous j := continuous_subtype_val.subtype_mk _
  let C := {w : X | sourceInclusive X psi loss n w ≤ (c : EReal)}
  have hi := hV.isClosedMap_subtype_val _ ((hc c).preimage hj)
  change IsClosed (Subtype.val '' (j ⁻¹' C)) at hi
  convert hi using 1
  ext v
  constructor
  · intro hv
    by_cases hvV : v ∈ V
    · exact ⟨⟨v,hvV⟩, by simpa [C,j,feasibleInclusive,hvV] using hv, rfl⟩
    · simpa [feasibleInclusive,hvV] using hv
  · rintro ⟨w,hw,rfl⟩
    simpa [feasibleInclusive,w.property,C,j] using hw

private theorem feasible_value {E : Type*} (X V : Set E) (hVX : V ⊆ X)
    (psi : ℕ → X → ℝ) (loss : ℕ → E → EReal) (n : ℕ) (v : E) (hv : v ∈ V)
    (hbot : ∀ i ≤ n, loss i v ≠ ⊥) (hfin : ∀ i ≤ n, loss i v ≠ ⊤) :
    feasibleInclusive X V hVX psi loss n v =
      ((regularizerValue X psi n v + ∑ i ∈ range (n+1), (loss i v).toReal : ℝ) : EReal) := by
  have hreg : regularizerValue X psi n v = psi n ⟨v,hVX hv⟩ :=
    Subtype.val_injective.extend_apply (psi n) _ ⟨v,hVX hv⟩
  rw [hreg, feasibleInclusive, dif_pos hv, sourceInclusive, EReal.coe_add]
  congr 1
  have hs (k : ℕ) (hk : k ≤ n+1) :
      ∑ i ∈ range k, loss i v = ((∑ i ∈ range k, (loss i v).toReal : ℝ) : EReal) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [sum_range_succ, sum_range_succ, EReal.coe_add, ih (by omega),
        EReal.coe_toReal (hfin k (by omega)) (hbot k (by omega))]
  exact hs _ le_rfl
private theorem ambient_agreement_closed {E : Type*} [TopologicalSpace E]
    (X : Set E) (f : X → EReal) (F : E → EReal) (hF : SourceClosed F)
    (h : ∀ x : X, f x = F x.val) : SourceClosed f := by
  intro c
  simpa only [show f = F ∘ Subtype.val from funext h] using
    (hF c).preimage (continuous_subtype_val : Continuous (Subtype.val : X → E))

private theorem feasible_data {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {X V : Set E} (hVX : V ⊆ X) (hV : Convex ℝ V) (hne : V.Nonempty)
    (psi : ℕ → X → ℝ) (loss : ℕ → E → EReal) (n : ℕ) (l : ℝ)
    (hb : ∀ i ≤ n, ∀ v, loss i v ≠ ⊥) (hd : ∀ i ≤ n, V ⊆ effectiveDomain (loss i))
    (hs : ∀ p q : X, sourceInclusive X psi loss n p < ⊤ → sourceInclusive X psi loss n q < ⊤ →
      ∀ a : ℝ, 0 < a → a < 1 → ∀ hz : a • p.val + (1-a) • q.val ∈ X,
        sourceInclusive X psi loss n ⟨a • p.val + (1-a) • q.val,hz⟩ ≤
          (a : EReal) * sourceInclusive X psi loss n p + ((1-a : ℝ) : EReal) * sourceInclusive X psi loss n q -
          (((l/2)*a*(1-a)*‖p.val-q.val‖^2 : ℝ) : EReal)) :
    let H := feasibleInclusive X V hVX psi loss n
    SourceProper H ∧ effectiveDomain H = V ∧
    ∀ p ∈ V, ∀ q ∈ V, ∀ a : ℝ, 0 < a → a < 1 →
      H (a • p + (1-a) • q) ≤ (a : EReal)*H p + ((1-a : ℝ) : EReal)*H q -
          (((l/2)*a*(1-a)*‖p-q‖^2 : ℝ) : EReal) := by
  dsimp only
  have hf (v : E) (hv : v ∈ V) := feasible_value X V hVX psi loss n v hv
    (fun i hi => hb i hi v) (fun i hi => ne_of_lt (hd i hi hv))
  have hdom : effectiveDomain (feasibleInclusive X V hVX psi loss n) = V := by
    ext v
    change feasibleInclusive X V hVX psi loss n v < ⊤ ↔ _
    by_cases hv : v ∈ V
    · exact iff_of_true ((hf v hv).symm ▸ EReal.coe_lt_top _) hv
    · simp [feasibleInclusive,hv]
  refine ⟨⟨?_,?_⟩,hdom,?_⟩
  · intro v
    by_cases hv : v ∈ V
    · simp [hf v hv]
    · simp [feasibleInclusive,hv]
  · obtain ⟨v,hv⟩ := hne
    exact ⟨v,_,hf v hv⟩
  · intro p hp q hq a ha ha1
    have hz := hV hp hq ha.le (sub_nonneg.mpr ha1.le) (by ring)
    have hfinite (v : E) (hv : v ∈ V) : sourceInclusive X psi loss n ⟨v,hVX hv⟩ < ⊤ := by
      have h1 : v ∈ effectiveDomain (feasibleInclusive X V hVX psi loss n) := hdom.symm ▸ hv
      simpa [effectiveDomain,feasibleInclusive,hv] using h1
    simpa only [feasibleInclusive,dif_pos hp,dif_pos hq,dif_pos hz] using
      hs ⟨p,hVX hp⟩ ⟨q,hVX hq⟩ (hfinite p hp) (hfinite q hq) a ha ha1 (hVX hz)

private theorem ambient_agreement_proper {E : Type*} (X V : Set E) (hVX : V ⊆ X)
    (hV : V.Nonempty) (psi : ℕ → X → ℝ) (loss : ℕ → E → EReal) (n : ℕ)
    (F : E → EReal) (hF : SourceProper F)
    (agree : ∀ x : X, sourceInclusive X psi loss n x = F x.val)
    (hb : ∀ i ≤ n, ∀ v, loss i v ≠ ⊥)
    (hd : ∀ i ≤ n, ∀ v ∈ V, loss i v < ⊤) :
    SourceProper (sourceInclusive X psi loss n) := by
  refine ⟨fun x => (agree x) ▸ hF.1 x.val,?_⟩
  obtain ⟨v,hv⟩ := hV
  have eq := feasible_value X V hVX psi loss n v hv (fun i hi => hb i hi v)
    (fun i hi => ne_of_lt (hd i hi v hv))
  exact ⟨⟨v,hVX hv⟩,_,by simpa only [feasibleInclusive,dif_pos hv] using eq⟩

private theorem ambient_agreement_strong {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (f : X → EReal) (F : E → EReal) (l : ℝ)
    (agree : ∀ w : X, f w = F w.val)
    (hs : ∀ p ∈ effectiveDomain F, ∀ q ∈ effectiveDomain F, ∀ a : ℝ, 0<a → a<1 →
      F (a • p + (1-a) • q) ≤ (a : EReal)*F p + ((1-a : ℝ) : EReal)*F q -
        (((l/2)*a*(1-a)*‖p-q‖^2 : ℝ) : EReal)) :
    ∀ p q : X, f p < ⊤ → f q < ⊤ → ∀ a : ℝ, 0<a → a<1 →
      ∀ hz : a • p.val + (1-a) • q.val ∈ X,
      f ⟨_,hz⟩ ≤ (a : EReal)*f p + ((1-a : ℝ) : EReal)*f q -
        (((l/2)*a*(1-a)*‖p.val-q.val‖^2 : ℝ) : EReal) := by
  intro p q hp hq a ha ha1 hz
  rw [agree] at hp hq
  simpa only [agree] using hs p.val hp q.val hq a ha ha1

private theorem ambient_feasible_closed {E : Type*} [TopologicalSpace E]
    (X V : Set E) (hVX : V ⊆ X) (hV : IsClosed V)
    (psi : ℕ → X → ℝ) (loss : ℕ → E → EReal) (n : ℕ)
    (F : E → EReal) (hF : SourceClosed F)
    (agree : ∀ v (hv : v ∈ V), sourceInclusive X psi loss n ⟨v,hVX hv⟩ = F v) :
    SourceClosed (feasibleInclusive X V hVX psi loss n) := by
  intro c
  have hh : {v | feasibleInclusive X V hVX psi loss n v ≤ (c : EReal)} =
      V ∩ {v | F v ≤ (c : EReal)} := by
    ext v
    by_cases hv : v ∈ V <;> simp [feasibleInclusive,hv,agree]
  rw [hh]
  exact hV.inter (hF c)

theorem corrected_btrl_terminal_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (T : ℕ) (hT : 0 < T) (X V : Set E) (hVX : V ⊆ X)
    (hVconv : Convex ℝ V) (hVclosed : IsClosed V) (hVnonempty : V.Nonempty)
    (psi : ℕ → X → ℝ) (loss : ℕ → E → EReal)
    (hlossBot : ∀ i < T, ∀ v, loss i v ≠ ⊥)
    (hlossDom : ∀ i < T, V ⊆ effectiveDomain (loss i))
    (lam : ℕ → ℝ) (hlam : ∀ t < T, 0 < lam t)
    (hproper : ∀ t < T, SourceProper (sourceInclusive X psi loss t))
    (hclosed : ∀ t < T, SourceClosed (sourceInclusive X psi loss t))
    (hstrong : ∀ t < T, ∀ p q : X,
      sourceInclusive X psi loss t p < ⊤ → sourceInclusive X psi loss t q < ⊤ →
      ∀ a : ℝ, 0 < a → a < 1 → ∀ hz : a • p.val + (1 - a) • q.val ∈ X,
        sourceInclusive X psi loss t ⟨a • p.val + (1 - a) • q.val, hz⟩ ≤
          (a : EReal) * sourceInclusive X psi loss t p +
          ((1 - a : ℝ) : EReal) * sourceInclusive X psi loss t q -
          (((lam t / 2) * a * (1 - a) * ‖p.val - q.val‖ ^ 2 : ℝ) : EReal))
    (x : ℕ → E) (hx : ∀ t < T, x t ∈ V)
    (hmin : ∀ t < T, IsMinOn (feasibleInclusive X V hVX psi loss t) V (x t))
    (u : E) (hu : u ∈ V) :
    let r := regularizerValue X psi
    let regret := (∑ t ∈ range T, (loss t (x t)).toReal) -
      ∑ t ∈ range T, (loss t u).toReal
    let corrected := r (T - 1) u - r 0 (x 0) -
      (∑ t ∈ range (T - 1), (lam t / 2) * ‖x t - x (t + 1)‖ ^ 2) +
      ∑ t ∈ range (T - 1), (r t (x (t + 1)) - r (t + 1) (x (t + 1)))
    regret ≤ corrected - (lam (T - 1) / 2) * ‖u - x (T - 1)‖ ^ 2 ∧
      regret ≤ corrected := by
  let r := regularizerValue X psi
  let L := fun i v => (loss i v).toReal
  let G := fun n v => r n v + ∑ i ∈ range (n+1), L i v
  let H := feasibleInclusive X V hVX psi loss
  have val (n : ℕ) (hn : n < T) (v : E) (hv : v ∈ V) : (H n v).toReal = G n v := by
    have eq := feasible_value X V hVX psi loss n v hv (fun i hi => hlossBot i (by omega) v)
      (fun i hi => ne_of_lt (hlossDom i (by omega) hv))
    simpa only [H,eq,EReal.toReal_coe,G,L,r] using congrArg EReal.toReal eq
  have growth (n : ℕ) (hn : n < T) (v : E) (hv : v ∈ V) :
      G n (x n) + (lam n / 2) * ‖v - x n‖ ^ 2 ≤ G n v := by
    obtain ⟨hp,hd,hs⟩ := feasible_data hVX hVconv hVnonempty psi loss n (lam n)
      (fun i hi => hlossBot i (by omega)) (fun i hi => hlossDom i (by omega)) (hstrong n hn)
    have hg := stronglyConvex_minimum_growth (H n) V (lam n) hp hVconv
      hd.symm.subset (hlam n hn).le hs (x n) (hx n hn) (hmin n hn) v hv
    simpa only [val n hn _ (hx n hn), val n hn _ hv] using hg
  let y : ℕ → E := fun i => if i=T then x (T-1) else x i
  have hy (i : ℕ) (hi : i<T) : y i = x i := if_neg (ne_of_lt hi)
  have hlast : T-1 < T := by omega
  have he : T-1+1=T := by omega
  have hi := BanditRL.OnlineCumulativePotential.finite_regret_identity r L x u (x (T-1)) T hT
  change (∑ t ∈ range T, (L t (y t) - L t u)) = r (T-1) u - r 0 (y 0) +
    (∑ t ∈ range T, (G t (y t) - G t (y (t+1)))) +
    (∑ t ∈ range (T-1), (r t (y (t+1)) - r (t+1) (y (t+1)))) +
    G (T-1) (x (T-1)) - G (T-1) u at hi
  have hmove : (∑ t ∈ range T, (G t (y t) - G t (y (t+1)))) ≤
      -(∑ t ∈ range (T-1), (lam t/2)*‖x t-x (t+1)‖^2) := by
    conv_lhs => rw [← he, sum_range_succ]
    rw [hy _ hlast,he,show y T=x (T-1) from if_pos rfl,sub_self,add_zero,← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro i hi'
    have hi0 := mem_range.mp hi'
    rw [hy _ (by omega),hy _ (by omega)]
    have hg := growth i (by omega) (x (i+1)) (hx _ (by omega))
    rw [norm_sub_rev (x (i+1))] at hg
    linarith
  have hsum : (∑ i ∈ range T, (L i (y i)-L i u)) =
      (∑ i ∈ range T,L i (x i)) - ∑ i ∈ range T,L i u := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i hi' => by rw [hy _ (mem_range.mp hi')])
  have hdrift : (∑ i ∈ range (T-1), (r i (y (i+1))-r (i+1) (y (i+1)))) =
      ∑ i ∈ range (T-1), (r i (x (i+1))-r (i+1) (x (i+1))) := by
    apply Finset.sum_congr rfl
    intro i hi'
    have hi0 := mem_range.mp hi'
    rw [hy _ (by omega)]
  rw [hsum,hy _ hT,hdrift] at hi
  have hg := growth (T-1) hlast u hu
  dsimp only
  change (_ : ℝ) ≤ r (T-1) u - r 0 (x 0) - _ + _ - _ ∧ _
  have hterm : 0 ≤ (lam (T-1)/2)*‖u-x (T-1)‖^2 := mul_nonneg (by linarith [hlam _ hlast]) (sq_nonneg _)
  change (∑ i ∈ range T, L i (x i)) - ∑ i ∈ range T, L i u ≤ _ ∧
         (∑ i ∈ range T, L i (x i)) - ∑ i ∈ range T, L i u ≤ _
  constructor <;> linarith

theorem btrl_real_round_minimizer_existsUnique {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (T : ℕ) (hT : 0 < T) (X V : Set E) (hVX : V ⊆ X)
    (hVconv : Convex ℝ V) (hVclosed : IsClosed V) (hVnonempty : V.Nonempty)
    (psi : ℕ → X → ℝ) (loss : ℕ → E → EReal)
    (hlossBot : ∀ i < T, ∀ v, loss i v ≠ ⊥)
    (hlossDom : ∀ i < T, V ⊆ effectiveDomain (loss i))
    (lam : ℕ → ℝ) (hlam : ∀ t < T, 0 < lam t)
    (hproper : ∀ t < T, SourceProper (sourceInclusive X psi loss t))
    (hclosed : ∀ t < T, SourceClosed (sourceInclusive X psi loss t))
    (hstrong : ∀ t < T, ∀ p q : X,
      sourceInclusive X psi loss t p < ⊤ → sourceInclusive X psi loss t q < ⊤ →
      ∀ a : ℝ, 0 < a → a < 1 → ∀ hz : a • p.val + (1 - a) • q.val ∈ X,
        sourceInclusive X psi loss t ⟨a • p.val + (1 - a) • q.val, hz⟩ ≤
          (a : EReal) * sourceInclusive X psi loss t p +
          ((1 - a : ℝ) : EReal) * sourceInclusive X psi loss t q -
          (((lam t / 2) * a * (1 - a) * ‖p.val - q.val‖ ^ 2 : ℝ) : EReal)) :
    ∀ t < T, ∃! p : E, p ∈ V ∧ IsMinOn (feasibleInclusive X V hVX psi loss t) V p := by
  intro n hn
  let H := feasibleInclusive X V hVX psi loss n
  obtain ⟨hP,hD,hS⟩ := feasible_data hVX hVconv hVnonempty psi loss n (lam n)
    (fun i hi => hlossBot i (by omega)) (fun i hi => hlossDom i (by omega)) (hstrong n hn)
  change SourceProper H at hP
  change effectiveDomain H = V at hD
  have HC : IsConvexExtended H := by
    apply (theorem_2_4 H hP.1 (hD.symm ▸ hVconv)).2
    intro p hp q hq a ha ha1
    have hs := hS p (hD ▸ hp) q (hD ▸ hq) a ha ha1
    refine hs.trans ?_
    have hc : 0 ≤ (lam n / 2) * a * (1-a) * ‖p-q‖^2 := by
      have := hlam n hn
      exact mul_nonneg (mul_nonneg (mul_nonneg (div_nonneg (hlam n hn).le (by norm_num)) ha.le) (sub_nonneg.mpr ha1.le)) (sq_nonneg _)
    have hp' := EReal.coe_toReal (ne_of_lt hp) (hP.1 p)
    have hq' := EReal.coe_toReal (ne_of_lt hq) (hP.1 q)
    change _ - _ ≤ (a : EReal) * H p + ((1-a : ℝ) : EReal) * H q
    change (a : EReal) * H p + ((1-a : ℝ) : EReal) * H q - _ ≤ _
    rw [← hp',← hq',← EReal.coe_mul,← EReal.coe_mul,← EReal.coe_add,← EReal.coe_sub,EReal.coe_le_coe_iff]
    linarith
  let d := Module.finrank ℝ E
  let e : E ≃ₗ[ℝ] EuclideanSpace ℝ (Fin d) :=
    LinearEquiv.ofFinrankEq _ _ finrank_euclideanSpace_fin.symm
  let F := fun u => H (e.symm u)
  have hPF : SourceProper F := by
    refine ⟨fun y => hP.1 _,?_⟩
    obtain ⟨p,r,he⟩ := hP.2
    exact ⟨e p,r,by simpa only [F,LinearEquiv.symm_apply_apply] using he⟩
  have hCF : IsConvexExtended F := HC.affine_preimage
    (e.symm.toAffineEquiv.toAffineMap.prodMap (AffineMap.id ℝ ℝ))
  have hDF : effectiveDomain F = e.symm ⁻¹' V := by
    rw [← hD]
    rfl
  have hi : (intrinsicInterior ℝ (effectiveDomain F)).Nonempty := by
    rw [hDF]
    apply Set.Nonempty.intrinsicInterior (hVconv.linear_preimage e.symm.toLinearMap)
    obtain ⟨p,hp⟩ := hVnonempty
    exact ⟨e p,by simpa⟩
  obtain ⟨s,hs⟩ := hi
  have hsub := subgradient_exists_of_relative_domain_interior F hPF hCF s hs
  have hsH : {p : E | (SourceSubdifferential (fun u => H (e.symm u)) (e p)).Nonempty}.Nonempty :=
    ⟨e.symm s,by simpa only [Set.mem_setOf_eq,LinearEquiv.apply_symm_apply,F] using hsub⟩
  obtain ⟨p,⟨hp,hmin⟩,hu⟩ := stronglyConvex_existsUnique_minimizer d e H (lam n) hP
    (feasible_closed X V hVX hVclosed psi loss n (hclosed n hn)) (hlam n hn)
    (by rw [hD]; exact hS) hsH
  refine ⟨p,⟨hD ▸ hp,fun q _ => hmin q⟩,?_⟩
  rintro q ⟨hq,hm⟩
  apply hu q
  refine ⟨hD.symm ▸ hq,?_⟩
  intro v
  by_cases hv : v ∈ V
  · exact hm hv
  · simp [H,feasibleInclusive,hv]

end BanditRL.OnlineBTRL
