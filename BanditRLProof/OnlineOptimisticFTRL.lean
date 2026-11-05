import BanditRLProof.OnlineBTRLTerminal
import BanditRLProof.OnlineStrongConvexSupport
import Mathlib.Analysis.Seminorm

noncomputable section
open Set Finset
open BanditRL.OnlineConvex
namespace BanditRL.OnlineOptimistic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def hinted {X V : Set E} (incl : V ⊆ X) (psi : ℕ → X → ℝ)
    (loss : ℕ → E → EReal) (hint : ℕ → V → ℝ) (n : ℕ) (v : V) : EReal :=
  (psi n ⟨v.val,incl v.property⟩ : EReal) + ∑ i ∈ range n, loss i v.val + (hint n v : EReal)

abbrev inclusive {X V : Set E} (incl : V ⊆ X) (psi : ℕ → X → ℝ)
    (loss : ℕ → E → EReal) (n : ℕ) (v : V) : EReal :=
  BanditRL.OnlineBTRL.sourceInclusive X psi loss n ⟨v.val,incl v.property⟩

def supports {V : Set E} (f : V → EReal) (p : V) (g : E →L[ℝ] ℝ) : Prop :=
  ∀ q : V, f p + (g (q.val-p.val) : EReal) ≤ f q

def restrictedStrong {V : Set E} (f : V → EReal) (N : Seminorm ℝ E) (l : ℝ) : Prop :=
  ∀ p q : V, ∀ a : ℝ, 0 < a → a < 1 → ∀ hz : a • p.val + (1-a) • q.val ∈ V,
    f ⟨_,hz⟩ ≤ (a:EReal)*f p + ((1-a:ℝ):EReal)*f q -
      ((l/2*a*(1-a)*(N (p.val-q.val))^2 : ℝ) : EReal)

def hintedRegular {V : Set E} (A : ℕ → V → EReal) (T : ℕ) : Prop :=
  ∀ n < T, SourceClosed (A n) ∧ (∀ v : V, A n v < ⊤) ∧
    (∀ v : V, ∃ g : E →L[ℝ] ℝ, supports (A n) v g) ∧
    ∃ N : Seminorm ℝ E, (∀ v, N v = 0 → v = 0) ∧
      ∃ μ : ℝ, 0 < μ ∧ restrictedStrong (A n) N μ

def inclusiveRegular {V : Set E} (G : ℕ → V → EReal) (lam : ℕ → ℝ) (T : ℕ) : Prop :=
  ∀ n < T, SourceClosed (G n) ∧ (∀ v : V, G n v < ⊤) ∧
    (∀ v : V, ∃ g : E →L[ℝ] ℝ, supports (G n) v g) ∧
    0 ≤ lam n ∧ restrictedStrong (G n) (normSeminorm ℝ E) (lam n)

def predicts {V : Set E} (A : ℕ → V → EReal) (T : ℕ) (x : ℕ → V) : Prop :=
  ∀ n < T, ∀ q : V, A n (x n) ≤ A n q

def forecastError {V : Set E} (loss : ℕ → E → EReal) (hint : ℕ → V → ℝ)
    (n : ℕ) (q : V) : EReal := loss n q.val - (hint n q : EReal)

def nextPlay {V : Set E} (T : ℕ) (x : ℕ → V) (z : V) (n : ℕ) : V :=
  if n+1=T then z else x (n+1)

def playedRegret {V : Set E} (T : ℕ) (loss : ℕ → E → EReal) (x : ℕ → V) (u : V) : ℝ :=
  (∑ n ∈ range T, (loss n (x n).val).toReal) - ∑ n ∈ range T, (loss n u.val).toReal

def regularizerTerms {X V : Set E} (incl : V ⊆ X) (T : ℕ) (psi : ℕ → X → ℝ)
    (x : ℕ → V) (u : V) : ℝ :=
  let r (n : ℕ) (v : V) := psi n ⟨v.val,incl v.property⟩
  r (T-1) u - r 0 (x 0) + ∑ n ∈ range (T-1), (r n (x (n+1))-r (n+1) (x (n+1)))

def sharpTerms {V : Set E} (T : ℕ) (x : ℕ → V) (z : V)
    (g : ℕ → E →L[ℝ] ℝ) (lam : ℕ → ℝ) : ℝ :=
  ∑ n ∈ range T, let v := (x n).val - (nextPlay T x z n).val;
                  g n v - lam n / 2 * ‖v‖^2

attribute [local instance] Classical.propDecidable

private def liftObj {V : Set E} (f : V → EReal) (v : E) : EReal :=
  if hv : v ∈ V then f ⟨v,hv⟩ else ⊤

private theorem lift_closed {V : Set E} (hV : IsClosed V) (f : V → EReal)
    (hf : SourceClosed f) : SourceClosed (liftObj f) := by
  intro c
  have hi := hV.isClosedMap_subtype_val _ (hf c)
  convert hi using 1
  ext v
  constructor
  · intro hv
    by_cases h : v ∈ V
    · exact ⟨⟨v,h⟩, by simpa [liftObj,h] using hv,rfl⟩
    · simpa [liftObj,h] using hv
  · rintro ⟨q,hq,rfl⟩
    simpa [liftObj,q.property] using hq

private theorem prefix_noBot (loss : ℕ → E → EReal) (T : ℕ)
    (hb : ∀ i < T, ∀ v, loss i v ≠ ⊥) (n : ℕ) (hn : n ≤ T) (v : E) :
    (∑ i ∈ range n, loss i v) ≠ ⊥ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, EReal.add_ne_bot_iff]
    exact ⟨ih (by omega),hb _ (by omega) v⟩

private theorem used_finite {X V : Set E} (incl : V ⊆ X) (T : ℕ)
    (psi : ℕ → X → ℝ) (loss : ℕ → E → EReal) (hb : ∀ i < T, ∀ v, loss i v ≠ ⊥)
    (hg : ∀ i < T, ∀ v : V, inclusive incl psi loss i v < ⊤)
    (n : ℕ) (hn : n < T) (v : V) : loss n v.val ≠ ⊤ := by
  intro bad
  have h := hg n hn v
  have hb' := prefix_noBot loss T hb n hn.le v.val
  simp only [inclusive, BanditRL.OnlineBTRL.sourceInclusive, sum_range_succ, bad] at h
  simpa only [EReal.add_top_of_ne_bot hb', EReal.coe_add_top, lt_self_iff_false] using h
private structure NormCopy (F : Type*) where
  val : F

private theorem norm_comparison [FiniteDimensional ℝ E] (N : Seminorm ℝ E)
    (sep : ∀ v, N v = 0 → v = 0) : ∃ c : ℝ, 0 < c ∧ ∀ v, c*‖v‖ ≤ N v := by
  let equiv : NormCopy E ≃ E := ⟨NormCopy.val,NormCopy.mk,fun _ => rfl,fun _ => rfl⟩
  letI : AddCommGroup (NormCopy E) := equiv.addCommGroup
  letI : Module ℝ (NormCopy E) := equiv.module ℝ
  let e : NormCopy E ≃ₗ[ℝ] E := equiv.linearEquiv ℝ
  let nn := N.comp e.toLinearMap
  let ag : AddGroupNorm (NormCopy E) :=
    { nn.toAddGroupSeminorm with eq_zero_of_map_eq_zero' := fun x hx => e.injective (by simpa using sep (e x) hx) }
  letI : NormedAddCommGroup (NormCopy E) := ag.toNormedAddCommGroup
  letI : NormedSpace ℝ (NormCopy E) :=
    { (inferInstance : Module ℝ (NormCopy E)) with norm_smul_le := fun t v => (map_smul_eq_mul nn t v).le }
  letI : FiniteDimensional ℝ (NormCopy E) := e.symm.finiteDimensional
  let L : NormCopy E →L[ℝ] E := ⟨e.toLinearMap,e.toLinearMap.continuous_of_finiteDimensional⟩
  let K : ℝ := max 1 ‖L‖
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨K⁻¹,inv_pos.mpr hK,fun v => ?_⟩
  have hv := L.le_opNorm (NormCopy.mk v)
  change ‖v‖ ≤ ‖L‖ * nn (NormCopy.mk v) at hv
  rw [inv_mul_le_iff₀ hK]
  exact hv.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (apply_nonneg N v))

private theorem display_strong [FiniteDimensional ℝ E] {V : Set E} {f : V → EReal}
    {N : Seminorm ℝ E} {μ : ℝ} (sep : ∀ v, N v = 0 → v = 0) (pos : 0 < μ)
    (strong : restrictedStrong f N μ) :
    ∃ l : ℝ, 0 < l ∧ restrictedStrong f (normSeminorm ℝ E) l := by
  obtain ⟨c,hc,hh⟩ := norm_comparison N sep
  refine ⟨μ*c^2,by positivity,?_⟩
  intro p q a ha ha1 hz
  refine (strong p q a ha ha1 hz).trans (EReal.sub_le_sub le_rfl ?_)
  apply EReal.coe_le_coe_iff.mpr
  change μ*c^2/2*a*(1-a)*‖p.val-q.val‖^2 ≤ μ/2*a*(1-a)*(N (p.val-q.val))^2
  have hs := pow_le_pow_left₀ (mul_nonneg hc.le (norm_nonneg _)) (hh (p.val-q.val)) 2
  have mul := mul_le_mul_of_nonneg_left hs (show 0 ≤ μ/2*a*(1-a) from by have := sub_pos.mpr ha1; positivity)
  nlinarith only [mul]

private theorem lift_data {V : Set E} (f : V → EReal) (hne : V.Nonempty)
    (finite : ∀ p, f p ≠ ⊥ ∧ f p < ⊤) :
    SourceProper (liftObj f) ∧ effectiveDomain (liftObj f) = V := by
  constructor
  · refine ⟨fun v => ?_,?_⟩
    · by_cases hv : v ∈ V
      · simpa [liftObj,hv] using (finite ⟨v,hv⟩).1
      · simp [liftObj,hv]
    · obtain ⟨p,hp⟩ := hne
      exact ⟨p,(f ⟨p,hp⟩).toReal,by simpa [liftObj,hp] using
        (EReal.coe_toReal (finite ⟨p,hp⟩).2.ne (finite ⟨p,hp⟩).1).symm⟩
  · ext p
    by_cases hp : p ∈ V
    · simpa [effectiveDomain,liftObj,hp] using (finite ⟨p,hp⟩).2
    · simp [effectiveDomain,liftObj,hp]

private theorem restricted_growth {V : Set E} (f : V → EReal) (cv : Convex ℝ V)
    (fin : ∀ p, f p ≠ ⊥ ∧ f p < ⊤) (l : ℝ) (hl : 0 ≤ l)
    (hs : restrictedStrong f (normSeminorm ℝ E) l)
    (p q : V) (g : E →L[ℝ] ℝ) (s : supports f p g) :
    (f p).toReal + g (q.val-p.val) + l/2*‖q.val-p.val‖^2 ≤ (f q).toReal := by
  obtain ⟨hP,hD⟩ := lift_data f ⟨p,p.property⟩ fin
  have strong : ∀ x ∈ V, ∀ y ∈ V, ∀ a : ℝ, 0 < a → a < 1 →
      liftObj f (a • x + (1-a) • y) ≤
        (a:EReal)*liftObj f x + ((1-a:ℝ):EReal)*liftObj f y -
          ((l/2*a*(1-a)*‖x-y‖^2 : ℝ) : EReal) := by
    intro x hx y hy a ha ha1
    have hz := cv hx hy ha.le (sub_nonneg.mpr ha1.le) (by ring)
    simpa only [liftObj,dif_pos hx,dif_pos hy,dif_pos hz] using hs ⟨x,hx⟩ ⟨y,hy⟩ a ha ha1 hz
  have ss : ∀ z ∈ V, liftObj f p + (g (z-p.val) : EReal) ≤ liftObj f z := by
    intro z hz
    simpa only [liftObj,dif_pos p.property,dif_pos hz] using s ⟨z,hz⟩
  have h := stronglyConvex_support_growth (liftObj f) V l hP cv (hD.symm ▸ Subset.rfl)
    hl strong p p.property g ss q q.property
  simpa only [liftObj,dif_pos p.property,dif_pos q.property] using h

private theorem hinted_bot {X V : Set E} (incl : V ⊆ X) (psi : ℕ → X → ℝ)
    (loss : ℕ → E → EReal) (hint : ℕ → V → ℝ) (T : ℕ) (hb : ∀ i < T, ∀ v, loss i v ≠ ⊥)
    (n : ℕ) (hn : n < T) (v : V) : hinted incl psi loss hint n v ≠ ⊥ := by
  exact EReal.add_ne_bot_iff.mpr ⟨EReal.add_ne_bot_iff.mpr ⟨EReal.coe_ne_bot _,prefix_noBot _ _ hb _ hn.le _⟩, EReal.coe_ne_bot _⟩

private theorem real_prefix (L : ℕ → E → EReal) (n : ℕ) (v : E)
    (hf : ∀ i < n, L i v ≠ ⊥ ∧ L i v ≠ ⊤) :
    ∑ i ∈ range n, L i v = ((∑ i ∈ range n, (L i v).toReal : ℝ) : EReal) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ,sum_range_succ,EReal.coe_add,ih (fun i hi => hf i (by omega)),
      EReal.coe_toReal (hf n (by omega)).2 (hf n (by omega)).1]

private theorem quadratic_attainment [FiniteDimensional ℝ E] {V : Set E}
    (hclosed : IsClosed V) (f : V → EReal) (hf : SourceClosed f)
    (fin : ∀ v, f v ≠ ⊥ ∧ f v < ⊤) (p : V) (g : E →L[ℝ] ℝ) (l : ℝ) (hl : 0 < l)
    (growth : ∀ q : V, (f p).toReal + g (q.val-p.val) + l/2*‖q.val-p.val‖^2 ≤ (f q).toReal) :
    ∃ z : V, ∀ q, f z ≤ f q := by
  let F := liftObj f
  let S : Set E := {v | F v ≤ f p}
  have eqv (v : V) : F v.val = f v := by simp [F,liftObj,v.property]
  have pS : p.val ∈ S := by change F p.val ≤ f p; rw [eqv]
  have SD : S ⊆ V := by
    intro v hv
    change F v ≤ f p at hv
    by_contra hn
    exact (fin p).2.not_ge (by simpa [F,liftObj,hn] using hv)
  have bnd : S ⊆ Metric.closedBall p.val (2*‖g‖/l) := by
    intro v hv
    let q : V := ⟨v,SD hv⟩
    have hv' : f q ≤ f p := by simpa only [← eqv q] using (show F v ≤ f p from hv)
    have hu := EReal.toReal_le_toReal hv' (fin q).1 (fin p).2.ne
    have hg := growth q
    have op : |g (q.val-p.val)| ≤ ‖g‖ * ‖q.val-p.val‖ := g.le_opNorm _
    have quad : l/2*‖q.val-p.val‖^2 ≤ ‖g‖*‖q.val-p.val‖ := by linarith [(abs_le.mp op).1]
    change dist v p.val ≤ _
    rw [dist_eq_norm]
    change ‖q.val-p.val‖ ≤ _
    apply (le_div_iff₀ hl).2
    by_cases hz : ‖q.val-p.val‖ = 0
    · rw [hz,zero_mul]; exact mul_nonneg (by norm_num) (norm_nonneg _)
    · have pos := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
      by_contra! hbad
      have hprod : 0 < (l/2*‖q.val-p.val‖-‖g‖)*‖q.val-p.val‖ := mul_pos (by linarith) pos
      nlinarith
  have closedF := lift_closed hclosed f hf
  have closedS : IsClosed S := by
    simpa only [S,F,EReal.coe_toReal (fin p).2.ne (fin p).1] using closedF (f p).toReal
  have compactS := (isCompact_closedBall p.val (2*‖g‖/l)).of_isClosed_subset closedS bnd
  have fld : LowerSemicontinuous F := (sourceClosed_iff_lowerSemicontinuous F).1 closedF
  have hmeet : (S ∩ effectiveDomain F).Nonempty := ⟨p.val,pS,by
    change F p.val < ⊤; rw [eqv]; exact (fin p).2⟩
  obtain ⟨z,hz,zm⟩ := source_weierstrass_extended F S fld compactS hmeet
  let z' : V := ⟨z,SD hz⟩
  refine ⟨z',fun q => ?_⟩
  rw [← eqv z', ← eqv q]
  by_cases hq : q.val ∈ S
  · exact zm hq
  · exact (show F z ≤ f p from hz).trans (lt_of_not_ge hq).le

private def ri {X V : Set E} (incl : V ⊆ X) (psi : ℕ → X → ℝ)
    (loss : ℕ → E → EReal) (n : ℕ) (v : V) :=
  psi n ⟨v.val,incl v.property⟩ + ∑ i ∈ range (n+1), (loss i v.val).toReal

private theorem eval_round {X V : Set E} (incl : V ⊆ X) (psi : ℕ → X → ℝ)
    (loss : ℕ → E → EReal) (hint : ℕ → V → ℝ) (n : ℕ)
    (fin : ∀ i ≤ n, ∀ v : V, loss i v.val ≠ ⊥ ∧ loss i v.val ≠ ⊤) (v : V) :
    inclusive incl psi loss n v = (ri incl psi loss n v : EReal) ∧
    forecastError loss hint n v = (((loss n v.val).toReal-hint n v : ℝ) : EReal) ∧
    hinted incl psi loss hint n v =
      ((ri incl psi loss n v - ((loss n v.val).toReal-hint n v) : ℝ) : EReal) := by
  have h₁ := real_prefix loss (n+1) v.val (fun i hi => fin i (by omega) v)
  have h₀ := real_prefix loss n v.val (fun i hi => fin i hi.le v)
  have hl := EReal.coe_toReal (fin n le_rfl v).2 (fin n le_rfl v).1
  refine ⟨?_,?_,?_⟩
  · simp only [inclusive,BanditRL.OnlineBTRL.sourceInclusive,ri,h₁,EReal.coe_add]
  · simp only [forecastError,EReal.coe_sub,hl]
  · simp only [hinted,h₀,← EReal.coe_add,ri,sum_range_succ]
    congr 1
    ring

private theorem min_support_sum {V : Set E} (f b a : V → EReal) (F B : V → ℝ)
    (hf : ∀ v, f v = (F v : EReal)) (hb : ∀ v, b v = (B v : EReal))
    (ha : ∀ v, a v = ((F v-B v : ℝ) : EReal))
    (p : V) (hmin : ∀ q, a p ≤ a q) (g : E →L[ℝ] ℝ) (hs : supports b p g) :
    supports f p g := by
  intro q
  have m := hmin q
  rw [ha,ha,EReal.coe_le_coe_iff] at m
  have s := hs q
  rw [hb,hb,← EReal.coe_add,EReal.coe_le_coe_iff] at s
  rw [hf,hf,← EReal.coe_add,EReal.coe_le_coe_iff]
  linarith

private theorem telescoped_growth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (T : ℕ) (hT : 0 < T) (X V : Set E) (incl : V ⊆ X)
    (hV : V.Nonempty) (hclosedV : IsClosed V) (hconvV : Convex ℝ V)
    (psi : ℕ → X → ℝ) (hint : ℕ → V → ℝ) (loss : ℕ → E → EReal)
    (hnobot : ∀ i < T, ∀ v, loss i v ≠ ⊥)
    (hA : hintedRegular (hinted incl psi loss hint) T)
    (lam : ℕ → ℝ) (hG : inclusiveRegular (inclusive incl psi loss) lam T)
    (x : ℕ → V) (hx : predicts (hinted incl psi loss hint) T x)
    (g : ℕ → E →L[ℝ] ℝ) (hg : ∀ n < T, supports (forecastError loss hint n) (x n) (g n))
    (z u : V) : playedRegret T loss x u ≤ regularizerTerms incl T psi x u +
      sharpTerms T x z g lam + (ri incl psi loss (T-1) z - ri incl psi loss (T-1) u) := by
  let r := fun n (v : V) => psi n ⟨v.val,incl v.property⟩
  let L := fun n (v : V) => (loss n v.val).toReal
  let G := ri incl psi loss
  let y := fun n => if n=T then z else x n
  have hy (n : ℕ) (hn : n<T) : y n = x n := if_neg hn.ne
  have hgrowth (n : ℕ) (hn : n < T) (q : V) :
      G n (x n) - G n q ≤ g n ((x n).val-q.val) - lam n/2*‖(x n).val-q.val‖^2 := by
    have fin (i : ℕ) (hi : i ≤ n) (v : V) : loss i v.val ≠ ⊥ ∧ loss i v.val ≠ ⊤ :=
      ⟨hnobot i (by omega) _,used_finite incl T psi loss hnobot (fun j hj => (hG j hj).2.1) i (by omega) v⟩
    have ev := eval_round incl psi loss hint n fin
    have ss := min_support_sum _ _ _ (G n) (fun v : V => L n v-hint n v)
      (fun v => (ev v).1) (fun v => (ev v).2.1) (fun v => (ev v).2.2) (x n) (hx n hn) (g n) (hg n hn)
    obtain ⟨_,hfin,_,hnl,st⟩ := hG n hn
    have fF (v : V) : inclusive incl psi loss n v ≠ ⊥ ∧ inclusive incl psi loss n v < ⊤ :=
      ⟨by rw [(ev v).1]; exact EReal.coe_ne_bot _,hfin v⟩
    have growth := restricted_growth _ hconvV fF (lam n) hnl st (x n) q (g n) ss
    rw [(ev (x n)).1,(ev q).1,EReal.toReal_coe,EReal.toReal_coe,norm_sub_rev q.val] at growth
    have opp : g n ((x n).val-q.val) = -g n (q.val-(x n).val) := by rw [← map_neg,neg_sub]
    dsimp only [G]
    linarith
  have idn := BanditRL.OnlineCumulativePotential.finite_regret_identity r L x u z T hT
  change (∑ n ∈ range T, (L n (y n)-L n u)) = r (T-1) u - r 0 (y 0) +
    (∑ n ∈ range T, (G n (y n)-G n (y (n+1)))) +
    (∑ n ∈ range (T-1), (r n (y (n+1))-r (n+1) (y (n+1)))) +
    G (T-1) z - G (T-1) u at idn
  have move : (∑ n ∈ range T, (G n (y n)-G n (y (n+1)))) ≤ sharpTerms T x z g lam := by
    apply Finset.sum_le_sum
    intro n hn
    rw [hy n (mem_range.mp hn)]
    exact hgrowth n (mem_range.mp hn) (y (n+1))
  have reg : (∑ n ∈ range T, (L n (y n)-L n u)) = playedRegret T loss x u := by
    unfold playedRegret
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun n hn => by rw [hy n (mem_range.mp hn)])
  have drift : (∑ n ∈ range (T-1), (r n (y (n+1))-r (n+1) (y (n+1)))) =
      ∑ n ∈ range (T-1), (r n (x (n+1))-r (n+1) (x (n+1))) := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [hy (n+1) (by have := mem_range.mp hn; omega)]
  rw [reg,drift,hy 0 hT] at idn
  change _ ≤ (r (T-1) u-r 0 (x 0) + _) + _ + (G (T-1) z-G (T-1) u)
  linarith

private theorem restricted_min_growth {V : Set E} (f : V → EReal) (cv : Convex ℝ V)
    (fin : ∀ p, f p ≠ ⊥ ∧ f p < ⊤) (l : ℝ) (hl : 0 ≤ l)
    (hs : restrictedStrong f (normSeminorm ℝ E) l)
    (p q : V) (m : ∀ v : V, f p ≤ f v) :
    (f p).toReal + l/2*‖q.val-p.val‖^2 ≤ (f q).toReal := by
  obtain ⟨hP,hD⟩ := lift_data f ⟨p,p.property⟩ fin
  have strong : ∀ x ∈ V, ∀ y ∈ V, ∀ a : ℝ, 0 < a → a < 1 →
      liftObj f (a • x + (1-a) • y) ≤
        (a:EReal)*liftObj f x + ((1-a:ℝ):EReal)*liftObj f y -
          ((l/2*a*(1-a)*‖x-y‖^2 : ℝ) : EReal) := by
    intro x hx y hy a ha ha1
    have hz := cv hx hy ha.le (sub_nonneg.mpr ha1.le) (by ring)
    simpa only [liftObj,dif_pos hx,dif_pos hy,dif_pos hz] using hs ⟨x,hx⟩ ⟨y,hy⟩ a ha ha1 hz
  have hm : IsMinOn (liftObj f) V p.val := by
    intro v hv
    change liftObj f p.val ≤ liftObj f v
    simpa only [liftObj,dif_pos p.property,dif_pos hv] using m ⟨v,hv⟩
  have h := stronglyConvex_minimum_growth (liftObj f) V l hP cv (hD.symm ▸ Subset.rfl)
    hl strong p p.property hm q q.property
  simpa only [liftObj,dif_pos p.property,dif_pos q.property] using h


theorem optimistic_round_unique
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (T : ℕ) (hT : 0 < T) (X V : Set E) (incl : V ⊆ X)
    (hV : V.Nonempty) (hclosedV : IsClosed V) (hconvV : Convex ℝ V)
    (psi : ℕ → X → ℝ) (hint : ℕ → V → ℝ) (loss : ℕ → E → EReal)
    (hnobot : ∀ i < T, ∀ v, loss i v ≠ ⊥)
    (hA : hintedRegular (hinted incl psi loss hint) T) :
    ∀ n < T, ∃! p : V, ∀ q : V, hinted incl psi loss hint n p ≤ hinted incl psi loss hint n q := by
  intro n hn
  let f := hinted incl psi loss hint n
  let H := liftObj f
  obtain ⟨cl,fin,supp,N,sep,μ,hμ,hs⟩ := hA n hn
  obtain ⟨l,hl,s⟩ := display_strong sep hμ hs
  have hf (v : V) : f v ≠ ⊥ ∧ f v < ⊤ := ⟨hinted_bot incl psi loss hint T hnobot n hn v,fin v⟩
  obtain ⟨hP,hD⟩ := lift_data f hV hf
  change effectiveDomain H = V at hD
  have val (v : V) : H v.val = f v := by simp [H,liftObj,v.property]
  have st : ∀ p ∈ effectiveDomain H, ∀ q ∈ effectiveDomain H, ∀ a : ℝ, 0<a → a<1 →
      H (a • p + (1-a) • q) ≤ (a:EReal)*H p + ((1-a:ℝ):EReal)*H q -
          ((l/2*a*(1-a)*‖p-q‖^2 : ℝ) : EReal) := by
    rw [hD]
    intro p hp q hq a ha ha1
    have hz := hconvV hp hq ha.le (sub_nonneg.mpr ha1.le) (by ring)
    simpa only [H,liftObj,dif_pos hp,dif_pos hq,dif_pos hz] using s ⟨p,hp⟩ ⟨q,hq⟩ a ha ha1 hz
  let d := Module.finrank ℝ E
  let e : E ≃ₗ[ℝ] EuclideanSpace ℝ (Fin d) := LinearEquiv.ofFinrankEq _ _ finrank_euclideanSpace_fin.symm
  obtain ⟨p,hp⟩ := hV
  let p' : V := ⟨p,hp⟩
  obtain ⟨g,hg⟩ := supp p'
  let L : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := g.comp e.symm.toLinearMap.toContinuousLinearMap
  have coord : {v : E | (SourceSubdifferential (fun u => H (e.symm u)) (e v)).Nonempty}.Nonempty := by
    refine ⟨p,(InnerProductSpace.toDual ℝ _).symm L,?_⟩
    intro y
    dsimp only
    rw [e.symm_apply_apply,InnerProductSpace.toDual_symm_apply]
    have he : L (y-e p) = g (e.symm y-p) := by
      change g (e.symm (y-e p)) = _
      rw [map_sub,e.symm_apply_apply]
    rw [he]
    by_cases hy : e.symm y ∈ V
    · simpa only [H,liftObj,dif_pos hp,dif_pos hy,p'] using hg ⟨_,hy⟩
    · simp [H,liftObj,hy]
  obtain ⟨z,⟨hz,hm⟩,hu⟩ := stronglyConvex_existsUnique_minimizer d e H l hP
    (lift_closed hclosedV f cl) hl st coord
  let z' : V := ⟨z,hD ▸ hz⟩
  refine ⟨z',fun q => by change f z' ≤ f q; rw [← val z',← val q]; exact hm q.val,?_⟩
  intro q hq
  apply Subtype.ext
  apply hu q.val
  refine ⟨hD.symm ▸ q.property,fun v => ?_⟩
  by_cases hv : v ∈ V
  · simpa only [f,H,liftObj,dif_pos q.property,dif_pos hv] using hq ⟨v,hv⟩
  · simp [H,liftObj,hv]

theorem zero_hint_terminal_attained
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (T : ℕ) (hT : 0 < T) (X V : Set E) (incl : V ⊆ X)
    (hV : V.Nonempty) (hclosedV : IsClosed V) (hconvV : Convex ℝ V)
    (psi : ℕ → X → ℝ) (hint : ℕ → V → ℝ) (loss : ℕ → E → EReal)
    (hnobot : ∀ i < T, ∀ v, loss i v ≠ ⊥)
    (hA : hintedRegular (hinted incl psi loss hint) T)
    (lam : ℕ → ℝ) (hG : inclusiveRegular (inclusive incl psi loss) lam T)
    (x : ℕ → V) (hx : predicts (hinted incl psi loss hint) T x)
    (hsupp : ∀ n < T, ∃ g : E →L[ℝ] ℝ, supports (forecastError loss hint n) (x n) g) :
    ∃ z : V, ∀ q : V, inclusive incl psi loss (T-1) z ≤ inclusive incl psi loss (T-1) q := by
  let n := T-1
  have hn : n < T := by dsimp [n]; omega
  let F := inclusive incl psi loss n
  let a := hinted incl psi loss hint n
  let p := x n
  have fin (i : ℕ) (hi : i ≤ n) (v : V) : loss i v.val ≠ ⊥ ∧ loss i v.val ≠ ⊤ :=
    ⟨hnobot i (by omega) _,used_finite incl T psi loss hnobot (fun j hj => (hG j hj).2.1) i (by omega) v⟩
  have ev := eval_round incl psi loss hint n fin
  obtain ⟨g,hg⟩ := hsupp n hn
  obtain ⟨_,afin,_,N,sep,μ,hμ,as⟩ := hA n hn
  obtain ⟨l,hl,st⟩ := display_strong sep hμ as
  have fa (v : V) : a v ≠ ⊥ ∧ a v < ⊤ := ⟨hinted_bot _ _ _ _ _ hnobot _ hn _,afin v⟩
  have fF (v : V) : F v ≠ ⊥ ∧ F v < ⊤ := by
    change inclusive incl psi loss n v ≠ ⊥ ∧ _
    rw [(ev v).1]
    exact ⟨EReal.coe_ne_bot _, (hG n hn).2.1 v⟩
  apply quadratic_attainment hclosedV F (hG n hn).1 fF p g l hl
  intro q
  have grow := restricted_min_growth a hconvV fa l hl.le st p q (hx n hn)
  have err := hg q
  change forecastError loss hint n p + _ ≤ _ at err
  rw [(ev p).2.1,(ev q).2.1,← EReal.coe_add,EReal.coe_le_coe_iff] at err
  change (hinted incl psi loss hint n p).toReal + _ ≤ (hinted incl psi loss hint n q).toReal at grow
  rw [(ev p).2.2,(ev q).2.2] at grow
  simp only [EReal.toReal_coe] at grow
  change (inclusive incl psi loss n p).toReal + _ + _ ≤ (inclusive incl psi loss n q).toReal
  rw [(ev p).1,(ev q).1]
  simp only [EReal.toReal_coe]
  linarith

theorem zero_hint_sharp_regret
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (T : ℕ) (hT : 0 < T) (X V : Set E) (incl : V ⊆ X)
    (hV : V.Nonempty) (hclosedV : IsClosed V) (hconvV : Convex ℝ V)
    (psi : ℕ → X → ℝ) (hint : ℕ → V → ℝ) (loss : ℕ → E → EReal)
    (hnobot : ∀ i < T, ∀ v, loss i v ≠ ⊥)
    (hA : hintedRegular (hinted incl psi loss hint) T)
    (lam : ℕ → ℝ) (hG : inclusiveRegular (inclusive incl psi loss) lam T)
    (x : ℕ → V) (hx : predicts (hinted incl psi loss hint) T x)
    (g : ℕ → E →L[ℝ] ℝ) (hg : ∀ n < T, supports (forecastError loss hint n) (x n) (g n))
    (z : V) (hz : ∀ q : V, inclusive incl psi loss (T-1) z ≤ inclusive incl psi loss (T-1) q) (u : V) :
    playedRegret T loss x u ≤ regularizerTerms incl T psi x u + sharpTerms T x z g lam := by
  have hn : T-1 < T := by omega
  have fin (i : ℕ) (hi : i ≤ T-1) (v : V) : loss i v.val ≠ ⊥ ∧ loss i v.val ≠ ⊤ :=
    ⟨hnobot i (by omega) _,used_finite incl T psi loss hnobot (fun j hj => (hG j hj).2.1) i (by omega) v⟩
  have ev := eval_round incl psi loss hint (T-1) fin
  have h := telescoped_growth T hT X V incl hV hclosedV hconvV psi hint loss hnobot hA lam hG x hx g hg z u
  have b := hz u
  rw [(ev z).1,(ev u).1,EReal.coe_le_coe_iff] at b
  linarith

theorem positive_modulus_young_regret
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (T : ℕ) (hT : 0 < T) (X V : Set E) (incl : V ⊆ X)
    (hV : V.Nonempty) (hclosedV : IsClosed V) (hconvV : Convex ℝ V)
    (psi : ℕ → X → ℝ) (hint : ℕ → V → ℝ) (loss : ℕ → E → EReal)
    (hnobot : ∀ i < T, ∀ v, loss i v ≠ ⊥)
    (hA : hintedRegular (hinted incl psi loss hint) T)
    (lam : ℕ → ℝ) (hG : inclusiveRegular (inclusive incl psi loss) lam T)
    (x : ℕ → V) (hx : predicts (hinted incl psi loss hint) T x)
    (g : ℕ → E →L[ℝ] ℝ) (hg : ∀ n < T, supports (forecastError loss hint n) (x n) (g n))
    (hpos : ∀ n < T, 0 < lam n) (u : V) :
    playedRegret T loss x u ≤ regularizerTerms incl T psi x u +
      ∑ n ∈ range T, ‖g n‖^2 / (2*lam n) := by
  obtain ⟨z,hz⟩ := zero_hint_terminal_attained T hT X V incl hV hclosedV hconvV psi hint loss hnobot hA lam hG x hx
    (fun n hn => ⟨g n,hg n hn⟩)
  have sharp := zero_hint_sharp_regret T hT X V incl hV hclosedV hconvV psi hint loss hnobot hA lam hG x hx g hg z hz u
  apply sharp.trans
  apply add_le_add_right
  apply Finset.sum_le_sum
  intro n hn
  let v := (x n).val-(nextPlay T x z n).val
  change g n v - lam n/2*‖v‖^2 ≤ ‖g n‖^2 / (2 * lam n)
  have pos := hpos n (mem_range.mp hn)
  have op : g n v ≤ ‖g n‖ * ‖v‖ := (le_abs_self _).trans ((g n).le_opNorm v)
  apply (le_div_iff₀ (by positivity : 0 < 2 * lam n)).2
  have op' := mul_le_mul_of_nonneg_right op pos.le
  nlinarith only [op',sq_nonneg (lam n*‖v‖-‖g n‖)]

theorem repeated_hint_residual_regret
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (T : ℕ) (hT : 0 < T) (X V : Set E) (incl : V ⊆ X)
    (hV : V.Nonempty) (hclosedV : IsClosed V) (hconvV : Convex ℝ V)
    (psi : ℕ → X → ℝ) (hint : ℕ → V → ℝ) (loss : ℕ → E → EReal)
    (hnobot : ∀ i < T, ∀ v, loss i v ≠ ⊥)
    (hA : hintedRegular (hinted incl psi loss hint) T)
    (lam : ℕ → ℝ) (hG : inclusiveRegular (inclusive incl psi loss) lam T)
    (x : ℕ → V) (hx : predicts (hinted incl psi loss hint) T x)
    (g : ℕ → E →L[ℝ] ℝ) (hg : ∀ n < T, supports (forecastError loss hint n) (x n) (g n))
    (z : V) (hz : ∀ q : V,
      inclusive incl psi loss (T-1) z + (hint (T-1) z : EReal) ≤
      inclusive incl psi loss (T-1) q + (hint (T-1) q : EReal)) (u : V) :
    playedRegret T loss x u ≤ regularizerTerms incl T psi x u + sharpTerms T x z g lam + (hint (T-1) u - hint (T-1) z) := by
  have hn : T-1 < T := by omega
  have fin (i : ℕ) (hi : i ≤ T-1) (v : V) : loss i v.val ≠ ⊥ ∧ loss i v.val ≠ ⊤ :=
    ⟨hnobot i (by omega) _,used_finite incl T psi loss hnobot (fun j hj => (hG j hj).2.1) i (by omega) v⟩
  have ev := eval_round incl psi loss hint (T-1) fin
  have h := telescoped_growth T hT X V incl hV hclosedV hconvV psi hint loss hnobot hA lam hG x hx g hg z u
  have b := hz u
  rw [(ev z).1,(ev u).1,← EReal.coe_add,← EReal.coe_add,EReal.coe_le_coe_iff] at b
  linarith

private theorem select_hint_prefix
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (T : ℕ) (hT : 0 < T) (X V : Set E) (incl : V ⊆ X)
    (hV : V.Nonempty) (hclosedV : IsClosed V) (hconvV : Convex ℝ V)
    (psi : ℕ → X → ℝ) (hint : ℕ → V → ℝ) (loss : ℕ → E → EReal)
    (hnobot : ∀ i < T, ∀ v, loss i v ≠ ⊥)
    (hA : hintedRegular (hinted incl psi loss hint) T) :
    ∃ x : ℕ → V, predicts (hinted incl psi loss hint) T x ∧
      ∀ n < T, ∀ (psi' : ℕ → X → ℝ) (loss' : ℕ → E → EReal) (hint' : ℕ → V → ℝ),
      (∀ v : V, psi' n ⟨v.val,incl v.property⟩ = psi n ⟨v.val,incl v.property⟩) →
      (∀ v : V, hint' n v = hint n v) →
      (∀ i < n, ∀ v : V, loss' i v.val = loss i v.val) →
      ∀ z : V, (∀ q, hinted incl psi' loss' hint' n z ≤ hinted incl psi' loss' hint' n q) → z = x n := by
  classical
  have all := optimistic_round_unique T hT X V incl hV hclosedV hconvV psi hint loss hnobot hA
  obtain ⟨w,hw⟩ := hV
  let x : ℕ → V := fun n => if hn : n < T then Classical.choose (all n hn) else ⟨w,hw⟩
  have spec (n : ℕ) (hn : n < T) := Classical.choose_spec (all n hn)
  refine ⟨x,fun n hn => ?_,?_⟩
  · simpa only [x,dif_pos hn] using (spec n hn).1
  · intro n hn psi' loss' hint' hp hh hl z hz
    have same (v : V) : hinted incl psi' loss' hint' n v = hinted incl psi loss hint n v := by
      simp only [hinted,hp v,hh v]
      rw [Finset.sum_congr rfl (fun i hi => hl i (Finset.mem_range.mp hi) v)]
    change z = (if h : n < T then Classical.choose (all n h) else ⟨w,hw⟩)
    rw [dif_pos hn]
    exact (spec n hn).2 z (fun q => by simpa only [same] using hz q)

end BanditRL.OnlineOptimistic
