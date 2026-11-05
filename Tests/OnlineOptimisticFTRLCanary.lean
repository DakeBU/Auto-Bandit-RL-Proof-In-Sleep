import BanditRLProof.OnlineOptimisticFTRL
import Mathlib.Analysis.Normed.Lp.ProdLp

noncomputable section
attribute [local instance] Classical.propDecidable
open Set Finset BanditRL.OnlineOptimistic
namespace BanditRL.OnlineOptimisticCanary

structure Inputs (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  T : ℕ
  V : Set E
  psi : ℕ → ↥(Set.univ : Set E) → ℝ
  hint : ℕ → V → ℝ
  loss : ℕ → E → EReal
  lam : ℕ → ℝ
  x : ℕ → V
  g : ℕ → E →L[ℝ] ℝ
  u : V

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
abbrev inc (m : Inputs E) : m.V ⊆ Set.univ := Set.subset_univ _
abbrev r (m : Inputs E) := playedRegret m.T m.loss m.x m.u
abbrev base (m : Inputs E) := regularizerTerms (inc m) m.T m.psi m.x m.u
abbrev s (m : Inputs E) (z : m.V) := base m + sharpTerms m.T m.x z m.g m.lam
abbrev y (m : Inputs E) := base m + ∑ n ∈ range m.T, ‖m.g n‖^2 / (2*m.lam n)
abbrev repeated (m : Inputs E) (z : m.V) := s m z + (m.hint (m.T-1) m.u - m.hint (m.T-1) z)
abbrev A (m : Inputs E) := hinted (inc m) m.psi m.loss m.hint
abbrev G (m : Inputs E) := inclusive (inc m) m.psi m.loss
abbrev allReal (v : ℝ) : (Set.univ : Set ℝ) := ⟨v, Set.mem_univ _⟩
abbrev slope (a : ℝ) : ℝ →L[ℝ] ℝ := a • ContinuousLinearMap.id ℝ ℝ

def repeatLast : Inputs ℝ where
  T := 1
  V := Set.univ
  psi := fun _ v => v.val^2/2
  hint := fun _ v => (v.val-1)^2/2
  loss := fun _ v => (((v-1)^2/2 : ℝ) : EReal)
  lam := fun _ => 2
  x := fun _ => allReal (1/2)
  g := fun _ => 0
  u := allReal (1/2)
abbrev repeatZ : repeatLast.V := allReal (1/2)
abbrev repeatZ' : repeatLast.V := allReal (2/3)

def driftingTwo : Inputs ℝ where
  T := 2
  V := Set.univ
  psi := fun n v => v.val^2/2 + (if n=0 then 0 else 2*v.val)
  hint := fun n v => if n=0 then 0 else -v.val
  loss := fun n v => ((if n=0 then v else 2*v : ℝ) : EReal)
  lam := fun _ => 1
  x := fun n => allReal (if n=0 then 0 else -2)
  g := fun n => slope (if n=0 then 1 else 3)
  u := allReal (-5)
abbrev driftZ : driftingTwo.V := allReal (-5)
abbrev term (m : Inputs E) (z : m.V) (n : ℕ) : ℝ :=
  let v := (m.x n).val - (nextPlay m.T m.x z n).val
  m.g n v - m.lam n/2 * ‖v‖^2

abbrev Pair := ℝ × ℝ
def box : Set Pair := (Set.Icc (-2 : ℝ) 2) ×ˢ (Set.Icc (-2 : ℝ) 2)
def quad (w : Pair) : ℝ := (9*w.1^2-6*w.1*w.2+9*w.2^2)/8
def euc : Seminorm ℝ Pair :=
  (normSeminorm ℝ (WithLp 2 Pair)).comp (WithLp.linearEquiv 2 ℝ Pair).symm.toLinearMap
def boxFunctional : Pair →L[ℝ] ℝ :=
  ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ
def dualBox : Inputs Pair where
  T := 1
  V := box
  psi := fun _ v => quad v.val/2
  hint := fun _ _ => 0
  loss := fun _ w => if w ∈ box then ((w.1+w.2 : ℝ) : EReal) else ⊤
  lam := fun _ => 1
  x := fun _ => ⟨(0,0), by norm_num [box, Set.mem_prod]⟩
  g := fun _ => boxFunctional
  u := ⟨(-4/3,-4/3), by norm_num [box, Set.mem_prod]⟩

def declaredZero : Inputs ℝ where
  T := 1
  V := Set.univ
  psi := fun _ v => v.val^2/2
  hint := fun _ _ => 0
  loss := fun _ v => (v : EReal)
  lam := fun _ => 0
  x := fun _ => allReal 0
  g := fun _ => slope 1
  u := allReal (-1)
def declaredOne : Inputs ℝ := { declaredZero with lam := fun _ => 1 }

def flatHalfLine : Inputs ℝ where
  T := 1
  V := Set.Ici 0
  psi := fun _ v => v.val^2/2
  hint := fun _ _ => 0
  loss := fun _ q => if 0 ≤ q then (((max (q-1) 0)^2/2-q^2/2 : ℝ) : EReal) else ⊤
  lam := fun _ => 0
  x := fun _ => ⟨(0 : ℝ), by change (0 : ℝ) ≤ (0 : ℝ); exact le_rfl⟩
  g := fun _ => slope (-1)
  u := ⟨1, by change (0 : ℝ) ≤ 1; norm_num⟩
abbrev flatZero : flatHalfLine.V := ⟨0, by change (0 : ℝ) ≤ 0; exact le_rfl⟩
abbrev flatOne : flatHalfLine.V := ⟨1, by change (0 : ℝ) ≤ 1; norm_num⟩
abbrev flatMin (z : flatHalfLine.V) := ∀ q : flatHalfLine.V, G flatHalfLine 0 z ≤ G flatHalfLine 0 q

open BanditRL.OnlineConvex

private structure Facts [FiniteDimensional ℝ E] (m : Inputs E) : Prop where
  pos : 0 < m.T
  closed : IsClosed m.V
  cv : Convex ℝ m.V
  bot : ∀ n < m.T, ∀ v, m.loss n v ≠ ⊥
  aReg : hintedRegular (A m) m.T
  gReg : inclusiveRegular (G m) m.lam m.T
  play : predicts (A m) m.T m.x
  supp : ∀ n < m.T, supports (forecastError m.loss m.hint n) (m.x n) (m.g n)

private def poly (k b c t : ℝ) := k/2*t^2+b*t+c
private abbrev Reg {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {V : Set F}
    (f : V → EReal) := SourceClosed f ∧ (∀ v, f v < ⊤) ∧ (∀ v, ∃ g, supports f v g)
private theorem scalar_shape {V : Set ℝ} (f : V → EReal) (k b c l : ℝ)
    (hk : 0 ≤ k) (hl : l ≤ k) (eq : ∀ v, f v = ((poly k b c v.val : ℝ) : EReal)) :
    Reg f ∧ restrictedStrong f (normSeminorm ℝ ℝ) l := by
  refine ⟨⟨?_,fun v => by rw [eq];exact EReal.coe_lt_top _,?_⟩,?_⟩
  · intro t
    have he : {v : V | f v ≤ (t:EReal)} = {v : V | poly k b c v.val ≤ t} := by ext v; simp [eq]
    rw [he]
    exact isClosed_le (by unfold poly; fun_prop) continuous_const
  · intro p
    refine ⟨slope (k*p.val+b),fun q => ?_⟩
    rw [eq,eq,← EReal.coe_add,EReal.coe_le_coe_iff]
    change poly k b c p.val + (k*p.val+b)*(q.val-p.val) ≤ poly k b c q.val
    unfold poly
    nlinarith [mul_nonneg hk (sq_nonneg (q.val-p.val))]
  · intro p q a ha ha1 hz
    simp only [eq,← EReal.coe_mul,← EReal.coe_add,← EReal.coe_sub,EReal.coe_le_coe_iff]
    change poly k b c (a*p.val+(1-a)*q.val) ≤ a*poly k b c p.val+(1-a)*poly k b c q.val-l/2*a*(1-a)*‖p.val-q.val‖^2
    rw [Real.norm_eq_abs,sq_abs]
    unfold poly
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (sub_nonneg.mpr hl) ha.le) (sub_nonneg.mpr ha1.le)) (sq_nonneg (p.val-q.val))]
private theorem scalar_A {V : Set ℝ} (f : V → EReal) (k b c : ℝ) (hk : 0 < k)
    (eq : ∀ v, f v = ((poly k b c v.val : ℝ) : EReal)) :
    SourceClosed f ∧ (∀ v, f v < ⊤) ∧ (∀ v, ∃ g, supports f v g) ∧
      ∃ N : Seminorm ℝ ℝ, (∀ v, N v = 0 → v = 0) ∧ ∃ μ, 0 < μ ∧ restrictedStrong f N μ := by
  obtain ⟨⟨a,b',c'⟩,s⟩ := scalar_shape f k b c k hk.le le_rfl eq
  exact ⟨a,b',c',normSeminorm ℝ ℝ,fun v hv => norm_eq_zero.mp (show ‖v‖ = 0 from hv),k,hk,s⟩
private theorem scalar_G {V : Set ℝ} (f : V → EReal) (k b c l : ℝ) (hl : 0 ≤ l) (hk : l ≤ k)
    (eq : ∀ v, f v = ((poly k b c v.val : ℝ) : EReal)) :
    SourceClosed f ∧ (∀ v, f v < ⊤) ∧ (∀ v, ∃ g, supports f v g) ∧ 0 ≤ l ∧ restrictedStrong f (normSeminorm ℝ ℝ) l := by
  obtain ⟨⟨a,b',c'⟩,s⟩ := scalar_shape f k b c l (hl.trans hk) hk eq
  exact ⟨a,b',c',hl,s⟩

private theorem poly_min {V : Set ℝ} (f : V → EReal) (p : V) (k b c : ℝ)
    (h : ∀ v, f v = ((poly k b c v.val : ℝ) : EReal)) (hk : 0 ≤ k) (stat : k*p.val+b=0) :
    ∀ q, f p ≤ f q := by
  intro q
  rw [h,h,EReal.coe_le_coe_iff]
  have z := congrArg (fun x : ℝ => x*(q.val-p.val)) stat
  dsimp at z
  unfold poly
  nlinarith [mul_nonneg hk (sq_nonneg (q.val-p.val))]

@[local simp] private theorem repeatLast_TEq  : repeatLast.T = 1 := rfl
@[local simp] private theorem repeatLast_psiEq (n:ℕ)(v:(Set.univ:Set ℝ)) : repeatLast.psi n v = v.val^2/2 := rfl
@[local simp] private theorem repeatLast_hintEq (n:ℕ)(v:repeatLast.V) : repeatLast.hint n v = (v.val-1)^2/2 := rfl
@[local simp] private theorem repeatLast_lamEq (n:ℕ) : repeatLast.lam n = 2 := rfl
@[local simp] private theorem repeatLast_gEq (n:ℕ) : repeatLast.g n = 0 := rfl
@[local simp] private theorem repeatLast_lossEq (n:ℕ)(v:ℝ) : repeatLast.loss n v = (((v-1)^2/2 : ℝ) : EReal) := rfl
@[local simp] private theorem repeatLast_xEq (n:ℕ) : (repeatLast.x n).val = (1/2) := rfl
@[local simp] private theorem repeatLast_uEq  : (repeatLast.u).val = (1/2) := rfl
@[local simp] private theorem driftingTwo_TEq  : driftingTwo.T = 2 := rfl
@[local simp] private theorem driftingTwo_psiEq (n:ℕ)(v:(Set.univ:Set ℝ)) : driftingTwo.psi n v = v.val^2/2 + (if n=0 then 0 else 2*v.val) := rfl
@[local simp] private theorem driftingTwo_hintEq (n:ℕ)(v:driftingTwo.V) : driftingTwo.hint n v = if n=0 then 0 else -v.val := rfl
@[local simp] private theorem driftingTwo_lamEq (n:ℕ) : driftingTwo.lam n = 1 := rfl
@[local simp] private theorem driftingTwo_gEq (n:ℕ) : driftingTwo.g n = slope (if n=0 then 1 else 3) := rfl
@[local simp] private theorem driftingTwo_lossEq (n:ℕ)(v:ℝ) : driftingTwo.loss n v = ((if n=0 then v else 2*v : ℝ) : EReal) := rfl
@[local simp] private theorem driftingTwo_xEq (n:ℕ) : (driftingTwo.x n).val = (if n=0 then 0 else -2) := rfl
@[local simp] private theorem driftingTwo_uEq  : (driftingTwo.u).val = (-5) := rfl
@[local simp] private theorem declaredZero_TEq  : declaredZero.T = 1 := rfl
@[local simp] private theorem declaredZero_psiEq (n:ℕ)(v:(Set.univ:Set ℝ)) : declaredZero.psi n v = v.val^2/2 := rfl
@[local simp] private theorem declaredZero_hintEq (n:ℕ)(v:declaredZero.V) : declaredZero.hint n v = 0 := rfl
@[local simp] private theorem declaredZero_lamEq (n:ℕ) : declaredZero.lam n = 0 := rfl
@[local simp] private theorem declaredZero_gEq (n:ℕ) : declaredZero.g n = slope 1 := rfl
@[local simp] private theorem declaredZero_lossEq (n:ℕ)(v:ℝ) : declaredZero.loss n v = (v : EReal) := rfl
@[local simp] private theorem declaredZero_xEq (n:ℕ) : (declaredZero.x n).val = 0 := rfl
@[local simp] private theorem declaredZero_uEq  : (declaredZero.u).val = (-1) := rfl
@[local simp] private theorem declaredOne_TEq  : declaredOne.T = 1 := rfl
@[local simp] private theorem declaredOne_psiEq (n:ℕ)(v:(Set.univ:Set ℝ)) : declaredOne.psi n v = v.val^2/2 := rfl
@[local simp] private theorem declaredOne_hintEq (n:ℕ)(v:declaredOne.V) : declaredOne.hint n v = 0 := rfl
@[local simp] private theorem declaredOne_lamEq (n:ℕ) : declaredOne.lam n = 1 := rfl
@[local simp] private theorem declaredOne_gEq (n:ℕ) : declaredOne.g n = slope 1 := rfl
@[local simp] private theorem declaredOne_lossEq (n:ℕ)(v:ℝ) : declaredOne.loss n v = (v : EReal) := rfl
@[local simp] private theorem declaredOne_xEq (n:ℕ) : (declaredOne.x n).val = 0 := rfl
@[local simp] private theorem declaredOne_uEq  : (declaredOne.u).val = (-1) := rfl
@[local simp] private theorem flatHalfLine_TEq  : flatHalfLine.T = 1 := rfl
@[local simp] private theorem flatHalfLine_psiEq (n:ℕ)(v:(Set.univ:Set ℝ)) : flatHalfLine.psi n v = v.val^2/2 := rfl
@[local simp] private theorem flatHalfLine_hintEq (n:ℕ)(v:flatHalfLine.V) : flatHalfLine.hint n v = 0 := rfl
@[local simp] private theorem flatHalfLine_lamEq (n:ℕ) : flatHalfLine.lam n = 0 := rfl
@[local simp] private theorem flatHalfLine_gEq (n:ℕ) : flatHalfLine.g n = slope (-1) := rfl
@[local simp] private theorem flatHalfLine_lossEq (n:ℕ)(v:ℝ) : flatHalfLine.loss n v = if 0 ≤ v then (((max (v-1) 0)^2/2-v^2/2 : ℝ) : EReal) else ⊤ := rfl
@[local simp] private theorem flatHalfLine_xEq (n:ℕ) : (flatHalfLine.x n).val = (0 : ℝ) := rfl
@[local simp] private theorem flatHalfLine_uEq  : (flatHalfLine.u).val = 1 := rfl
@[local simp] private theorem dualBox_TEq  : dualBox.T = 1 := rfl
@[local simp] private theorem dualBox_psiEq (n:ℕ)(v:(Set.univ:Set Pair)) : dualBox.psi n v = quad v.val/2 := rfl
@[local simp] private theorem dualBox_hintEq (n:ℕ)(v:dualBox.V) : dualBox.hint n v = 0 := rfl
@[local simp] private theorem dualBox_lamEq (n:ℕ) : dualBox.lam n = 1 := rfl
@[local simp] private theorem dualBox_gEq (n:ℕ) : dualBox.g n = boxFunctional := rfl
@[local simp] private theorem dualBox_lossEq (n:ℕ)(v:Pair) : dualBox.loss n v = if v ∈ box then ((v.1+v.2 : ℝ) : EReal) else ⊤ := rfl
@[local simp] private theorem dualBox_xEq (n:ℕ) : (dualBox.x n).val = (0,0) := rfl
@[local simp] private theorem dualBox_uEq  : (dualBox.u).val = (-4/3,-4/3) := rfl

private theorem repeatLast_A0 (w : repeatLast.V) : A repeatLast 0 w = ((poly (2) (-1) ((1/2)) w.val : ℝ) : EReal) := by
  simp only [A,G,hinted,inclusive,BanditRL.OnlineBTRL.sourceInclusive,Finset.sum_range_succ,Finset.sum_range_zero,add_zero,zero_add,repeatLast_TEq,repeatLast_psiEq,repeatLast_hintEq,repeatLast_lamEq,repeatLast_gEq,repeatLast_lossEq,repeatLast_xEq,repeatLast_uEq,ite_true,ite_false,  Nat.reduceAdd, ← EReal.coe_add, EReal.coe_zero]
  first | (apply congrArg (fun t : ℝ => (t:EReal));simp [poly] <;> ring) | rfl

private theorem repeatLast_G0 (w : repeatLast.V) : G repeatLast 0 w = ((poly (2) (-1) ((1/2)) w.val : ℝ) : EReal) := by
  simp only [A,G,hinted,inclusive,BanditRL.OnlineBTRL.sourceInclusive,Finset.sum_range_succ,Finset.sum_range_zero,add_zero,zero_add,repeatLast_TEq,repeatLast_psiEq,repeatLast_hintEq,repeatLast_lamEq,repeatLast_gEq,repeatLast_lossEq,repeatLast_xEq,repeatLast_uEq,ite_true,ite_false,  Nat.reduceAdd, ← EReal.coe_add, EReal.coe_zero]
  first | (apply congrArg (fun t : ℝ => (t:EReal));simp [poly] <;> ring) | rfl

private theorem repeatLast_facts : Facts repeatLast := by
  refine ⟨by decide,isClosed_univ,convex_univ,?_,?_,?_,?_,?_⟩
  · intro n hn v; exact EReal.coe_ne_bot _
  · intro n hn
    change n < 1 at hn
    interval_cases n
    · exact scalar_A _ (2) (-1) ((1/2)) (by norm_num) repeatLast_A0
  · intro n hn
    change n < 1 at hn
    interval_cases n
    · exact scalar_G _ (2) (-1) ((1/2)) 2 (by norm_num) (by norm_num) repeatLast_G0
  · intro n hn
    change n < 1 at hn
    interval_cases n
    · exact poly_min _ _ (2) (-1) ((1/2)) repeatLast_A0 (by norm_num) (by norm_num [repeatLast,repeatZ,repeatZ',driftZ,allReal,poly,slope,Real.norm_eq_abs])
  · intro n hn
    change n < 1 at hn
    interval_cases n
    · intro w; norm_num [forecastError,repeatLast,slope,allReal,← EReal.coe_sub,← EReal.coe_add,EReal.coe_le_coe_iff] <;> first | linarith | ring_nf

private theorem driftingTwo_A0 (w : driftingTwo.V) : A driftingTwo 0 w = ((poly (1) (0) (0) w.val : ℝ) : EReal) := by
  simp only [A,G,hinted,inclusive,BanditRL.OnlineBTRL.sourceInclusive,Finset.sum_range_succ,Finset.sum_range_zero,add_zero,zero_add,driftingTwo_TEq,driftingTwo_psiEq,driftingTwo_hintEq,driftingTwo_lamEq,driftingTwo_gEq,driftingTwo_lossEq,driftingTwo_xEq,driftingTwo_uEq,ite_true,ite_false,  Nat.reduceAdd, ← EReal.coe_add, EReal.coe_zero]
  first | (apply congrArg (fun t : ℝ => (t:EReal));simp [poly] <;> ring) | rfl

private theorem driftingTwo_G0 (w : driftingTwo.V) : G driftingTwo 0 w = ((poly (1) (1) (0) w.val : ℝ) : EReal) := by
  simp only [A,G,hinted,inclusive,BanditRL.OnlineBTRL.sourceInclusive,Finset.sum_range_succ,Finset.sum_range_zero,add_zero,zero_add,driftingTwo_TEq,driftingTwo_psiEq,driftingTwo_hintEq,driftingTwo_lamEq,driftingTwo_gEq,driftingTwo_lossEq,driftingTwo_xEq,driftingTwo_uEq,ite_true,ite_false,  Nat.reduceAdd, ← EReal.coe_add, EReal.coe_zero]
  first | (apply congrArg (fun t : ℝ => (t:EReal));simp [poly] <;> ring) | rfl

private theorem driftingTwo_A1 (w : driftingTwo.V) : A driftingTwo 1 w = ((poly (1) (2) (0) w.val : ℝ) : EReal) := by
  simp only [A,G,hinted,inclusive,BanditRL.OnlineBTRL.sourceInclusive,Finset.sum_range_succ,Finset.sum_range_zero,add_zero,zero_add,driftingTwo_TEq,driftingTwo_psiEq,driftingTwo_hintEq,driftingTwo_lamEq,driftingTwo_gEq,driftingTwo_lossEq,driftingTwo_xEq,driftingTwo_uEq,ite_true,ite_false,  Nat.reduceAdd, ← EReal.coe_add, EReal.coe_zero]
  first | (apply congrArg (fun t : ℝ => (t:EReal));simp [poly] <;> ring) | rfl

private theorem driftingTwo_G1 (w : driftingTwo.V) : G driftingTwo 1 w = ((poly (1) (5) (0) w.val : ℝ) : EReal) := by
  simp only [A,G,hinted,inclusive,BanditRL.OnlineBTRL.sourceInclusive,Finset.sum_range_succ,Finset.sum_range_zero,add_zero,zero_add,driftingTwo_TEq,driftingTwo_psiEq,driftingTwo_hintEq,driftingTwo_lamEq,driftingTwo_gEq,driftingTwo_lossEq,driftingTwo_xEq,driftingTwo_uEq,ite_true,ite_false,  Nat.reduceAdd, ← EReal.coe_add, EReal.coe_zero]
  first | (apply congrArg (fun t : ℝ => (t:EReal));simp [poly] <;> ring) | rfl

private theorem driftingTwo_facts : Facts driftingTwo := by
  refine ⟨by decide,isClosed_univ,convex_univ,?_,?_,?_,?_,?_⟩
  · intro n hn v; exact EReal.coe_ne_bot _
  · intro n hn
    change n < 2 at hn
    interval_cases n
    · exact scalar_A _ (1) (0) (0) (by norm_num) driftingTwo_A0
    · exact scalar_A _ (1) (2) (0) (by norm_num) driftingTwo_A1
  · intro n hn
    change n < 2 at hn
    interval_cases n
    · exact scalar_G _ (1) (1) (0) 1 (by norm_num) (by norm_num) driftingTwo_G0
    · exact scalar_G _ (1) (5) (0) 1 (by norm_num) (by norm_num) driftingTwo_G1
  · intro n hn
    change n < 2 at hn
    interval_cases n
    · exact poly_min _ _ (1) (0) (0) driftingTwo_A0 (by norm_num) (by norm_num [driftingTwo,repeatZ,repeatZ',driftZ,allReal,poly,slope,Real.norm_eq_abs])
    · exact poly_min _ _ (1) (2) (0) driftingTwo_A1 (by norm_num) (by norm_num [driftingTwo,repeatZ,repeatZ',driftZ,allReal,poly,slope,Real.norm_eq_abs])
  · intro n hn
    change n < 2 at hn
    interval_cases n
    · intro w; norm_num [forecastError,driftingTwo,slope,allReal,← EReal.coe_sub,← EReal.coe_add,EReal.coe_le_coe_iff] <;> first | linarith | ring_nf
    · intro w
      change (((2*(-2):ℝ):EReal)-((-(-2):ℝ):EReal))+((3*(w.val-(-2)):ℝ):EReal) ≤ ((2*w.val:ℝ):EReal)-((-w.val:ℝ):EReal)
      rw [← EReal.coe_sub,← EReal.coe_add,← EReal.coe_sub,EReal.coe_le_coe_iff]
      linarith

private theorem declaredZero_A0 (w : declaredZero.V) : A declaredZero 0 w = ((poly (1) (0) (0) w.val : ℝ) : EReal) := by
  simp only [A,G,hinted,inclusive,BanditRL.OnlineBTRL.sourceInclusive,Finset.sum_range_succ,Finset.sum_range_zero,add_zero,zero_add,declaredZero_TEq,declaredZero_psiEq,declaredZero_hintEq,declaredZero_lamEq,declaredZero_gEq,declaredZero_lossEq,declaredZero_xEq,declaredZero_uEq,ite_true,ite_false,  Nat.reduceAdd, ← EReal.coe_add, EReal.coe_zero]
  first | (apply congrArg (fun t : ℝ => (t:EReal));simp [poly] <;> ring) | rfl

private theorem declaredZero_G0 (w : declaredZero.V) : G declaredZero 0 w = ((poly (1) (1) (0) w.val : ℝ) : EReal) := by
  simp only [A,G,hinted,inclusive,BanditRL.OnlineBTRL.sourceInclusive,Finset.sum_range_succ,Finset.sum_range_zero,add_zero,zero_add,declaredZero_TEq,declaredZero_psiEq,declaredZero_hintEq,declaredZero_lamEq,declaredZero_gEq,declaredZero_lossEq,declaredZero_xEq,declaredZero_uEq,ite_true,ite_false,  Nat.reduceAdd, ← EReal.coe_add, EReal.coe_zero]
  first | (apply congrArg (fun t : ℝ => (t:EReal));simp [poly] <;> ring) | rfl

private theorem declaredZero_facts : Facts declaredZero := by
  refine ⟨by decide,isClosed_univ,convex_univ,?_,?_,?_,?_,?_⟩
  · intro n hn v; exact EReal.coe_ne_bot _
  · intro n hn
    change n < 1 at hn
    interval_cases n
    · exact scalar_A _ (1) (0) (0) (by norm_num) declaredZero_A0
  · intro n hn
    change n < 1 at hn
    interval_cases n
    · exact scalar_G _ (1) (1) (0) 0 (by norm_num) (by norm_num) declaredZero_G0
  · intro n hn
    change n < 1 at hn
    interval_cases n
    · exact poly_min _ _ (1) (0) (0) declaredZero_A0 (by norm_num) (by norm_num [declaredZero,repeatZ,repeatZ',driftZ,allReal,poly,slope,Real.norm_eq_abs])
  · intro n hn
    change n < 1 at hn
    interval_cases n
    · intro w; norm_num [forecastError,declaredZero,slope,allReal,← EReal.coe_sub,← EReal.coe_add,EReal.coe_le_coe_iff] <;> first | linarith | ring_nf

private theorem declaredOne_A0 (w : declaredOne.V) : A declaredOne 0 w = ((poly (1) (0) (0) w.val : ℝ) : EReal) := by
  simp only [A,G,hinted,inclusive,BanditRL.OnlineBTRL.sourceInclusive,Finset.sum_range_succ,Finset.sum_range_zero,add_zero,zero_add,declaredOne_TEq,declaredOne_psiEq,declaredOne_hintEq,declaredOne_lamEq,declaredOne_gEq,declaredOne_lossEq,declaredOne_xEq,declaredOne_uEq,ite_true,ite_false,  Nat.reduceAdd, ← EReal.coe_add, EReal.coe_zero]
  first | (apply congrArg (fun t : ℝ => (t:EReal));simp [poly] <;> ring) | rfl

private theorem declaredOne_G0 (w : declaredOne.V) : G declaredOne 0 w = ((poly (1) (1) (0) w.val : ℝ) : EReal) := by
  simp only [A,G,hinted,inclusive,BanditRL.OnlineBTRL.sourceInclusive,Finset.sum_range_succ,Finset.sum_range_zero,add_zero,zero_add,declaredOne_TEq,declaredOne_psiEq,declaredOne_hintEq,declaredOne_lamEq,declaredOne_gEq,declaredOne_lossEq,declaredOne_xEq,declaredOne_uEq,ite_true,ite_false,  Nat.reduceAdd, ← EReal.coe_add, EReal.coe_zero]
  first | (apply congrArg (fun t : ℝ => (t:EReal));simp [poly] <;> ring) | rfl

private theorem declaredOne_facts : Facts declaredOne := by
  refine ⟨by decide,isClosed_univ,convex_univ,?_,?_,?_,?_,?_⟩
  · intro n hn v; exact EReal.coe_ne_bot _
  · intro n hn
    change n < 1 at hn
    interval_cases n
    · exact scalar_A _ (1) (0) (0) (by norm_num) declaredOne_A0
  · intro n hn
    change n < 1 at hn
    interval_cases n
    · exact scalar_G _ (1) (1) (0) 1 (by norm_num) (by norm_num) declaredOne_G0
  · intro n hn
    change n < 1 at hn
    interval_cases n
    · exact poly_min _ _ (1) (0) (0) declaredOne_A0 (by norm_num) (by norm_num [declaredOne,declaredZero,repeatZ,repeatZ',driftZ,allReal,poly,slope,Real.norm_eq_abs])
  · intro n hn
    change n < 1 at hn
    interval_cases n
    · intro w; norm_num [forecastError,declaredOne,declaredZero,slope,allReal,← EReal.coe_sub,← EReal.coe_add,EReal.coe_le_coe_iff] <;> first | linarith | ring_nf


private def hinge (t : ℝ) := max (t-1) 0
private def bowl (t : ℝ) := (hinge t)^2/2
private theorem tangent_bowl (p q : ℝ) : bowl p + hinge p*(q-p) ≤ bowl q := by
  by_cases hp : p ≤ 1
  · have hz : hinge p = 0 := max_eq_right (by linarith)
    unfold bowl;rw [hz];nlinarith [sq_nonneg (hinge q)]
  · have eq : hinge p = p-1 := max_eq_left (by linarith)
    have hq : q-1 ≤ hinge q := le_max_left _ _
    unfold bowl;rw [eq]
    nlinarith [sq_nonneg (hinge q-(p-1)),mul_nonneg (show 0 ≤ p-1 by linarith) (sub_nonneg.mpr hq)]

private theorem flat_A (w : flatHalfLine.V) : A flatHalfLine 0 w = ((poly 1 0 0 w.val : ℝ):EReal) := by
  simp only [A,hinted,Finset.sum_range_zero,add_zero,flatHalfLine_psiEq,flatHalfLine_hintEq,EReal.coe_zero,add_zero];apply congrArg (fun t : ℝ => (t:EReal));unfold poly;ring
private theorem flat_G (w : flatHalfLine.V) : G flatHalfLine 0 w = (bowl w.val : EReal) := by
  have hv : 0 ≤ w.val := w.property
  simp only [G,inclusive,BanditRL.OnlineBTRL.sourceInclusive,Finset.sum_range_one,flatHalfLine_psiEq,flatHalfLine_lossEq,if_pos hv,← EReal.coe_add]; apply congrArg (fun t:ℝ => (t:EReal));unfold bowl hinge;ring
private theorem flat_err (w : flatHalfLine.V) : forecastError flatHalfLine.loss flatHalfLine.hint 0 w =
    ((bowl w.val-w.val^2/2 : ℝ):EReal) := by
  have hv : 0 ≤ w.val := w.property
  simp [forecastError,flatHalfLine,hv,bowl,hinge]
private theorem flat_greg : inclusiveRegular (G flatHalfLine) flatHalfLine.lam 1 := by
  intro n hn
  have : n=0 := by omega
  subst n
  refine ⟨?_,fun v => by rw [flat_G];exact EReal.coe_lt_top _,?_,by norm_num,?_⟩
  · intro c
    have eq : {w : flatHalfLine.V | G flatHalfLine 0 w ≤ (c:EReal)} = {w | bowl w.val ≤ c} := by ext w;simp [flat_G]
    rw [eq]
    exact isClosed_le (by unfold bowl hinge; fun_prop) continuous_const
  · intro p
    refine ⟨slope (hinge p.val),fun q => ?_⟩
    rw [flat_G,flat_G,← EReal.coe_add,EReal.coe_le_coe_iff]
    exact tangent_bowl p.val q.val
  · intro p q a ha h1 hz
    simp only [flat_G,← EReal.coe_mul,← EReal.coe_add,← EReal.coe_sub,EReal.coe_le_coe_iff]
    change bowl (a*p.val+(1-a)*q.val) ≤ a*bowl p.val + (1-a)*bowl q.val - 0/2*a*(1-a)*_
    let t := a*p.val+(1-a)*q.val
    have p₁ := mul_le_mul_of_nonneg_left (tangent_bowl t p.val) ha.le
    have q₁ := mul_le_mul_of_nonneg_left (tangent_bowl t q.val) (sub_nonneg.mpr h1.le)
    change bowl t ≤ _
    have cancel : a*(hinge t*(p.val-t))+(1-a)*(hinge t*(q.val-t))=0 := by
      generalize hinge t = g; dsimp [t]; ring
    nlinarith only [p₁,q₁,cancel]

private theorem flat_facts : Facts flatHalfLine := by
  refine ⟨by decide,isClosed_Ici,convex_Ici _,?_,?_,flat_greg,?_,?_⟩
  · intro n hn v
    by_cases hv : 0 ≤ v
    · rw [flatHalfLine_lossEq,if_pos hv]; exact EReal.coe_ne_bot _
    · rw [flatHalfLine_lossEq,if_neg hv];exact top_ne_bot
  · intro n hn;change n < 1 at hn
    have : n=0 := by omega
    subst n; exact scalar_A _ 1 0 0 (by norm_num) flat_A
  · intro n hn;change n < 1 at hn
    have : n=0 := by omega
    subst n;exact poly_min _ _ 1 0 0 flat_A (by norm_num) (by change (1:ℝ)*0+0=0;norm_num)
  · intro n hn;change n < 1 at hn
    have : n=0 := by omega
    subst n;intro q
    rw [flat_err,flat_err,← EReal.coe_add,EReal.coe_le_coe_iff]
    change bowl 0-0^2/2+(-1)*(q.val-0) ≤ bowl q.val-q.val^2/2
    have hp : 0 ≤ q.val := q.property
    by_cases hx : q.val ≤ 1
    · have hz : hinge q.val=0 := max_eq_right (by linarith)
      have h0 : hinge 0 = 0 := by norm_num [hinge]
      simp only [bowl,h0,hz] <;> nlinarith [mul_nonneg hp (sub_nonneg.mpr hx)]
    · have hz : hinge q.val=q.val-1 := max_eq_left (by linarith)
      have h0 : hinge 0 = 0 := by norm_num [hinge]
      simp only [bowl,h0,hz] <;> nlinarith

private theorem flat_arg (z : flatHalfLine.V) : flatMin z ↔ z.val ∈ Set.Icc (0:ℝ) 1 := by
  constructor
  · intro h
    have h0 := h flatZero
    rw [flat_G,flat_G,EReal.coe_le_coe_iff] at h0
    have bn : bowl flatZero.val=0 := by norm_num [bowl,hinge,flatZero]
    rw [bn] at h0
    have hz : hinge z.val=0 := by unfold bowl at h0;nlinarith [sq_nonneg (hinge z.val)]
    exact ⟨z.property,by have hl := (le_max_left (z.val-1) 0);change z.val-1 ≤ hinge z.val at hl;linarith⟩
  · intro hz q
    rw [flat_G,flat_G,EReal.coe_le_coe_iff]
    have hh : hinge z.val=0 := max_eq_right (sub_nonpos.mpr hz.2)
    unfold bowl;rw [hh];nlinarith [sq_nonneg (hinge q.val)]

private theorem euc_sq (w : Pair) : (euc w)^2 = w.1^2+w.2^2 := by
  change ‖WithLp.toLp 2 w‖^2 = _
  rw [WithLp.prod_norm_sq_eq_of_L2]
  change ‖w.1‖^2+‖w.2‖^2 = _
  simp [Real.norm_eq_abs]
private theorem euc_sep (w : Pair) (h : euc w=0) : w=0 := by
  have s := euc_sq w
  rw [h] at s
  exact Prod.ext (by change w.1=0;nlinarith [sq_nonneg w.2]) (by change w.2=0;nlinarith [sq_nonneg w.1])
private theorem euc_minor (w : Pair) : (3:ℝ)/4*(euc w)^2 ≤ quad w := by
  rw [euc_sq];unfold quad;nlinarith [sq_nonneg (w.1-w.2)]
private theorem sup_minor (w : Pair) : (normSeminorm ℝ Pair w)^2 ≤ quad w := by
  change ‖w‖^2 ≤ _
  rw [Prod.norm_def];rcases le_total ‖w.1‖ ‖w.2‖ with h|h
  · rw [max_eq_right h,Real.norm_eq_abs,sq_abs];unfold quad;nlinarith [sq_nonneg (3*w.1-w.2)]
  · rw [max_eq_left h,Real.norm_eq_abs,sq_abs];unfold quad;nlinarith [sq_nonneg (w.1-3*w.2)]
private def boxpoly (b : ℝ) (w : Pair) := quad w/2+b*(w.1+w.2)
private theorem box_A (w : dualBox.V) : A dualBox 0 w = (boxpoly 0 w.val : EReal) := by
  simp [A,hinted,dualBox,boxpoly]
private theorem box_G (w : dualBox.V) : G dualBox 0 w = (boxpoly 1 w.val : EReal) := by
  have hw : w.val ∈ box := w.property
  simp [G,inclusive,BanditRL.OnlineBTRL.sourceInclusive,inc,dualBox,boxpoly,hw,EReal.coe_add]
private theorem box_err (w : dualBox.V) : forecastError dualBox.loss dualBox.hint 0 w =
    ((w.val.1+w.val.2:ℝ):EReal) := by
  have hw : w.val ∈ box := w.property
  simp [forecastError,dualBox,hw]
private def twoSlope (p q : ℝ) : Pair →L[ℝ] ℝ :=
  p • ContinuousLinearMap.fst ℝ ℝ ℝ + q • ContinuousLinearMap.snd ℝ ℝ ℝ
private theorem box_tangent (b : ℝ) (p q : Pair) :
    boxpoly b p + twoSlope ((9*p.1-3*p.2)/8+b) ((9*p.2-3*p.1)/8+b) (q-p) ≤ boxpoly b q := by
  have h := sup_minor (q-p)
  have nn : 0 ≤ quad (q-p) := (sq_nonneg _).trans h
  change boxpoly b p + (((9*p.1-3*p.2)/8+b)*(q.1-p.1)+((9*p.2-3*p.1)/8+b)*(q.2-p.2)) ≤ _
  simp only [boxpoly,quad,Prod.fst_sub,Prod.snd_sub] at nn ⊢
  linarith
private theorem box_shape (f : dualBox.V → EReal) (b l : ℝ) (N : Seminorm ℝ Pair)
    (eq : ∀ w, f w = (boxpoly b w.val : EReal)) (minor : ∀ w, l*(N w)^2 ≤ quad w) :
    Reg f ∧ restrictedStrong f N l := by
  refine ⟨⟨?_,fun v => by rw [eq];exact EReal.coe_lt_top _,?_⟩,?_⟩
  · intro c
    have he : {w : dualBox.V | f w ≤ (c:EReal)} = {w | boxpoly b w.val ≤ c} := by ext w;simp [eq]
    rw [he]; exact isClosed_le (by unfold boxpoly quad;fun_prop) continuous_const
  · intro p
    refine ⟨twoSlope ((9*p.val.1-3*p.val.2)/8+b) ((9*p.val.2-3*p.val.1)/8+b),fun q => ?_⟩
    rw [eq,eq,← EReal.coe_add,EReal.coe_le_coe_iff]
    exact box_tangent b p.val q.val
  · intro p q a ha h1 hz
    simp only [eq,← EReal.coe_mul,← EReal.coe_add,← EReal.coe_sub,EReal.coe_le_coe_iff]
    have hm := mul_le_mul_of_nonneg_left (minor (p.val-q.val)) (show 0 ≤ a*(1-a)/2 by have := sub_pos.mpr h1;positivity)
    change boxpoly b (a • p.val+(1-a) • q.val) ≤ _
    simp only [boxpoly,quad,Prod.fst_sub,Prod.snd_sub,Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul] at hm ⊢
    nlinarith only [hm]
private theorem box_facts : Facts dualBox := by
  have sa := box_shape _ 0 (3/4) euc box_A euc_minor
  have sg := box_shape _ 1 1 (normSeminorm ℝ Pair) box_G (fun w => by simpa using sup_minor w)
  refine ⟨by decide,isClosed_Icc.prod isClosed_Icc,(convex_Icc _ _).prod (convex_Icc _ _),?_,?_,?_,?_,?_⟩
  · intro n hn w; by_cases hw : w ∈ box <;> simp [dualBox,hw]
  · intro n hn;change n<1 at hn;have : n=0 := by omega
    subst n; exact ⟨sa.1.1,sa.1.2.1,sa.1.2.2,euc,euc_sep,3/4,by norm_num,sa.2⟩
  · intro n hn;change n<1 at hn;have : n=0 := by omega
    subst n; exact ⟨sg.1.1,sg.1.2.1,sg.1.2.2,by norm_num [dualBox],sg.2⟩
  · intro n hn;change n<1 at hn;have : n=0 := by omega
    subst n; intro q;rw [box_A,box_A,EReal.coe_le_coe_iff]
    have h := sup_minor q.val
    change boxpoly 0 (0,0) ≤ _
    norm_num [boxpoly,quad] at *;nlinarith [sq_nonneg (normSeminorm ℝ Pair q.val)]
  · intro n hn;change n<1 at hn;have : n=0 := by omega
    subst n;intro q;rw [box_err,box_err,← EReal.coe_add,EReal.coe_le_coe_iff]
    change 0+0+(q.val.1-0+(q.val.2-0)) ≤ _;ring_nf;exact le_rfl
private theorem box_min (q : dualBox.V) : G dualBox 0 dualBox.u ≤ G dualBox 0 q := by
  rw [box_G,box_G,EReal.coe_le_coe_iff]
  have ht := box_tangent 1 dualBox.u.val q.val
  norm_num [dualBox,twoSlope] at ht
  convert ht using 1 <;> norm_num
private theorem box_dual_norm : ‖boxFunctional‖=2 := by
  apply le_antisymm
  · apply boxFunctional.opNorm_le_bound (by norm_num)
    intro w
    change |w.1+w.2| ≤ 2*‖w‖
    have a : |w.1| ≤ ‖w‖ := le_max_left _ _
    have b : |w.2| ≤ ‖w‖ := le_max_right _ _
    linarith [abs_add_le w.1 w.2]
  · have h := boxFunctional.le_opNorm ((1,1):Pair)
    norm_num [boxFunctional,Prod.norm_def] at h
    exact h

private theorem boxFunctional_apply (w:Pair) : boxFunctional w = w.1+w.2 := rfl

theorem repeat_last_residual :
    r repeatLast ≤ s repeatLast repeatZ ∧
    r repeatLast ≤ y repeatLast ∧
    r repeatLast ≤ repeated repeatLast repeatZ' ∧
    repeatZ ≠ repeatZ' ∧ r repeatLast = 0 ∧ s repeatLast repeatZ = 0 ∧ y repeatLast = 0 ∧
    s repeatLast repeatZ' = -1/36 ∧ repeatLast.hint 0 repeatLast.u - repeatLast.hint 0 repeatZ' = 5/72 ∧
    repeated repeatLast repeatZ' = 1/24 ∧ ¬r repeatLast ≤ s repeatLast repeatZ' ∧
    ¬r repeatLast ≤ s repeatLast repeatZ' - (repeatLast.hint 0 repeatLast.u - repeatLast.hint 0 repeatZ') := by
  have f := repeatLast_facts
  have fy := repeatLast_facts
  have hz := poly_min _ repeatZ 2 (-1) (1/2) repeatLast_G0 (by norm_num) (by norm_num [repeatLast,repeatZ,repeatZ',driftZ,allReal,poly,slope,Real.norm_eq_abs])
  refine ⟨zero_hint_sharp_regret repeatLast.T f.pos Set.univ repeatLast.V (inc repeatLast) ⟨repeatLast.u,repeatLast.u.property⟩ f.closed f.cv repeatLast.psi repeatLast.hint repeatLast.loss f.bot f.aReg repeatLast.lam f.gReg repeatLast.x f.play repeatLast.g f.supp repeatZ hz repeatLast.u,
    positive_modulus_young_regret repeatLast.T fy.pos Set.univ repeatLast.V (inc repeatLast) ⟨repeatLast.u,repeatLast.u.property⟩ fy.closed fy.cv repeatLast.psi repeatLast.hint repeatLast.loss fy.bot fy.aReg repeatLast.lam fy.gReg repeatLast.x fy.play repeatLast.g fy.supp (by intro n hn; norm_num [repeatLast]) repeatLast.u,?_⟩
  have he (w : repeatLast.V) : G repeatLast 0 w + (repeatLast.hint 0 w : EReal) =
      ((poly 3 (-2) 1 w.val : ℝ) : EReal) := by
    rw [repeatLast_G0,← EReal.coe_add];congr 1;unfold poly;change _ + (w.val-1)^2/2 = _;ring
  have hz' := poly_min _ repeatZ' 3 (-2) 1 he (by norm_num) (by norm_num [repeatZ',allReal])
  refine ⟨repeated_hint_residual_regret repeatLast.T f.pos Set.univ repeatLast.V (inc repeatLast) ⟨repeatLast.u,repeatLast.u.property⟩ f.closed f.cv repeatLast.psi repeatLast.hint repeatLast.loss f.bot f.aReg repeatLast.lam f.gReg repeatLast.x f.play repeatLast.g f.supp repeatZ' hz' repeatLast.u,?_⟩
  norm_num [r,s,y,base,repeated,playedRegret,regularizerTerms,sharpTerms,inc,nextPlay,term,repeatLast,driftZ,repeatZ,repeatZ',allReal,slope,Finset.sum_range_succ,Real.norm_eq_abs,ContinuousLinearMap.norm_id,Subtype.ext_iff]

  intro h; have e := congrArg Subtype.val h; norm_num at e

theorem two_round_drift :
    r driftingTwo ≤ s driftingTwo driftZ ∧ r driftingTwo ≤ y driftingTwo ∧
    predicts (A driftingTwo) 2 driftingTwo.x ∧
    r driftingTwo = 11 ∧ driftingTwo.psi 1 (allReal (-5)) - driftingTwo.psi 0 (allReal 0) = 5/2 ∧
    driftingTwo.psi 0 (allReal (-2)) - driftingTwo.psi 1 (allReal (-2)) = 4 ∧
    term driftingTwo driftZ 0 = 0 ∧ term driftingTwo driftZ 1 = 9/2 ∧
    s driftingTwo driftZ = 11 ∧ y driftingTwo = 23/2 ∧ ¬r driftingTwo ≤ s driftingTwo driftZ - 4 := by
  have f := driftingTwo_facts
  have fy := driftingTwo_facts
  have hz := poly_min _ driftZ 1 5 0 driftingTwo_G1 (by norm_num) (by norm_num [driftingTwo,repeatZ,repeatZ',driftZ,allReal,poly,slope,Real.norm_eq_abs])
  refine ⟨zero_hint_sharp_regret driftingTwo.T f.pos Set.univ driftingTwo.V (inc driftingTwo) ⟨driftingTwo.u,driftingTwo.u.property⟩ f.closed f.cv driftingTwo.psi driftingTwo.hint driftingTwo.loss f.bot f.aReg driftingTwo.lam f.gReg driftingTwo.x f.play driftingTwo.g f.supp driftZ hz driftingTwo.u,
    positive_modulus_young_regret driftingTwo.T fy.pos Set.univ driftingTwo.V (inc driftingTwo) ⟨driftingTwo.u,driftingTwo.u.property⟩ fy.closed fy.cv driftingTwo.psi driftingTwo.hint driftingTwo.loss fy.bot fy.aReg driftingTwo.lam fy.gReg driftingTwo.x fy.play driftingTwo.g fy.supp (by intro n hn; norm_num [driftingTwo]) driftingTwo.u,?_⟩
  refine ⟨f.play,?_⟩
  norm_num [r,s,y,base,repeated,playedRegret,regularizerTerms,sharpTerms,inc,nextPlay,term,driftingTwo,driftZ,repeatZ,repeatZ',allReal,slope,Finset.sum_range_succ,Real.norm_eq_abs,ContinuousLinearMap.norm_id,Subtype.ext_iff]

  norm_num [norm_smul,ContinuousLinearMap.norm_id]

theorem dual_box_norms :
    r dualBox ≤ s dualBox dualBox.u ∧ r dualBox ≤ y dualBox ∧
    (∀ w, euc w = 0 → w = 0) ∧ restrictedStrong (A dualBox 0) euc (3/4) ∧
    restrictedStrong (G dualBox 0) (normSeminorm ℝ Pair) 1 ∧
    (∀ w : Pair, (euc w)^2 = w.1^2+w.2^2) ∧ euc (1,1) ≠ ‖((1,1) : Pair)‖ ∧
    ‖boxFunctional‖ = 2 ∧ boxFunctional (1,1) = 2 ∧
    dualBox.loss 0 (3,0) = ⊤ ∧ supports (forecastError dualBox.loss dualBox.hint 0) (dualBox.x 0) boxFunctional ∧
    r dualBox = 8/3 ∧ s dualBox dualBox.u = 28/9 ∧ y dualBox = 10/3 ∧
    base dualBox + (euc (1,1))^2/2 = 7/3 ∧ ¬r dualBox ≤ base dualBox + (euc (1,1))^2/2 := by
  have f := box_facts
  refine ⟨zero_hint_sharp_regret dualBox.T f.pos Set.univ dualBox.V (inc dualBox) ⟨dualBox.u,dualBox.u.property⟩ f.closed f.cv dualBox.psi dualBox.hint dualBox.loss f.bot f.aReg dualBox.lam f.gReg dualBox.x f.play dualBox.g f.supp dualBox.u box_min dualBox.u,
    positive_modulus_young_regret dualBox.T f.pos Set.univ dualBox.V (inc dualBox) ⟨dualBox.u,dualBox.u.property⟩ f.closed f.cv dualBox.psi dualBox.hint dualBox.loss f.bot f.aReg dualBox.lam f.gReg dualBox.x f.play dualBox.g f.supp (by intro n hn;norm_num [dualBox]) dualBox.u,
    euc_sep,(box_shape _ 0 (3/4) euc box_A euc_minor).2,(box_shape _ 1 1 (normSeminorm ℝ Pair) box_G (fun w => by simpa using sup_minor w)).2,euc_sq,?_,box_dual_norm,?_,?_,f.supp 0 (by decide),?_⟩
  · intro h;have hh := euc_sq (1,1);rw [h] at hh;norm_num [Prod.norm_def] at hh
  · norm_num [boxFunctional]
  · norm_num [dualBox,box,Set.mem_prod]
  · have he := euc_sq (1,1)
    norm_num at he
    norm_num [r,s,y,base,playedRegret,regularizerTerms,sharpTerms,dualBox,quad,box,Set.mem_prod,nextPlay,Finset.sum_range_succ,box_dual_norm,Prod.norm_def,Real.norm_eq_abs,he,boxFunctional_apply]
    all_goals try norm_num [← EReal.coe_neg,← EReal.coe_add]

theorem announced_zero_and_positive_young :
    r declaredZero ≤ s declaredZero declaredZero.u ∧ r declaredOne ≤ y declaredOne ∧
    declaredZero.lam 0 = 0 ∧ declaredOne.lam 0 = 1 ∧
    r declaredZero = 1 ∧ s declaredZero declaredZero.u = 3/2 ∧
    y declaredZero = 1/2 ∧ ¬r declaredZero ≤ y declaredZero ∧ y declaredOne = 1 := by
  have f := declaredZero_facts
  have fy := declaredOne_facts
  have hz := poly_min _ declaredZero.u 1 1 0 declaredZero_G0 (by norm_num) (by norm_num [declaredZero,repeatZ,repeatZ',driftZ,allReal,poly,slope,Real.norm_eq_abs])
  refine ⟨zero_hint_sharp_regret declaredZero.T f.pos Set.univ declaredZero.V (inc declaredZero) ⟨declaredZero.u,declaredZero.u.property⟩ f.closed f.cv declaredZero.psi declaredZero.hint declaredZero.loss f.bot f.aReg declaredZero.lam f.gReg declaredZero.x f.play declaredZero.g f.supp declaredZero.u hz declaredZero.u,
    positive_modulus_young_regret declaredOne.T fy.pos Set.univ declaredOne.V (inc declaredOne) ⟨declaredOne.u,declaredOne.u.property⟩ fy.closed fy.cv declaredOne.psi declaredOne.hint declaredOne.loss fy.bot fy.aReg declaredOne.lam fy.gReg declaredOne.x fy.play declaredOne.g fy.supp (by intro n hn; norm_num [declaredOne]) declaredOne.u,?_⟩
  norm_num [r,s,y,base,repeated,playedRegret,regularizerTerms,sharpTerms,inc,nextPlay,term,declaredZero,declaredOne,driftZ,repeatZ,repeatZ',allReal,slope,Finset.sum_range_succ,Real.norm_eq_abs,ContinuousLinearMap.norm_id,Subtype.ext_iff]

theorem flat_terminal_minimizers :
    (∀ n < flatHalfLine.T, ∃! p : flatHalfLine.V, ∀ q : flatHalfLine.V, A flatHalfLine n p ≤ A flatHalfLine n q) ∧
    (∃ z : flatHalfLine.V, flatMin z) ∧
    (∀ z : flatHalfLine.V, z.val ∈ Set.Icc (0:ℝ) 1 → r flatHalfLine ≤ s flatHalfLine z) ∧
    (∀ z : flatHalfLine.V, flatMin z ↔ z.val ∈ Set.Icc (0:ℝ) 1) ∧
    flatMin flatZero ∧ flatMin flatOne ∧ flatZero ≠ flatOne ∧
    (∀ μ : ℝ, 0 < μ → ¬restrictedStrong (G flatHalfLine 0) (normSeminorm ℝ ℝ) μ) ∧
    flatHalfLine.loss 0 (-1) = ⊤ ∧ r flatHalfLine = 1/2 ∧
    (∀ z : flatHalfLine.V, z.val ∈ Set.Icc (0:ℝ) 1 → s flatHalfLine z = 1/2+z.val) := by
  have f := flat_facts
  refine ⟨optimistic_round_unique flatHalfLine.T f.pos Set.univ flatHalfLine.V (inc flatHalfLine) ⟨flatHalfLine.u,flatHalfLine.u.property⟩ f.closed f.cv flatHalfLine.psi flatHalfLine.hint flatHalfLine.loss f.bot f.aReg,
    zero_hint_terminal_attained flatHalfLine.T f.pos Set.univ flatHalfLine.V (inc flatHalfLine) ⟨flatHalfLine.u,flatHalfLine.u.property⟩ f.closed f.cv flatHalfLine.psi flatHalfLine.hint flatHalfLine.loss f.bot f.aReg flatHalfLine.lam f.gReg flatHalfLine.x f.play (fun n hn => ⟨flatHalfLine.g n,f.supp n hn⟩),
    fun z hz => zero_hint_sharp_regret flatHalfLine.T f.pos Set.univ flatHalfLine.V (inc flatHalfLine) ⟨flatHalfLine.u,flatHalfLine.u.property⟩ f.closed f.cv flatHalfLine.psi flatHalfLine.hint flatHalfLine.loss f.bot f.aReg flatHalfLine.lam f.gReg flatHalfLine.x f.play flatHalfLine.g f.supp z ((flat_arg z).2 hz) flatHalfLine.u,flat_arg,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (flat_arg _).2 (by norm_num [flatZero,Set.mem_Icc])
  · exact (flat_arg _).2 (by norm_num [flatOne,Set.mem_Icc])
  · intro h;have hh := congrArg Subtype.val h;norm_num [flatZero,flatOne] at hh
  · intro μ hμ hs
    have mid : (1/2:ℝ) • flatZero.val+(1-1/2:ℝ) • flatOne.val ∈ flatHalfLine.V := by norm_num [flatZero,flatOne,flatHalfLine]
    have h := hs flatZero flatOne (1/2) (by norm_num) (by norm_num) mid
    simp only [flat_G,← EReal.coe_mul,← EReal.coe_add,← EReal.coe_sub,EReal.coe_le_coe_iff] at h
    norm_num [flatZero,flatOne,bowl,hinge,Real.norm_eq_abs] at h
    linarith
  · norm_num [flatHalfLine]
  · change (∑ i ∈ range 1, (flatHalfLine.loss i (flatHalfLine.x i).val).toReal) - (∑ i ∈ range 1, (flatHalfLine.loss i flatHalfLine.u.val).toReal) = _
    simp only [Finset.sum_range_one,flatHalfLine_xEq,flatHalfLine_uEq,flatHalfLine_lossEq,if_pos (by norm_num : (0:ℝ) ≤ 0),if_pos (by norm_num : (0:ℝ) ≤ 1),EReal.toReal_coe]
    norm_num
  · intro z hz
    have zn : 0 ≤ z.val := z.property
    norm_num [s,base,regularizerTerms,sharpTerms,nextPlay,slope,Finset.sum_range_succ] <;> ring
    change (1:ℝ)^2*(1/2)-0+0^2*(-1/2)+z.val=1/2+z.val
    ring

end BanditRL.OnlineOptimisticCanary
