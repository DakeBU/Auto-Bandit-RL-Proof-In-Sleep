import BanditRLProof.OnlineBTRLTerminal
noncomputable section
attribute [local instance] Classical.propDecidable
open Set Finset
namespace BanditRL.OnlineBTRLCanary

structure Model where
  T : ℕ
  X : Set ℝ
  V : Set ℝ
  psi : ℕ → X → ℝ
  loss : ℕ → ℝ → EReal
  lam : ℕ → ℝ
  x : ℕ → ℝ
  u : ℝ

def repeatedLast : Model :=
  ⟨1, univ, univ, fun _ w => w.val^2 / 2,
    fun _ v => (((v-1)^2 / 2 : ℝ) : EReal), fun _ => 2,
    fun t => if t = 0 then 1/2 else 17, 1/2⟩

def twoRounds : Model :=
  ⟨2, univ, Icc (-1) 3, fun t w => if t = 0 then w.val^2/2 else w.val^2,
    fun t v => if v ∈ Icc (-1:ℝ) 3 then
      ((if t = 0 then -v else -3*v : ℝ) : EReal) else ⊤,
    fun t => if t = 0 then 1 else 2,
    fun t => if t = 0 then 1 else if t = 1 then 2 else 100, 0⟩

def constrained : Model :=
  ⟨1, univ, Icc 0 1, fun _ w => w.val^2/2,
    fun _ v => ((-2*v : ℝ) : EReal), fun _ => 1,
    fun t => if t = 0 then 1 else 17, 0⟩

def openCarrier : Model :=
  ⟨1, Ioo (-1) 1, Icc (-1/2) (1/2), fun _ w => w.val^2,
    fun _ _ => 0, fun _ => 2, fun t => if t = 0 then 0 else 17, 1/2⟩

def r (m : Model) (t : ℕ) : ℝ → ℝ :=
  Function.extend Subtype.val (m.psi t) (fun _ => 0)

def g (m : Model) (t : ℕ) (v : m.X) : EReal :=
  (m.psi t v : EReal) + ∑ i ∈ range (t+1), m.loss i v.val

def h (m : Model) (t : ℕ) (v : ℝ) : EReal :=
  if hv : v ∈ m.V then
    if hx : v ∈ m.X then g m t ⟨v,hx⟩ else ⊤
  else ⊤

def regret (m : Model) : ℝ :=
  (∑ t ∈ range m.T, (m.loss t (m.x t)).toReal) -
    ∑ t ∈ range m.T, (m.loss t m.u).toReal

def baseline (m : Model) : ℝ := r m (m.T-1) m.u - r m 0 (m.x 0)
def movement (m : Model) : ℝ :=
  -(∑ t ∈ range (m.T-1), (m.lam t / 2) * ‖m.x t - m.x (t+1)‖ ^ 2)
def drift (m : Model) : ℝ :=
  ∑ t ∈ range (m.T-1), (r m t (m.x (t+1)) - r m (t+1) (m.x (t+1)))
def terminal (m : Model) : ℝ :=
  -(m.lam (m.T-1) / 2) * ‖m.u - m.x (m.T-1)‖ ^ 2
def weak (m : Model) : ℝ := baseline m + movement m + drift m
def sharp (m : Model) : ℝ := weak m + terminal m

def bounds (m : Model) : Prop := regret m ≤ sharp m ∧ regret m ≤ weak m
def attainment (m : Model) : Prop :=
  ∀ t < m.T, ∃! p : ℝ, p ∈ m.V ∧ IsMinOn (h m t) m.V p
def runValid (m : Model) : Prop :=
  m.V ⊆ m.X ∧ Convex ℝ m.V ∧ IsClosed m.V ∧ m.V.Nonempty ∧ m.u ∈ m.V ∧
    ∀ t < m.T, m.x t ∈ m.V ∧ IsMinOn (h m t) m.V (m.x t)
def closedLevels {α : Type*} [TopologicalSpace α] (f : α → EReal) : Prop :=
  ∀ c : ℝ, IsClosed {v | f v ≤ (c : EReal)}
def wrongExtension (v : ℝ) : EReal :=
  if v ∈ openCarrier.X then ((v^2 : ℝ) : EReal) else ⊤

open BanditRL.OnlineBTRL BanditRL.OnlineConvex
private def StrongAt (m : Model) (n : ℕ) : Prop :=
  ∀ p q : m.X, g m n p < ⊤ → g m n q < ⊤ →
    ∀ a : ℝ, 0 < a → a < 1 → ∀ hz : a • p.val + (1-a) • q.val ∈ m.X,
    g m n ⟨_,hz⟩ ≤ (a : EReal)*g m n p + ((1-a : ℝ) : EReal)*g m n q -
      (((m.lam n / 2)*a*(1-a)*‖p.val-q.val‖^2 : ℝ) : EReal)

private def poly (l b c v : ℝ) : ℝ := l/2*v^2+b*v+c

private theorem shape (m : Model) (n : ℕ) (D : Set ℝ) (hvx : m.V ⊆ m.X)
    (hu : m.u ∈ m.V) (hd : m.V ⊆ D) (hc : IsClosed D) (hcv : Convex ℝ D)
    (b c : ℝ) (eq : ∀ w : m.X, g m n w =
      if w.val ∈ D then ((poly (m.lam n) b c w.val : ℝ) : EReal) else ⊤) :
    SourceProper (g m n) ∧ SourceClosed (g m n) ∧ StrongAt m n := by
  refine ⟨⟨?_,?_⟩,?_,?_⟩
  · intro w
    rw [eq]
    split_ifs <;> simp
  · exact ⟨⟨m.u,hvx hu⟩,_,by rw [eq,if_pos (hd hu)]⟩
  · intro r'
    have hset : {w : m.X | g m n w ≤ (r' : EReal)} =
        (Subtype.val ⁻¹' D) ∩ {w : m.X | poly (m.lam n) b c w.val ≤ r'} := by
      ext w
      by_cases hw : w.val ∈ D <;> simp [eq,hw]
    rw [hset]
    exact (hc.preimage continuous_subtype_val).inter (isClosed_le (by unfold poly; fun_prop) continuous_const)
  · intro p q hp hq a ha ha1 hz
    have inD (w : m.X) (hf : g m n w < ⊤) : w.val ∈ D := by
      by_contra hw
      simp [eq,hw] at hf
    have hpd := inD p hp
    have hqd := inD q hq
    have hzD := hcv hpd hqd ha.le (sub_nonneg.mpr ha1.le) (by ring)
    rw [eq,if_pos hzD,eq,if_pos hpd,eq,if_pos hqd]
    simp only [← EReal.coe_mul,← EReal.coe_add,
      ← EReal.coe_sub,EReal.coe_le_coe_iff,Real.norm_eq_abs,sq_abs,smul_eq_mul,poly]
    exact le_of_eq (by ring)

private theorem h_eq (m : Model) (n : ℕ) (hvx : m.V ⊆ m.X) :
    h m n = feasibleInclusive m.X m.V hvx m.psi m.loss n := by
  funext v
  by_cases hv : v ∈ m.V <;> simp [h,feasibleInclusive,hv,show v ∈ m.V → v ∈ m.X from @hvx v,g,sourceInclusive]

private theorem r_on (m : Model) (n : ℕ) (v : ℝ) (hv : v ∈ m.X) :
    r m n v = m.psi n ⟨v,hv⟩ :=
  Subtype.val_injective.extend_apply _ _ ⟨v,hv⟩

private structure Facts (m : Model) : Prop where
  posT : 0 < m.T
  vx : m.V ⊆ m.X
  conv : Convex ℝ m.V
  closed : IsClosed m.V
  uFeas : m.u ∈ m.V
  noBot : ∀ i < m.T, ∀ v, m.loss i v ≠ ⊥
  dom : ∀ i < m.T, m.V ⊆ effectiveDomain (m.loss i)
  curvature : ∀ i < m.T, 0 < m.lam i
  properties : ∀ i < m.T, SourceProper (g m i) ∧ SourceClosed (g m i) ∧ StrongAt m i
  xFeas : ∀ i < m.T, m.x i ∈ m.V
  optimal : ∀ i < m.T, IsMinOn (h m i) m.V (m.x i)

private theorem facts_run (m : Model) (f : Facts m) : runValid m :=
  ⟨f.vx,f.conv,f.closed,⟨_,f.uFeas⟩,f.uFeas,fun i hi => ⟨f.xFeas i hi,f.optimal i hi⟩⟩

private theorem r_univ (m : Model) (hx : m.X = univ) (n : ℕ) (v : ℝ) :
    r m n v = m.psi n ⟨v,by rw [hx];trivial⟩ := r_on _ _ _ _
private theorem h_on (m : Model) (n : ℕ) (v : ℝ) (hV : v ∈ m.V) (hX : v ∈ m.X) :
    h m n v = g m n ⟨v,hX⟩ := by simp [h,hV,hX]

private theorem rep_g (w : repeatedLast.X) : g repeatedLast 0 w =
    ((poly 2 (-1) (1/2) w.val : ℝ) : EReal) := by
  simp only [g,repeatedLast,Finset.sum_range_one,Nat.zero_add,← EReal.coe_add]
  congr 1
  unfold poly
  ring

private theorem rep_h (v : ℝ) : h repeatedLast 0 v = ((poly 2 (-1) (1/2) v : ℝ) : EReal) := by
  rw [h_on repeatedLast 0 v (Set.mem_univ _) (Set.mem_univ _)]
  exact rep_g _

private theorem rep_min (p : ℝ) :
    IsMinOn (h repeatedLast 0) repeatedLast.V p ↔ p = 1/2 := by
  constructor
  · intro hmin
    have hh := hmin (Set.mem_univ (1/2 : ℝ))
    change h repeatedLast 0 p ≤ h repeatedLast 0 (1/2) at hh
    rw [rep_h,rep_h,EReal.coe_le_coe_iff] at hh
    unfold poly at hh
    by_contra hn
    nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr hn)]
  · rintro rfl v _
    change h repeatedLast 0 (1/2) ≤ h repeatedLast 0 v
    rw [rep_h,rep_h,EReal.coe_le_coe_iff]
    unfold poly
    nlinarith [sq_nonneg (v-1/2)]

private theorem rep_facts : Facts repeatedLast := by
  refine ⟨by decide,Subset.rfl,convex_univ,isClosed_univ,Set.mem_univ _,?_,?_,?_,?_,?_,?_⟩
  · intro i hi v
    exact EReal.coe_ne_bot _
  · intro i hi v hv
    exact EReal.coe_lt_top _
  · intro i hi
    norm_num [repeatedLast]
  · intro i hi
    have : i = 0 := by change i < 1 at hi; omega
    subst i
    apply shape repeatedLast 0 univ Subset.rfl (Set.mem_univ _) Subset.rfl isClosed_univ convex_univ (-1) (1/2)
    intro w
    simpa only [Set.mem_univ,if_true] using rep_g w
  · intro i hi
    exact Set.mem_univ _
  · intro i hi
    have : i = 0 := by change i < 1 at hi; omega
    subst i
    apply (rep_min _).2
    norm_num [repeatedLast]
private theorem con_g (w : constrained.X) : g constrained 0 w =
    ((poly 1 (-2) 0 w.val : ℝ) : EReal) := by
  simp only [g,constrained,Finset.sum_range_one,Nat.zero_add,← EReal.coe_add]
  congr 1
  unfold poly
  ring

private theorem con_h (v : ℝ) (hv : v ∈ constrained.V) :
    h constrained 0 v = ((poly 1 (-2) 0 v : ℝ) : EReal) := by
  rw [h_on constrained 0 v hv (Set.mem_univ _)]
  exact con_g _

private theorem con_min : IsMinOn (h constrained 0) constrained.V 1 := by
  intro v hv
  change h constrained 0 1 ≤ h constrained 0 v
  rw [con_h _ (by norm_num [constrained]),con_h _ hv,EReal.coe_le_coe_iff]
  change 0 ≤ v ∧ v ≤ 1 at hv
  unfold poly
  nlinarith [sq_nonneg (v-1)]

private theorem con_facts : Facts constrained := by
  refine ⟨by decide,Set.subset_univ _,convex_Icc _ _,isClosed_Icc,by norm_num [constrained],?_,?_,?_,?_,?_,?_⟩
  · intro i hi v; exact EReal.coe_ne_bot _
  · intro i hi v hv; exact EReal.coe_lt_top _
  · intro i hi;norm_num [constrained]
  · intro i hi
    have : i = 0 := by change i < 1 at hi; omega
    subst i
    apply shape constrained 0 univ (Set.subset_univ _) (by norm_num [constrained])
      (Set.subset_univ _) isClosed_univ convex_univ (-2) 0
    intro w
    simpa only [Set.mem_univ,if_true] using con_g w
  · intro i hi
    have : i = 0 := by change i < 1 at hi; omega
    subst i; norm_num [constrained]
  · intro i hi
    have : i = 0 := by change i < 1 at hi; omega
    subst i;exact con_min

private theorem open_vx : openCarrier.V ⊆ openCarrier.X := by
  intro v hv
  change -(1:ℝ)/2 ≤ v ∧ v ≤ 1/2 at hv
  exact ⟨by linarith [hv.1],by linarith [hv.2]⟩

private theorem open_g (w : openCarrier.X) :
    g openCarrier 0 w = ((w.val^2 : ℝ) : EReal) := by simp [g,openCarrier]

private theorem square_closed : SourceClosed (fun v : ℝ => ((v^2 : ℝ) : EReal)) := by
  intro c
  simpa only [EReal.coe_le_coe_iff] using (isClosed_le (f:=fun v : ℝ => v^2) (g:=fun _ => c) (by fun_prop) continuous_const)

private theorem open_h (v : ℝ) (hv : v ∈ openCarrier.V) :
    h openCarrier 0 v = ((v^2 : ℝ) : EReal) := by rw [h_on _ _ _ hv (open_vx hv),open_g]

private theorem open_facts : Facts openCarrier := by
  refine ⟨by decide,open_vx,convex_Icc _ _,isClosed_Icc,by norm_num [openCarrier],?_,?_,?_,?_,?_,?_⟩
  · intro i hi v;exact EReal.zero_ne_bot
  · intro i hi v hv;exact EReal.zero_lt_top
  · intro i hi;norm_num [openCarrier]
  · intro i hi
    have : i = 0 := by change i < 1 at hi; omega
    subst i
    apply shape openCarrier 0 univ open_vx (by norm_num [openCarrier]) (Set.subset_univ _)
      isClosed_univ convex_univ 0 0
    intro w
    rw [open_g]
    norm_num [poly,openCarrier]
  · intro i hi
    have : i = 0 := by change i < 1 at hi; omega
    subst i; norm_num [openCarrier]
  · intro i hi
    have : i = 0 := by change i < 1 at hi; omega
    subst i;intro v hv
    change h openCarrier 0 0 ≤ h openCarrier 0 v
    rw [open_h _ (by norm_num [openCarrier]),open_h _ hv,EReal.coe_le_coe_iff]
    simpa using sq_nonneg v

private theorem two_g0 (w : twoRounds.X) : g twoRounds 0 w =
    if w.val ∈ Icc (-1:ℝ) 3 then ((poly 1 (-1) 0 w.val : ℝ) : EReal) else ⊤ := by
  by_cases hv : w.val ∈ Icc (-1:ℝ) 3
  · simp only [g,twoRounds,if_true,Finset.sum_range_one,Nat.zero_add,if_pos hv,← EReal.coe_add]
    congr 1;unfold poly;ring
  · simp only [g,twoRounds,Nat.zero_add,Finset.sum_range_one,if_neg hv,if_true,EReal.coe_add_top]
private theorem two_g1 (w : twoRounds.X) : g twoRounds 1 w =
    if w.val ∈ Icc (-1:ℝ) 3 then ((poly 2 (-4) 0 w.val : ℝ) : EReal) else ⊤ := by
  by_cases hv : w.val ∈ Icc (-1:ℝ) 3
  · simp only [g,twoRounds,Finset.sum_range_succ,Finset.sum_range_zero,zero_add,if_pos hv,
      if_true,one_ne_zero,if_false,← EReal.coe_add]
    congr 1;unfold poly;ring
  · simp only [g,twoRounds,Finset.sum_range_succ,Finset.sum_range_zero,zero_add,if_neg hv,if_true,one_ne_zero,if_false,EReal.top_add_top,EReal.coe_add_top]
private theorem two_facts : Facts twoRounds := by
  refine ⟨by decide,Set.subset_univ _,convex_Icc _ _,isClosed_Icc,by norm_num [twoRounds],?_,?_,?_,?_,?_,?_⟩
  · intro i hi v
    by_cases hv : v ∈ Icc (-1:ℝ) 3
    · simp only [twoRounds,if_pos hv]; exact EReal.coe_ne_bot _
    · simp only [twoRounds,if_neg hv]; exact top_ne_bot
  · intro i hi v hv
    change v ∈ Icc (-1:ℝ) 3 at hv
    change twoRounds.loss i v < ⊤
    simp only [twoRounds,if_pos hv]
    exact EReal.coe_lt_top _
  · intro i hi
    by_cases h0 : i = 0 <;> norm_num [twoRounds,h0]
  · intro i hi
    change i < 2 at hi
    interval_cases i
    · exact shape twoRounds 0 _ (Set.subset_univ _) (by norm_num [twoRounds]) Subset.rfl
        isClosed_Icc (convex_Icc _ _) (-1) 0 (fun w => by simpa [twoRounds] using two_g0 w)
    · exact shape twoRounds 1 _ (Set.subset_univ _) (by norm_num [twoRounds]) Subset.rfl
        isClosed_Icc (convex_Icc _ _) (-4) 0 (fun w => by simpa [twoRounds] using two_g1 w)
  · intro i hi;change i < 2 at hi;interval_cases i <;> norm_num [twoRounds]
  · intro i hi v hv
    change v ∈ Icc (-1:ℝ) 3 at hv
    change i < 2 at hi
    interval_cases i
    · change h twoRounds 0 1 ≤ h twoRounds 0 v
      rw [h_on _ _ _ (by norm_num [twoRounds]) (Set.mem_univ _),
        h_on _ _ _ hv (Set.mem_univ _),two_g0,two_g0]
      simp only [if_pos hv,show (1:ℝ) ∈ Icc (-1:ℝ) 3 by norm_num,if_true,EReal.coe_le_coe_iff,poly]
      nlinarith [sq_nonneg (v-1)]
    · change h twoRounds 1 2 ≤ h twoRounds 1 v
      rw [h_on _ _ _ (by norm_num [twoRounds]) (Set.mem_univ _),
        h_on _ _ _ hv (Set.mem_univ _),two_g1,two_g1]
      simp only [if_pos hv,show (2:ℝ) ∈ Icc (-1:ℝ) 3 by norm_num,if_true,EReal.coe_le_coe_iff,poly]
      nlinarith [sq_nonneg (v-2)]

theorem constrained_minimum_and_ambient_minimum :
    let m := constrained
    bounds m ∧ attainment m ∧ runValid m ∧
    m.x 0 = 1 ∧ (2 : ℝ) ∉ m.V ∧
    (∀ p : ℝ, IsMinOn (fun v => r m 0 v + (m.loss 0 v).toReal) univ p ↔ p = 2) ∧
    (∀ p : ℝ, (p ∈ m.V ∧ IsMinOn (h m 0) m.V p) ↔ p = 1) ∧
    regret m = -2 ∧ weak m = -(1/2 : ℝ) ∧ terminal m = -(1/2 : ℝ) ∧ sharp m = -1 := by
  let m := constrained
  have f : Facts m := con_facts
  have bound := corrected_btrl_terminal_bound m.T f.posT m.X m.V f.vx f.conv f.closed ⟨_,f.uFeas⟩
    m.psi m.loss f.noBot f.dom m.lam f.curvature (fun i hi => (f.properties i hi).1)
    (fun i hi => (f.properties i hi).2.1) (fun i hi => (f.properties i hi).2.2)
    m.x f.xFeas (fun i hi => h_eq m i f.vx ▸ f.optimal i hi) m.u f.uFeas
  have att := btrl_real_round_minimizer_existsUnique m.T f.posT m.X m.V f.vx f.conv f.closed ⟨_,f.uFeas⟩
    m.psi m.loss f.noBot f.dom m.lam f.curvature (fun i hi => (f.properties i hi).1)
    (fun i hi => (f.properties i hi).2.1) (fun i hi => (f.properties i hi).2.2)
  refine ⟨?_,?_,facts_run m f,?_⟩
  · simpa only [bounds,sharp,weak,regret,baseline,movement,drift,terminal,r,regularizerValue,
      sub_eq_add_neg,neg_mul] using bound
  · intro i hi
    rw [h_eq m i f.vx]
    exact att i hi
  · have hr (n : ℕ) (v : ℝ) : r constrained n v = v^2/2 := r_univ _ rfl n v
    have ha (p : ℝ) : IsMinOn (fun v => r constrained 0 v + (constrained.loss 0 v).toReal) univ p ↔ p = 2 := by
      constructor
      · intro hm
        have hh := hm (Set.mem_univ (2:ℝ))
        change r constrained 0 p + _ ≤ r constrained 0 2 + _ at hh
        simp only [hr] at hh
        change p^2/2 + -2*p ≤ 2^2/2 + -2*2 at hh
        by_contra hn
        nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr hn)]
      · rintro rfl v _
        change r constrained 0 2 + _ ≤ r constrained 0 v + _
        simp only [hr]
        change 2^2/2 + -2*2 ≤ v^2/2 + -2*v
        nlinarith [sq_nonneg (v-2)]
    have hc (p : ℝ) : (p ∈ constrained.V ∧ IsMinOn (h constrained 0) constrained.V p) ↔ p = 1 := by
      constructor
      · rintro ⟨hp,hm⟩
        have hh := hm (show (1:ℝ) ∈ constrained.V by norm_num [constrained])
        change h constrained 0 p ≤ h constrained 0 1 at hh
        rw [con_h p hp,con_h 1 (by norm_num [constrained]),EReal.coe_le_coe_iff] at hh
        change 0 ≤ p ∧ p ≤ 1 at hp
        unfold poly at hh
        nlinarith [sq_nonneg (p-1)]
      · rintro rfl
        exact ⟨by norm_num [constrained],con_min⟩
    refine ⟨by rfl,by norm_num [m,constrained],ha,hc,?_,?_,?_,?_⟩ <;>
      dsimp only [m,regret,weak,sharp,baseline,movement,drift,terminal] <;>
      (try simp only [hr]) <;> norm_num [constrained,Real.norm_eq_abs]

theorem open_carrier_closed_transfer :
    let m := openCarrier
    bounds m ∧ attainment m ∧ runValid m ∧
    ¬ IsClosed m.X ∧ closedLevels (g m 0) ∧
    closedLevels (fun v : ℝ => ((v^2 : ℝ) : EReal)) ∧
    (∀ v : m.X, g m 0 v = ((v.val ^ 2 : ℝ) : EReal)) ∧
    closedLevels (h m 0) ∧ {v : ℝ | wrongExtension v ≤ 1} = m.X ∧
    ¬ closedLevels wrongExtension ∧ m.x 0 = 0 ∧
    regret m = 0 ∧ weak m = 1/4 ∧ sharp m = 0 := by
  let m := openCarrier
  have f : Facts m := open_facts
  have bound := corrected_btrl_terminal_bound m.T f.posT m.X m.V f.vx f.conv f.closed ⟨_,f.uFeas⟩
    m.psi m.loss f.noBot f.dom m.lam f.curvature (fun i hi => (f.properties i hi).1)
    (fun i hi => (f.properties i hi).2.1) (fun i hi => (f.properties i hi).2.2)
    m.x f.xFeas (fun i hi => h_eq m i f.vx ▸ f.optimal i hi) m.u f.uFeas
  have att := btrl_real_round_minimizer_existsUnique m.T f.posT m.X m.V f.vx f.conv f.closed ⟨_,f.uFeas⟩
    m.psi m.loss f.noBot f.dom m.lam f.curvature (fun i hi => (f.properties i hi).1)
    (fun i hi => (f.properties i hi).2.1) (fun i hi => (f.properties i hi).2.2)
  refine ⟨?_,?_,facts_run m f,?_⟩
  · simpa only [bounds,sharp,weak,regret,baseline,movement,drift,terminal,r,regularizerValue,
      sub_eq_add_neg,neg_mul] using bound
  · intro i hi
    rw [h_eq m i f.vx]
    exact att i hi
  · have hn : ¬ IsClosed openCarrier.X := by
      change ¬ IsClosed (Ioo (-1:ℝ) 1)
      intro hc
      have hcl := hc.closure_eq
      rw [closure_Ioo (by norm_num)] at hcl
      have h1 : (1:ℝ) ∈ Ioo (-1:ℝ) 1 := hcl ▸ (show (1:ℝ) ∈ Icc (-1:ℝ) 1 by norm_num)
      exact (lt_irrefl _ h1.2)
    have hrel : closedLevels (g openCarrier 0) := (open_facts.properties 0 (by decide)).2.1
    have hr₁ : closedLevels (h openCarrier 0) := by
      intro c
      let j : openCarrier.V → openCarrier.X := fun v => ⟨v.val,open_vx v.property⟩
      have hj : Continuous j := continuous_subtype_val.subtype_mk _
      have hi := isClosed_Icc.isClosedMap_subtype_val _ ((hrel c).preimage hj)
      change IsClosed (Subtype.val '' (j ⁻¹' {w | g openCarrier 0 w ≤ (c:EReal)})) at hi
      convert hi using 1
      ext v
      constructor
      · intro hv
        by_cases hV : v ∈ openCarrier.V
        · refine ⟨⟨v,hV⟩,?_,rfl⟩
          change h openCarrier 0 v ≤ (c:EReal) at hv
          change g openCarrier 0 ⟨v,open_vx hV⟩ ≤ (c:EReal)
          rwa [h_on _ _ _ hV (open_vx hV)] at hv
        · simpa only [h,if_neg hV,dif_neg hV,Set.mem_setOf_eq,not_le.mpr (EReal.coe_lt_top c)] using hv
      · rintro ⟨w,hw,rfl⟩
        simpa only [Set.mem_setOf_eq,h_on _ _ _ w.property (open_vx w.property)] using hw
    have hr₂ : closedLevels (h openCarrier 0) := by
      intro c
      have hs : {v | h openCarrier 0 v ≤ (c:EReal)} = openCarrier.V ∩ {v | ((v^2:ℝ):EReal) ≤ (c:EReal)} := by
        ext v
        by_cases hv : v ∈ openCarrier.V
        · simp only [Set.mem_setOf_eq,Set.mem_inter_iff,hv,true_and,open_h v hv]
        · have he : h openCarrier 0 v = ⊤ := by unfold h;rw [dif_neg hv]
          simp only [Set.mem_setOf_eq,Set.mem_inter_iff,he,not_le.mpr (EReal.coe_lt_top c),hv,false_and]
      rw [hs]
      exact isClosed_Icc.inter (square_closed c)
    have wrong : {v : ℝ | wrongExtension v ≤ 1} = openCarrier.X := by
      ext v
      by_cases hv : v ∈ openCarrier.X
      · have hh : (-1:ℝ) < v ∧ v < 1 := hv
        have hs : v^2 ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr hh.2.le) (sub_nonneg.mpr hh.1.le)]
        apply iff_of_true _ hv
        change wrongExtension v ≤ 1
        rw [wrongExtension,if_pos hv]
        exact EReal.coe_le_coe_iff.mpr hs
      · change wrongExtension v ≤ 1 ↔ _
        rw [wrongExtension,if_neg hv]
        exact iff_of_false (not_le.mpr (EReal.coe_lt_top 1)) hv
    refine ⟨hn,hrel,square_closed,open_g,and_self_iff.mp ⟨hr₁,hr₂⟩,wrong,?_,by rfl,?_,?_,?_⟩
    · intro hc
      have h1 := hc 1
      exact hn (by simpa only [EReal.coe_one,wrong] using h1)
    · norm_num [m,regret,openCarrier]
    · change r openCarrier 0 (1/2) - r openCarrier 0 0 - _ + _ = _
      rw [r_on openCarrier 0 (1/2) (by norm_num [openCarrier]),r_on openCarrier 0 0 (by norm_num [openCarrier])]
      change (1/2:ℝ)^2-0^2 - _ + _ = _
      norm_num [m,openCarrier,drift,movement]
    · change r openCarrier 0 (1/2) - r openCarrier 0 0 - _ + _ + _ = _
      rw [r_on openCarrier 0 (1/2) (by norm_num [openCarrier]),r_on openCarrier 0 0 (by norm_num [openCarrier])]
      change (1/2:ℝ)^2-0^2 - _ + _ + _ = _
      norm_num [m,openCarrier,drift,movement,terminal,Real.norm_eq_abs]

theorem repeated_last_bound_and_fake_ghost :
    let m := repeatedLast
    bounds m ∧ attainment m ∧ runValid m ∧
    m.x 0 = 1/2 ∧ m.u = 1/2 ∧ m.x 1 = 17 ∧
    regret m = 0 ∧ weak m = 0 ∧ sharp m = 0 ∧
    (∀ p : ℝ, IsMinOn (h m 0) m.V p ↔ p = 1/2) ∧
    (∀ p : ℝ, IsMinOn (fun v => r m 0 v + 2 * (m.loss 0 v).toReal) m.V p ↔ p = 2/3) ∧
    weak m - (m.lam 0 / 2) * ‖m.x 0 - (2/3 : ℝ)‖ ^ 2 = -(1/36 : ℝ) ∧
    ¬ regret m ≤ weak m - (m.lam 0 / 2) * ‖m.x 0 - (2/3 : ℝ)‖ ^ 2 := by
  let m := repeatedLast
  have f : Facts m := rep_facts
  have bound := corrected_btrl_terminal_bound m.T f.posT m.X m.V f.vx f.conv f.closed ⟨_,f.uFeas⟩
    m.psi m.loss f.noBot f.dom m.lam f.curvature (fun i hi => (f.properties i hi).1)
    (fun i hi => (f.properties i hi).2.1) (fun i hi => (f.properties i hi).2.2)
    m.x f.xFeas (fun i hi => h_eq m i f.vx ▸ f.optimal i hi) m.u f.uFeas
  have att := btrl_real_round_minimizer_existsUnique m.T f.posT m.X m.V f.vx f.conv f.closed ⟨_,f.uFeas⟩
    m.psi m.loss f.noBot f.dom m.lam f.curvature (fun i hi => (f.properties i hi).1)
    (fun i hi => (f.properties i hi).2.1) (fun i hi => (f.properties i hi).2.2)
  refine ⟨?_,?_,facts_run m f,?_⟩
  · simpa only [bounds,sharp,weak,regret,baseline,movement,drift,terminal,r,regularizerValue,
      sub_eq_add_neg,neg_mul] using bound
  · intro i hi
    rw [h_eq m i f.vx]
    exact att i hi
  · have hr (t : ℕ) (v : ℝ) : r repeatedLast t v = v^2/2 := r_univ _ rfl t v
    have bad (p : ℝ) : IsMinOn (fun v => r repeatedLast 0 v + 2*(repeatedLast.loss 0 v).toReal) repeatedLast.V p ↔ p = 2/3 := by
      constructor
      · intro hmin
        have hh := hmin (Set.mem_univ (2/3 : ℝ))
        change r repeatedLast 0 p + 2*((((p-1)^2/2:ℝ):EReal).toReal) ≤ r repeatedLast 0 (2/3) + _ at hh
        simp only [hr,EReal.toReal_coe] at hh
        change p^2/2 + 2*((p-1)^2/2) ≤ (2/3:ℝ)^2/2 + 2*((2/3-1)^2/2) at hh
        by_contra hn
        nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr hn)]
      · rintro rfl v _
        change r repeatedLast 0 (2/3) + _ ≤ r repeatedLast 0 v + _
        simp only [hr]
        change (2/3:ℝ)^2/2 + 2*((2/3-1)^2/2) ≤ v^2/2 + 2*((v-1)^2/2)
        simp only [repeatedLast,EReal.toReal_coe] at *
        nlinarith [sq_nonneg (v-2/3)]
    refine ⟨by norm_num [m,repeatedLast],by rfl,by norm_num [m,repeatedLast],?_,?_,?_,rep_min,bad,?_,?_⟩ <;>
      norm_num [m,sharp,weak,regret,baseline,terminal,movement,drift,hr,repeatedLast,Real.norm_eq_abs]

theorem two_round_endpoint_and_drift :
    let m := twoRounds
    bounds m ∧ attainment m ∧ runValid m ∧
    m.x 0 = 1 ∧ m.x 1 = 2 ∧ m.x 2 = 100 ∧ m.x 2 ≠ m.x (m.T-1) ∧
    m.loss 0 4 = ⊤ ∧ m.loss 1 4 = ⊤ ∧ regret m = -7 ∧ baseline m = -(1/2 : ℝ) ∧
    movement m = -(1/2 : ℝ) ∧ drift m = -2 ∧ terminal m = -4 ∧ sharp m = -7 ∧ weak m = -3 := by
  let m := twoRounds
  have f : Facts m := two_facts
  have bound := corrected_btrl_terminal_bound m.T f.posT m.X m.V f.vx f.conv f.closed ⟨_,f.uFeas⟩
    m.psi m.loss f.noBot f.dom m.lam f.curvature (fun i hi => (f.properties i hi).1)
    (fun i hi => (f.properties i hi).2.1) (fun i hi => (f.properties i hi).2.2)
    m.x f.xFeas (fun i hi => h_eq m i f.vx ▸ f.optimal i hi) m.u f.uFeas
  have att := btrl_real_round_minimizer_existsUnique m.T f.posT m.X m.V f.vx f.conv f.closed ⟨_,f.uFeas⟩
    m.psi m.loss f.noBot f.dom m.lam f.curvature (fun i hi => (f.properties i hi).1)
    (fun i hi => (f.properties i hi).2.1) (fun i hi => (f.properties i hi).2.2)
  refine ⟨?_,?_,facts_run m f,?_⟩
  · simpa only [bounds,sharp,weak,regret,baseline,movement,drift,terminal,r,regularizerValue,
      sub_eq_add_neg,neg_mul] using bound
  · intro i hi
    rw [h_eq m i f.vx]
    exact att i hi
  · have hr (n : ℕ) (v : ℝ) : r twoRounds n v = if n=0 then v^2/2 else v^2 :=
      r_univ _ rfl n v
    dsimp only [m,regret,sharp,weak,baseline,movement,drift,terminal]
    simp only [hr]
    norm_num [twoRounds, Finset.sum_range_succ,Real.norm_eq_abs]

end BanditRL.OnlineBTRLCanary
