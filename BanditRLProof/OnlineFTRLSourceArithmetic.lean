-- Partial extended-real arithmetic for the supplied FTRL minimizing-run interface.
import BanditRLProof.OnlineFTRLFiniteIdentity
noncomputable section
attribute [local instance] Classical.propDecidable
open Set Finset
namespace BanditRL.OnlineFTRLSourceArithmetic

-- Option.none records undefined source arithmetic, not an extended-real value.
def sourceAdd (a b : EReal) : Option EReal :=
  if (a = ⊤ ∧ b = ⊥) ∨ (a = ⊥ ∧ b = ⊤) then none else some (a + b)
def sourceSub (a b : EReal) : Option EReal := sourceAdd a (-b)
def sourceSum : ℕ → (ℕ → Option EReal) → Option EReal
  | 0, _ => some 0
  | n + 1, f => (sourceSum n f).bind (fun a => (f n).bind (sourceAdd a))

def objective {E : Type*} (psi : ℕ → E → ℝ) (loss : ℕ → E → EReal)
    (t : ℕ) (v : E) : EReal :=
  (psi t v : EReal) + ∑ i ∈ range t, loss i v

def sourceLHS {E : Type*} (T : ℕ) (loss : ℕ → E → EReal)
    (x : ℕ → E) (u : E) : Option EReal :=
  sourceSum T (fun t => sourceSub (loss t (x t)) (loss t u))

def sourceRHS {E : Type*} (T : ℕ) (V : Set E) (psi : ℕ → E → ℝ)
    (loss : ℕ → E → EReal) (x : ℕ → E) (u : E) : Option EReal :=
  let F := objective psi loss
  let brackets := sourceSum T (fun t =>
    (sourceSub (F t (x t)) (F (t + 1) (x (t + 1)))).bind
      (fun delta => sourceAdd delta (loss t (x t))))
  -- Preserve the displayed outer left association: initial + sum + a_T - F_T(u).
  brackets.bind (fun s =>
    (sourceAdd ((psi T u - sInf (psi 0 '' V) : ℝ) : EReal) s).bind
      (fun q => (sourceAdd q (F T (x T))).bind
        (fun r => sourceSub r (F T u))))

def playedTop {E : Type*} (T : ℕ) (loss : ℕ → E → EReal) (x : ℕ → E) : Prop :=
  ∃ t < T, loss t (x t) = ⊤
def comparatorTop {E : Type*} (T : ℕ) (loss : ℕ → E → EReal) (u : E) : Prop :=
  ∃ t < T, loss t u = ⊤

-- Independent ordinary-arithmetic cases: no constructor for opposing infinities.
private inductive OrdinaryAdd : EReal → EReal → EReal → Prop
  | finite (a b : ℝ) : OrdinaryAdd a b (↑(a + b))
  | finiteTop (a : ℝ) : OrdinaryAdd a ⊤ ⊤
  | topFinite (b : ℝ) : OrdinaryAdd ⊤ b ⊤
  | topTop : OrdinaryAdd ⊤ ⊤ ⊤
  | finiteBot (a : ℝ) : OrdinaryAdd a ⊥ ⊥
  | botFinite (b : ℝ) : OrdinaryAdd ⊥ b ⊥
  | botBot : OrdinaryAdd ⊥ ⊥ ⊥

private theorem sourceAdd_sound {a b c : EReal}
    (h : sourceAdd a b = some c) : OrdinaryAdd a b c := by
  cases a <;> cases b <;>
    simp [sourceAdd, ← EReal.coe_add] at h <;> subst c <;> constructor

private theorem sourceAdd_complete {a b c : EReal}
    (h : OrdinaryAdd a b c) : sourceAdd a b = some c := by
  cases h <;> simp [sourceAdd, EReal.coe_add]

private theorem sourceAdd_meaning {a b c : EReal} :
    sourceAdd a b = some c ↔ OrdinaryAdd a b c :=
  ⟨sourceAdd_sound, sourceAdd_complete⟩

private theorem sourceSub_meaning {a b c : EReal} :
    sourceSub a b = some c ↔ OrdinaryAdd a (-b) c := by
  exact sourceAdd_meaning

private theorem sourceAdd_undefined (a b : EReal) :
    sourceAdd a b = none ↔ (a = ⊤ ∧ b = ⊥) ∨ (a = ⊥ ∧ b = ⊤) := by
  unfold sourceAdd
  split <;> simp_all

private theorem sourceSub_undefined (a b : EReal) :
    sourceSub a b = none ↔ (a = ⊤ ∧ b = ⊤) ∨ (a = ⊥ ∧ b = ⊥) := by
  simp [sourceSub, sourceAdd_undefined]

private inductive OrdinarySum (f : ℕ → Option EReal) : ℕ → EReal → Prop
  | zero : OrdinarySum f 0 0
  | succ {n : ℕ} {a b c : EReal} : OrdinarySum f n a → f n = some b →
      OrdinaryAdd a b c → OrdinarySum f (n + 1) c

private theorem sourceSum_complete {f : ℕ → Option EReal} {n : ℕ} {c : EReal}
    (h : OrdinarySum f n c) : sourceSum n f = some c := by
  induction h with
  | zero => rfl
  | succ ha hb hab ih => simp [sourceSum, ih, hb, sourceAdd_complete hab]

private theorem sourceSum_sound (n : ℕ) (f : ℕ → Option EReal) (c : EReal)
    (h : sourceSum n f = some c) : OrdinarySum f n c := by
  induction n generalizing c with
  | zero =>
    have hc : c = 0 := by simpa [sourceSum] using h.symm
    subst c
    exact OrdinarySum.zero
  | succ n ih =>
    simp only [sourceSum, Option.bind_eq_some_iff] at h
    obtain ⟨a, ha, b, hb, hab⟩ := h
    exact OrdinarySum.succ (ih a ha) hb (sourceAdd_sound hab)

private theorem sourceSum_none_of_none (n : ℕ) (f : ℕ → Option EReal)
    (h : ∃ i < n, f i = none) : sourceSum n f = none := by
  induction n with
  | zero => simp at h
  | succ n ih =>
    obtain ⟨i, hi, hfi⟩ := h
    by_cases hin : i < n
    · simp [sourceSum, ih ⟨i, hin, hfi⟩]
    · have hie : i = n := by omega
      subst i
      simp [sourceSum, hfi]


private theorem sourceAdd_finite (a b : ℝ) :
    sourceAdd (a : EReal) (b : EReal) = some ((a + b : ℝ) : EReal) := by
  simp [sourceAdd, EReal.coe_add]

private theorem sourceSub_finite (a b : ℝ) :
    sourceSub (a : EReal) (b : EReal) = some ((a - b : ℝ) : EReal) := by
  simp [sourceSub, sourceAdd, EReal.coe_sub, sub_eq_add_neg]

private theorem sourceAdd_noBot (a b : EReal) (ha : a ≠ ⊥) (hb : b ≠ ⊥) :
    sourceAdd a b = some (a + b) := by
  simp [sourceAdd, ha, hb]

private theorem finite_sum_noBot (n : ℕ) (f : ℕ → EReal)
    (hf : ∀ i < n, f i ≠ ⊥) : (∑ i ∈ range n, f i) ≠ ⊥ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, EReal.add_ne_bot_iff]
    exact ⟨ih (by intro i hi; exact hf i (by omega)), hf n (by omega)⟩

private theorem sourceSum_noBot (n : ℕ) (f : ℕ → EReal)
    (hf : ∀ i < n, f i ≠ ⊥) :
    sourceSum n (fun i => some (f i)) = some (∑ i ∈ range n, f i) := by
  induction n with
  | zero => simp [sourceSum]
  | succ n ih =>
    have hn : ∀ i < n, f i ≠ ⊥ := by intro i hi; exact hf i (by omega)
    simp only [sourceSum, ih hn, Option.bind_some, sum_range_succ]
    exact sourceAdd_noBot _ _ (finite_sum_noBot n f hn) (hf n (by omega))

private theorem sourceSum_finite (n : ℕ) (f : ℕ → ℝ) :
    sourceSum n (fun i => some (f i : EReal)) = some ((∑ i ∈ range n, f i : ℝ) : EReal) := by
  induction n with
  | zero => simp [sourceSum]
  | succ n ih => simp [sourceSum, ih, sourceAdd_finite, sum_range_succ]

private theorem objective_noBot {E : Type*} (psi : ℕ → E → ℝ)
    (loss : ℕ → E → EReal) (n : ℕ) (v : E)
    (hf : ∀ i < n, loss i v ≠ ⊥) : objective psi loss n v ≠ ⊥ := by
  exact EReal.add_ne_bot_iff.mpr ⟨EReal.coe_ne_bot _, finite_sum_noBot n (fun i => loss i v) hf⟩

private theorem objective_partial_interpretation {E : Type*} (psi : ℕ → E → ℝ)
    (loss : ℕ → E → EReal) (n : ℕ) (v : E)
    (hf : ∀ i < n, loss i v ≠ ⊥) :
    (sourceSum n (fun i => some (loss i v))).bind
      (fun p => sourceAdd (psi n v : EReal) p) = some (objective psi loss n v) := by
  rw [sourceSum_noBot n (fun i => loss i v) hf]
  exact sourceAdd_noBot _ _ (EReal.coe_ne_bot _) (finite_sum_noBot n (fun i => loss i v) hf)


private theorem sum_finite_iff (n : ℕ) (f : ℕ → EReal)
    (hf : ∀ i < n, f i ≠ ⊥) :
    (∑ i ∈ range n, f i) ≠ ⊤ ↔ ∀ i < n, f i ≠ ⊤ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : ∀ i < n, f i ≠ ⊥ := by intro i hi; exact hf i (by omega)
    rw [sum_range_succ, EReal.add_ne_top_iff_ne_top₂
      (finite_sum_noBot n f hn) (hf n (by omega)), ih hn]
    constructor
    · rintro ⟨hp, hl⟩ i hi
      by_cases h : i < n
      · exact hp i h
      · have : i = n := by omega
        simpa [this] using hl
    · intro h
      exact ⟨fun i hi => h i (by omega), h n (by omega)⟩

private theorem objective_finite_iff {E : Type*} (psi : ℕ → E → ℝ)
    (loss : ℕ → E → EReal) (n : ℕ) (v : E)
    (hf : ∀ i < n, loss i v ≠ ⊥) :
    objective psi loss n v ≠ ⊤ ↔ ∀ i < n, loss i v ≠ ⊤ := by
  unfold objective
  rw [EReal.add_ne_top_iff_ne_top₂ (EReal.coe_ne_bot _)
    (finite_sum_noBot n (fun i => loss i v) hf)]
  constructor
  · intro h
    exact (sum_finite_iff n (fun i => loss i v) hf).mp h.2
  · intro h
    exact ⟨EReal.coe_ne_top _, (sum_finite_iff n (fun i => loss i v) hf).mpr h⟩

private theorem attained_initial_minimum {E : Type*} (V : Set E)
    (psi : ℕ → E → ℝ) (loss : ℕ → E → EReal) (x : ℕ → E)
    (hx : x 0 ∈ V) (hmin : IsMinOn (objective psi loss 0) V (x 0)) :
    sInf (psi 0 '' V) = psi 0 (x 0) := by
  have hm : IsMinOn (psi 0) V (x 0) := by
    intro v hv
    simpa only [objective, sum_range_zero, add_zero, EReal.coe_le_coe_iff] using hmin hv
  have hmem : psi 0 (x 0) ∈ psi 0 '' V := ⟨x 0, hx, rfl⟩
  have hb : BddBelow (psi 0 '' V) := by
    refine ⟨psi 0 (x 0), ?_⟩
    rintro z ⟨v, hv, rfl⟩
    exact hm hv
  apply le_antisymm (csInf_le hb hmem)
  apply le_csInf ⟨_, hmem⟩
  rintro z ⟨v, hv, rfl⟩
  exact hm hv

private theorem selected_top_step {E : Type*} (T t : ℕ) (V : Set E)
    (psi : ℕ → E → ℝ) (loss : ℕ → E → EReal) (x : ℕ → E)
    (hbot : ∀ i < T, ∀ v, loss i v ≠ ⊥) (ht : t < T)
    (hx : x t ∈ V) (hmin : IsMinOn (objective psi loss (t+1)) V (x (t+1)))
    (hprev : objective psi loss t (x t) ≠ ⊤)
    (hnext : objective psi loss (t+1) (x (t+1)) = ⊤) : loss t (x t) = ⊤ := by
  have hm := hmin hx
  rw [hnext] at hm
  have hnew : objective psi loss (t+1) (x t) = ⊤ := top_le_iff.mp hm
  by_contra hp
  have hn : ∀ i < t+1, loss i (x t) ≠ ⊥ := by intro i hi; exact hbot i (by omega) _
  have hold := (objective_finite_iff psi loss t (x t)
    (by intro i hi; exact hbot i (by omega) _)).mp hprev
  have hfinite := (objective_finite_iff psi loss (t+1) (x t) hn).mpr (by
    intro i hi
    by_cases h : i < t
    · exact hold i h
    · have : i = t := by omega
      simpa [this] using hp)
  exact hfinite hnew

private theorem first_selected_top_obstruction {E : Type*} (T : ℕ) (V : Set E)
    (psi : ℕ → E → ℝ) (loss : ℕ → E → EReal) (x : ℕ → E)
    (hbot : ∀ i < T, ∀ v, loss i v ≠ ⊥)
    (hx : ∀ t ≤ T, x t ∈ V)
    (hmin : ∀ t ≤ T, IsMinOn (objective psi loss t) V (x t))
    (hbad : ∃ j ≤ T, objective psi loss j (x j) = ⊤) :
    ∃ t < T, (sourceSub (objective psi loss t (x t))
      (objective psi loss (t+1) (x (t+1)))).bind
        (fun delta => sourceAdd delta (loss t (x t))) = none := by
  let j := Nat.find hbad
  have hj : j ≤ T ∧ objective psi loss j (x j) = ⊤ := Nat.find_spec hbad
  have hjpos : 0 < j := by
    by_contra hn
    have hz : j = 0 := by omega
    have hf : objective psi loss 0 (x 0) ≠ ⊤ := by simp [objective]
    exact hf (by simpa [hz] using hj.2)
  let t := j - 1
  have hsucc : t + 1 = j := by dsimp [t]; omega
  have ht : t < T := by omega
  have hprev : objective psi loss t (x t) ≠ ⊤ := by
    intro htop
    exact (Nat.find_min hbad (by dsimp [j, t]; omega)) ⟨by omega, htop⟩
  have hnext : objective psi loss (t+1) (x (t+1)) = ⊤ := by simpa [hsucc] using hj.2
  have hp := selected_top_step T t V psi loss x hbot ht (hx t (by omega))
    (hmin (t+1) (by omega)) hprev hnext
  have hb : objective psi loss t (x t) ≠ ⊥ := objective_noBot psi loss t (x t)
    (by intro i hi; exact hbot i (by omega) _)
  refine ⟨t, ht, ?_⟩
  simp [hnext, hp, sourceSub, sourceAdd, hprev, hb]

private theorem sourceRHS_none_selected_top {E : Type*} (T : ℕ) (V : Set E)
    (psi : ℕ → E → ℝ) (loss : ℕ → E → EReal) (x : ℕ → E) (u : E)
    (hbot : ∀ i < T, ∀ v, loss i v ≠ ⊥)
    (hx : ∀ t ≤ T, x t ∈ V)
    (hmin : ∀ t ≤ T, IsMinOn (objective psi loss t) V (x t))
    (hbad : ∃ j ≤ T, objective psi loss j (x j) = ⊤) :
    sourceRHS T V psi loss x u = none := by
  have h := first_selected_top_obstruction T V psi loss x hbot hx hmin hbad
  dsimp only [sourceRHS]
  rw [sourceSum_none_of_none _ _ h]
  rfl


private theorem sourceSum_congr (n : ℕ) (f g : ℕ → Option EReal)
    (h : ∀ i < n, f i = g i) : sourceSum n f = sourceSum n g := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sourceSum, ih (by intro i hi; exact h i (by omega)), h n (by omega)]

private theorem sourceLHS_finite {E : Type*} (T : ℕ) (loss : ℕ → E → EReal)
    (x : ℕ → E) (u : E) (hbot : ∀ i < T, ∀ v, loss i v ≠ ⊥)
    (hp : ∀ i < T, loss i (x i) ≠ ⊤) (hc : ∀ i < T, loss i u ≠ ⊤) :
    sourceLHS T loss x u =
      some ((∑ i ∈ range T, ((loss i (x i)).toReal - (loss i u).toReal) : ℝ) : EReal) := by
  unfold sourceLHS
  trans sourceSum T (fun i => some (((loss i (x i)).toReal - (loss i u).toReal : ℝ) : EReal))
  · apply sourceSum_congr
    intro i hi
    have hpi := EReal.coe_toReal (hp i hi) (hbot i hi (x i))
    have hci := EReal.coe_toReal (hc i hi) (hbot i hi u)
    rw [← hpi, ← hci]
    simpa using sourceSub_finite (loss i (x i)).toReal (loss i u).toReal
  · exact sourceSum_finite _ _

private theorem sourceRHS_finite {E : Type*} (T : ℕ) (V : Set E)
    (psi : ℕ → E → ℝ) (loss : ℕ → E → EReal) (x : ℕ → E) (u : E)
    (hbot : ∀ i < T, ∀ v, loss i v ≠ ⊥)
    (hs : ∀ i ≤ T, objective psi loss i (x i) ≠ ⊤)
    (hp : ∀ i < T, loss i (x i) ≠ ⊤) (hc : ∀ i < T, loss i u ≠ ⊤) :
    sourceRHS T V psi loss x u = some ((psi T u - sInf (psi 0 '' V) +
      (∑ i ∈ range T, ((objective psi loss i (x i)).toReal -
        (objective psi loss (i+1) (x (i+1))).toReal + (loss i (x i)).toReal)) +
      (objective psi loss T (x T)).toReal - (objective psi loss T u).toReal : ℝ) : EReal) := by
  have ha : ∀ i ≤ T, ((objective psi loss i (x i)).toReal : EReal) =
      objective psi loss i (x i) := by
    intro i hi
    exact EReal.coe_toReal (hs i hi) (objective_noBot psi loss i (x i)
      (by intro j hj; exact hbot j (by omega) _))
  have hu : ((objective psi loss T u).toReal : EReal) = objective psi loss T u :=
    EReal.coe_toReal ((objective_finite_iff psi loss T u (fun i hi => hbot i hi u)).mpr hc)
      (objective_noBot psi loss T u (fun i hi => hbot i hi u))
  have hsum : sourceSum T (fun i =>
      (sourceSub (objective psi loss i (x i)) (objective psi loss (i+1) (x (i+1)))).bind
        (fun z => sourceAdd z (loss i (x i)))) =
      some ((∑ i ∈ range T, ((objective psi loss i (x i)).toReal -
        (objective psi loss (i+1) (x (i+1))).toReal + (loss i (x i)).toReal) : ℝ) : EReal) := by
    trans sourceSum T (fun i => some (((objective psi loss i (x i)).toReal -
      (objective psi loss (i+1) (x (i+1))).toReal + (loss i (x i)).toReal : ℝ) : EReal))
    · apply sourceSum_congr
      intro i hi
      have hpi := EReal.coe_toReal (hp i hi) (hbot i hi (x i))
      rw [← ha i (by omega), ← ha (i+1) (by omega), ← hpi]
      simp only [sourceSub_finite, Option.bind_some, sourceAdd_finite, EReal.toReal_coe]
    · exact sourceSum_finite _ _
  dsimp only [sourceRHS]
  rw [hsum]
  simp only [Option.bind_some]
  rw [sourceAdd_finite, Option.bind_some, ← ha T (le_refl T), sourceAdd_finite,
    Option.bind_some, ← hu, sourceSub_finite]
  simp only [EReal.toReal_coe]

private theorem finite_source_bridge
    (d T : ℕ) (X V : Set (EuclideanSpace ℝ (Fin d)))
    (hVX : V ⊆ X) (hVclosed : IsClosed V) (hV : V.Nonempty)
    (psi : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (loss : ℕ → EuclideanSpace ℝ (Fin d) → EReal)
    (hbot : ∀ i < T, ∀ v, loss i v ≠ ⊥)
    (x : ℕ → EuclideanSpace ℝ (Fin d)) (u : EuclideanSpace ℝ (Fin d)) (hu : u ∈ X)
    (hx : ∀ t ≤ T, x t ∈ V)
    (hmin : ∀ t ≤ T, IsMinOn (objective psi loss t) V (x t))
    (hs : ∀ t ≤ T, objective psi loss t (x t) ≠ ⊤)
    (hp : ∀ t < T, loss t (x t) ≠ ⊤) (hc : ∀ t < T, loss t u ≠ ⊤) :
    sourceLHS T loss x u = sourceRHS T V psi loss x u ∧ (sourceLHS T loss x u).isSome := by
  have h := OnlineFTRL.lemma7_1_finite_values d T X V hVX hVclosed hV psi loss hbot x u hu hx hmin hs hp hc
  rw [sourceLHS_finite T loss x u hbot hp hc, sourceRHS_finite T V psi loss x u hbot hs hp hc]
  constructor
  · exact congrArg (fun r : ℝ => some (r : EReal)) h
  · rfl


private theorem finite_sum_top_iff (n : ℕ) (f : ℕ → EReal)
    (hf : ∀ i < n, f i ≠ ⊥) :
    (∑ i ∈ range n, f i) = ⊤ ↔ ∃ i < n, f i = ⊤ := by
  constructor
  · intro ht
    by_contra hn
    push_neg at hn
    exact ((sum_finite_iff n f hf).mpr hn) ht
  · rintro ⟨i, hi, htop⟩
    by_contra hn
    exact ((sum_finite_iff n f hf).mp hn i hi) htop

private theorem coe_add_top_iff (r : ℝ) (p : EReal) :
    (r : EReal) + p = ⊤ ↔ p = ⊤ := by
  cases p <;> simp [← EReal.coe_add]

private theorem selected_bracket_sum {E : Type*} (T : ℕ)
    (psi : ℕ → E → ℝ) (loss : ℕ → E → EReal) (x : ℕ → E)
    (hbot : ∀ i < T, ∀ v, loss i v ≠ ⊥)
    (hs : ∀ i ≤ T, objective psi loss i (x i) ≠ ⊤) :
    ∃ s : EReal,
      sourceSum T (fun i => (sourceSub (objective psi loss i (x i))
        (objective psi loss (i+1) (x (i+1)))).bind
          (fun z => sourceAdd z (loss i (x i)))) = some s ∧
      s ≠ ⊥ ∧ (s = ⊤ ↔ playedTop T loss x) := by
  let f := fun i =>
    (((objective psi loss i (x i)).toReal -
      (objective psi loss (i+1) (x (i+1))).toReal : ℝ) : EReal) + loss i (x i)
  have hn : ∀ i < T, f i ≠ ⊥ := by
    intro i hi
    exact EReal.add_ne_bot_iff.mpr ⟨EReal.coe_ne_bot _, hbot i hi _⟩
  have he : sourceSum T (fun i => (sourceSub (objective psi loss i (x i))
      (objective psi loss (i+1) (x (i+1)))).bind
        (fun z => sourceAdd z (loss i (x i)))) = sourceSum T (fun i => some (f i)) := by
    apply sourceSum_congr
    intro i hi
    have ha (j : ℕ) (hj : j ≤ T) := EReal.coe_toReal (hs j hj)
      (objective_noBot psi loss j (x j) (by intro k hk; exact hbot k (by omega) _))
    rw [← ha i (by omega), ← ha (i+1) (by omega), sourceSub_finite]
    simp only [Option.bind_some, EReal.toReal_coe]
    exact sourceAdd_noBot _ _ (EReal.coe_ne_bot _) (hbot i hi _)
  refine ⟨∑ i ∈ range T, f i, he.trans (sourceSum_noBot T f hn), finite_sum_noBot T f hn, ?_⟩
  rw [finite_sum_top_iff T f hn]
  simp only [f, coe_add_top_iff, playedTop]

private theorem comparator_objective_top_iff {E : Type*} (T : ℕ)
    (psi : ℕ → E → ℝ) (loss : ℕ → E → EReal) (u : E)
    (hbot : ∀ i < T, ∀ v, loss i v ≠ ⊥) :
    objective psi loss T u = ⊤ ↔ comparatorTop T loss u := by
  unfold objective comparatorTop
  rw [coe_add_top_iff, finite_sum_top_iff T (fun i => loss i u) (fun i hi => hbot i hi u)]

private theorem checked_tail_domain (r a : ℝ) (s b : EReal)
    (hs : s ≠ ⊥) (hb : b ≠ ⊥) :
    ((sourceAdd (r : EReal) s).bind (fun q =>
      (sourceAdd q (a : EReal)).bind (fun z => sourceSub z b))).isSome ↔
        ¬ (s = ⊤ ∧ b = ⊤) := by
  cases s <;> cases b <;> simp_all [sourceAdd, sourceSub, ← EReal.coe_add]

private theorem selected_RHS_domain {E : Type*} (T : ℕ) (V : Set E)
    (psi : ℕ → E → ℝ) (loss : ℕ → E → EReal) (x : ℕ → E) (u : E)
    (hbot : ∀ i < T, ∀ v, loss i v ≠ ⊥)
    (hs : ∀ i ≤ T, objective psi loss i (x i) ≠ ⊤) :
    (sourceRHS T V psi loss x u).isSome ↔
      ¬ (playedTop T loss x ∧ comparatorTop T loss u) := by
  obtain ⟨s, he, hsb, hst⟩ := selected_bracket_sum T psi loss x hbot hs
  have ha := EReal.coe_toReal (hs T (le_refl T))
    (objective_noBot psi loss T (x T) (fun i hi => hbot i hi _))
  have hb := objective_noBot psi loss T u (fun i hi => hbot i hi u)
  dsimp only [sourceRHS]
  rw [he]
  simp only [Option.bind_some]
  rw [← ha, checked_tail_domain _ _ _ _ hsb hb, hst, comparator_objective_top_iff T psi loss u hbot]

theorem source_arithmetic_domain
    (d T : ℕ) (X V : Set (EuclideanSpace ℝ (Fin d)))
    (hVX : V ⊆ X) (hVclosed : IsClosed V) (hV : V.Nonempty)
    (psi : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (loss : ℕ → EuclideanSpace ℝ (Fin d) → EReal)
    (hbot : ∀ i < T, ∀ v, loss i v ≠ ⊥)
    (x : ℕ → EuclideanSpace ℝ (Fin d))
    (u : EuclideanSpace ℝ (Fin d)) (hu : u ∈ X)
    (hx : ∀ t ≤ T, x t ∈ V)
    (hmin : ∀ t ≤ T, IsMinOn (objective psi loss t) V (x t)) :
    (sourceRHS T V psi loss x u).isSome ↔
      (∀ t ≤ T, objective psi loss t (x t) ≠ ⊤) ∧
      ¬ (playedTop T loss x ∧ comparatorTop T loss u) := by
  by_cases hs : ∀ i ≤ T, objective psi loss i (x i) ≠ ⊤
  · rw [selected_RHS_domain T V psi loss x u hbot hs]
    exact (and_iff_right hs).symm
  · have hbad : ∃ i ≤ T, objective psi loss i (x i) = ⊤ := by
      push_neg at hs
      exact hs
    rw [sourceRHS_none_selected_top T V psi loss x u hbot hx hmin hbad]
    simp only [Option.isSome_none, Bool.false_eq_true, false_iff, not_and]
    intro hfinite
    obtain ⟨i, hi, htop⟩ := hbad
    exact False.elim (hfinite i hi htop)


private theorem sourceAdd_finite_left (r : ℝ) (b : EReal) :
    sourceAdd (r : EReal) b = some ((r : EReal) + b) := by simp [sourceAdd]
private theorem sourceAdd_finite_right (a : EReal) (r : ℝ) :
    sourceAdd a (r : EReal) = some (a + (r : EReal)) := by simp [sourceAdd]

private theorem finite_sum_noTop (n : ℕ) (f : ℕ → EReal)
    (hf : ∀ i < n, f i ≠ ⊤) : (∑ i ∈ range n, f i) ≠ ⊤ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    exact EReal.add_ne_top (ih (by intro i hi; exact hf i (by omega))) (hf n (by omega))

private theorem sourceSum_noTop (n : ℕ) (f : ℕ → EReal)
    (hf : ∀ i < n, f i ≠ ⊤) :
    sourceSum n (fun i => some (f i)) = some (∑ i ∈ range n, f i) := by
  induction n with
  | zero => simp [sourceSum]
  | succ n ih =>
    have hn : ∀ i < n, f i ≠ ⊤ := by intro i hi; exact hf i (by omega)
    simp only [sourceSum, ih hn, Option.bind_some, sum_range_succ]
    simp [sourceAdd, finite_sum_noTop n f hn, hf n (by omega)]

private theorem finite_sum_bot_iff (n : ℕ) (f : ℕ → EReal) :
    (∑ i ∈ range n, f i) = ⊥ ↔ ∃ i < n, f i = ⊥ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, EReal.add_eq_bot_iff, ih]
    constructor
    · rintro (⟨i, hi, hb⟩ | hb)
      · exact ⟨i, by omega, hb⟩
      · exact ⟨n, by omega, hb⟩
    · rintro ⟨i, hi, hb⟩
      by_cases h : i < n
      · exact Or.inl ⟨i, h, hb⟩
      · have : i = n := by omega
        exact Or.inr (by simpa [this] using hb)

private theorem sourceLHS_played_top {E : Type*} (T : ℕ)
    (loss : ℕ → E → EReal) (x : ℕ → E) (u : E)
    (hbot : ∀ i < T, ∀ v, loss i v ≠ ⊥)
    (hp : playedTop T loss x) (hc : ¬ comparatorTop T loss u) :
    sourceLHS T loss x u = some ⊤ := by
  have hc' : ∀ i < T, loss i u ≠ ⊤ := by simpa [comparatorTop] using hc
  let f := fun i => loss i (x i) + ((-(loss i u).toReal : ℝ) : EReal)
  have hn : ∀ i < T, f i ≠ ⊥ := by
    intro i hi
    exact EReal.add_ne_bot_iff.mpr ⟨hbot i hi _, EReal.coe_ne_bot _⟩
  have he : sourceLHS T loss x u = sourceSum T (fun i => some (f i)) := by
    apply sourceSum_congr
    intro i hi
    have hci := EReal.coe_toReal (hc' i hi) (hbot i hi u)
    rw [← hci]
    simp only [sourceSub, ← EReal.coe_neg, sourceAdd_finite_right, EReal.toReal_coe]
    rfl
  rw [he, sourceSum_noBot T f hn]
  congr 1
  apply (finite_sum_top_iff T f hn).mpr
  obtain ⟨i, hi, hpi⟩ := hp
  exact ⟨i, hi, by simp [f, hpi]⟩

private theorem sourceLHS_comparator_top {E : Type*} (T : ℕ)
    (loss : ℕ → E → EReal) (x : ℕ → E) (u : E)
    (hbot : ∀ i < T, ∀ v, loss i v ≠ ⊥)
    (hp : ¬ playedTop T loss x) (hc : comparatorTop T loss u) :
    sourceLHS T loss x u = some ⊥ := by
  have hp' : ∀ i < T, loss i (x i) ≠ ⊤ := by simpa [playedTop] using hp
  let f := fun i => ((loss i (x i)).toReal : EReal) + (-loss i u)
  have hn : ∀ i < T, f i ≠ ⊤ := by
    intro i hi
    exact EReal.add_ne_top (EReal.coe_ne_top _) (by simpa using hbot i hi u)
  have he : sourceLHS T loss x u = sourceSum T (fun i => some (f i)) := by
    apply sourceSum_congr
    intro i hi
    have hpi := EReal.coe_toReal (hp' i hi) (hbot i hi (x i))
    rw [← hpi]
    simp [sourceSub, sourceAdd_finite_left, f]
  rw [he, sourceSum_noTop T f hn]
  congr 1
  apply (finite_sum_bot_iff T f).mpr
  obtain ⟨i, hi, hci⟩ := hc
  exact ⟨i, hi, by simp [f, hci]⟩

private theorem sourceRHS_played_top {E : Type*} (T : ℕ) (V : Set E)
    (psi : ℕ → E → ℝ) (loss : ℕ → E → EReal) (x : ℕ → E) (u : E)
    (hbot : ∀ i < T, ∀ v, loss i v ≠ ⊥)
    (hs : ∀ i ≤ T, objective psi loss i (x i) ≠ ⊤)
    (hp : playedTop T loss x) (hc : ¬ comparatorTop T loss u) :
    sourceRHS T V psi loss x u = some ⊤ := by
  obtain ⟨s, he, hsb, hst⟩ := selected_bracket_sum T psi loss x hbot hs
  have hst' : s = ⊤ := hst.mpr hp
  have ha := EReal.coe_toReal (hs T (le_refl T))
    (objective_noBot psi loss T (x T) (fun i hi => hbot i hi _))
  have hc' : objective psi loss T u ≠ ⊤ := by
    intro h
    exact hc ((comparator_objective_top_iff T psi loss u hbot).mp h)
  have hb := EReal.coe_toReal hc' (objective_noBot psi loss T u (fun i hi => hbot i hi u))
  dsimp only [sourceRHS]
  rw [he, hst']
  simp only [Option.bind_some]
  rw [← ha, ← hb]
  simp [sourceAdd, sourceSub, ← EReal.coe_add, ← EReal.coe_sub, ← EReal.coe_neg]

private theorem sourceRHS_comparator_top {E : Type*} (T : ℕ) (V : Set E)
    (psi : ℕ → E → ℝ) (loss : ℕ → E → EReal) (x : ℕ → E) (u : E)
    (hbot : ∀ i < T, ∀ v, loss i v ≠ ⊥)
    (hs : ∀ i ≤ T, objective psi loss i (x i) ≠ ⊤)
    (hp : ¬ playedTop T loss x) (hc : comparatorTop T loss u) :
    sourceRHS T V psi loss x u = some ⊥ := by
  obtain ⟨s, he, hsb, hst⟩ := selected_bracket_sum T psi loss x hbot hs
  have hsf : s ≠ ⊤ := fun h => hp (hst.mp h)
  have hscoe := EReal.coe_toReal hsf hsb
  have ha := EReal.coe_toReal (hs T (le_refl T))
    (objective_noBot psi loss T (x T) (fun i hi => hbot i hi _))
  have hb : objective psi loss T u = ⊤ := (comparator_objective_top_iff T psi loss u hbot).mpr hc
  dsimp only [sourceRHS]
  rw [he]
  simp only [Option.bind_some]
  rw [← hscoe, ← ha, hb]
  simp [sourceAdd, sourceSub, ← EReal.coe_add, ← EReal.coe_sub]

theorem played_top_source_identity
    (d T : ℕ) (X V : Set (EuclideanSpace ℝ (Fin d)))
    (hVX : V ⊆ X) (hVclosed : IsClosed V) (hV : V.Nonempty)
    (psi : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (loss : ℕ → EuclideanSpace ℝ (Fin d) → EReal)
    (hbot : ∀ i < T, ∀ v, loss i v ≠ ⊥)
    (x : ℕ → EuclideanSpace ℝ (Fin d))
    (u : EuclideanSpace ℝ (Fin d)) (hu : u ∈ X)
    (hx : ∀ t ≤ T, x t ∈ V)
    (hmin : ∀ t ≤ T, IsMinOn (objective psi loss t) V (x t))
    (hselected : ∀ t ≤ T, objective psi loss t (x t) ≠ ⊤)
    (hplayed : playedTop T loss x)
    (hcomparator : ¬ comparatorTop T loss u) :
    sourceLHS T loss x u = some ⊤ ∧ sourceRHS T V psi loss x u = some ⊤ := by
  exact ⟨sourceLHS_played_top T loss x u hbot hplayed hcomparator,
    sourceRHS_played_top T V psi loss x u hbot hselected hplayed hcomparator⟩

theorem comparator_top_source_identity
    (d T : ℕ) (X V : Set (EuclideanSpace ℝ (Fin d)))
    (hVX : V ⊆ X) (hVclosed : IsClosed V) (hV : V.Nonempty)
    (psi : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (loss : ℕ → EuclideanSpace ℝ (Fin d) → EReal)
    (hbot : ∀ i < T, ∀ v, loss i v ≠ ⊥)
    (x : ℕ → EuclideanSpace ℝ (Fin d))
    (u : EuclideanSpace ℝ (Fin d)) (hu : u ∈ X)
    (hx : ∀ t ≤ T, x t ∈ V)
    (hmin : ∀ t ≤ T, IsMinOn (objective psi loss t) V (x t))
    (hselected : ∀ t ≤ T, objective psi loss t (x t) ≠ ⊤)
    (hplayed : ¬ playedTop T loss x)
    (hcomparator : comparatorTop T loss u) :
    sourceLHS T loss x u = some ⊥ ∧ sourceRHS T V psi loss x u = some ⊥ := by
  exact ⟨sourceLHS_comparator_top T loss x u hbot hplayed hcomparator,
    sourceRHS_comparator_top T V psi loss x u hbot hselected hplayed hcomparator⟩


private theorem ordinaryAdd_top_left {a b c : EReal} (h : OrdinaryAdd a b c)
    (ha : a = ⊤) : c = ⊤ := by cases h <;> simp_all
private theorem ordinaryAdd_top_right {a b c : EReal} (h : OrdinaryAdd a b c)
    (hb : b = ⊤) : c = ⊤ := by cases h <;> simp_all
private theorem ordinaryAdd_bot_left {a b c : EReal} (h : OrdinaryAdd a b c)
    (ha : a = ⊥) : c = ⊥ := by cases h <;> simp_all
private theorem ordinaryAdd_bot_right {a b c : EReal} (h : OrdinaryAdd a b c)
    (hb : b = ⊥) : c = ⊥ := by cases h <;> simp_all

private theorem ordinarySum_contains_top {f : ℕ → Option EReal} {n : ℕ} {c : EReal}
    (h : OrdinarySum f n c) : (∃ i < n, f i = some ⊤) → c = ⊤ := by
  induction h with
  | zero => simp
  | @succ n a b c ha hb hab ih =>
    rintro ⟨i, hi, hfi⟩
    by_cases hin : i < n
    · exact ordinaryAdd_top_left hab (ih ⟨i, hin, hfi⟩)
    · have hie : i = n := by omega
      have hbe : b = ⊤ := by simpa [hie, hb] using hfi
      exact ordinaryAdd_top_right hab hbe

private theorem ordinarySum_contains_bot {f : ℕ → Option EReal} {n : ℕ} {c : EReal}
    (h : OrdinarySum f n c) : (∃ i < n, f i = some ⊥) → c = ⊥ := by
  induction h with
  | zero => simp
  | @succ n a b c ha hb hab ih =>
    rintro ⟨i, hi, hfi⟩
    by_cases hin : i < n
    · exact ordinaryAdd_bot_left hab (ih ⟨i, hin, hfi⟩)
    · have hie : i = n := by omega
      have hbe : b = ⊥ := by simpa [hie, hb] using hfi
      exact ordinaryAdd_bot_right hab hbe

private theorem sourceSum_opposite_infinities (n : ℕ) (f : ℕ → Option EReal)
    (hp : ∃ i < n, f i = some ⊤) (hn : ∃ i < n, f i = some ⊥) :
    sourceSum n f = none := by
  cases hs : sourceSum n f with
  | none => rfl
  | some c =>
    have hm := sourceSum_sound n f c hs
    have ht := ordinarySum_contains_top hm hp
    have hb := ordinarySum_contains_bot hm hn
    exact False.elim (top_ne_bot (ht.symm.trans hb))

private theorem sourceLHS_both_top {E : Type*} (T : ℕ)
    (loss : ℕ → E → EReal) (x : ℕ → E) (u : E)
    (hbot : ∀ i < T, ∀ v, loss i v ≠ ⊥)
    (hp : playedTop T loss x) (hc : comparatorTop T loss u) :
    sourceLHS T loss x u = none := by
  obtain ⟨i, hi, hpi⟩ := hp
  obtain ⟨j, hj, hcj⟩ := hc
  by_cases hci : loss i u = ⊤
  · exact sourceSum_none_of_none T _ ⟨i, hi, by simp [hpi, hci, sourceSub, sourceAdd]⟩
  by_cases hpj : loss j (x j) = ⊤
  · exact sourceSum_none_of_none T _ ⟨j, hj, by simp [hpj, hcj, sourceSub, sourceAdd]⟩
  apply sourceSum_opposite_infinities
  · refine ⟨i, hi, ?_⟩
    have he := EReal.coe_toReal hci (hbot i hi u)
    rw [hpi, ← he]
    simp [sourceSub, sourceAdd, ← EReal.coe_neg]
  · refine ⟨j, hj, ?_⟩
    have he := EReal.coe_toReal hpj (hbot j hj (x j))
    rw [hcj, ← he]
    simp [sourceSub, sourceAdd]

private theorem sourceRHS_both_top {E : Type*} (T : ℕ) (V : Set E)
    (psi : ℕ → E → ℝ) (loss : ℕ → E → EReal) (x : ℕ → E) (u : E)
    (hbot : ∀ i < T, ∀ v, loss i v ≠ ⊥)
    (hs : ∀ i ≤ T, objective psi loss i (x i) ≠ ⊤)
    (hp : playedTop T loss x) (hc : comparatorTop T loss u) :
    sourceRHS T V psi loss x u = none := by
  have hn : ¬ (sourceRHS T V psi loss x u).isSome := by
    rw [selected_RHS_domain T V psi loss x u hbot hs]
    exact not_not_intro ⟨hp, hc⟩
  cases he : sourceRHS T V psi loss x u with
  | none => rfl
  | some a => simp [he] at hn

theorem both_top_source_undefined
    (d T : ℕ) (X V : Set (EuclideanSpace ℝ (Fin d)))
    (hVX : V ⊆ X) (hVclosed : IsClosed V) (hV : V.Nonempty)
    (psi : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (loss : ℕ → EuclideanSpace ℝ (Fin d) → EReal)
    (hbot : ∀ i < T, ∀ v, loss i v ≠ ⊥)
    (x : ℕ → EuclideanSpace ℝ (Fin d))
    (u : EuclideanSpace ℝ (Fin d)) (hu : u ∈ X)
    (hx : ∀ t ≤ T, x t ∈ V)
    (hmin : ∀ t ≤ T, IsMinOn (objective psi loss t) V (x t))
    (hselected : ∀ t ≤ T, objective psi loss t (x t) ≠ ⊤)
    (hplayed : playedTop T loss x)
    (hcomparator : comparatorTop T loss u) :
    sourceLHS T loss x u = none ∧ sourceRHS T V psi loss x u = none := by
  exact ⟨sourceLHS_both_top T loss x u hbot hplayed hcomparator,
    sourceRHS_both_top T V psi loss x u hbot hselected hplayed hcomparator⟩

theorem lawful_source_identity
    (d T : ℕ) (X V : Set (EuclideanSpace ℝ (Fin d)))
    (hVX : V ⊆ X) (hVclosed : IsClosed V) (hV : V.Nonempty)
    (psi : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (loss : ℕ → EuclideanSpace ℝ (Fin d) → EReal)
    (hbot : ∀ i < T, ∀ v, loss i v ≠ ⊥)
    (x : ℕ → EuclideanSpace ℝ (Fin d))
    (u : EuclideanSpace ℝ (Fin d)) (hu : u ∈ X)
    (hx : ∀ t ≤ T, x t ∈ V)
    (hmin : ∀ t ≤ T, IsMinOn (objective psi loss t) V (x t))
    (hselected : ∀ t ≤ T, objective psi loss t (x t) ≠ ⊤)
    (hexclusive : ¬ (playedTop T loss x ∧ comparatorTop T loss u)) :
    sourceLHS T loss x u = sourceRHS T V psi loss x u ∧
      (sourceLHS T loss x u).isSome := by
  by_cases hp : playedTop T loss x
  · have hc : ¬ comparatorTop T loss u := fun hc => hexclusive ⟨hp, hc⟩
    obtain ⟨hl, hr⟩ := played_top_source_identity d T X V hVX hVclosed hV psi loss hbot x u hu hx hmin hselected hp hc
    rw [hl, hr]
    exact ⟨rfl, rfl⟩
  · by_cases hc : comparatorTop T loss u
    · obtain ⟨hl, hr⟩ := comparator_top_source_identity d T X V hVX hVclosed hV psi loss hbot x u hu hx hmin hselected hp hc
      rw [hl, hr]
      exact ⟨rfl, rfl⟩
    · exact finite_source_bridge d T X V hVX hVclosed hV psi loss hbot x u hu hx hmin hselected
        (by simpa [playedTop] using hp) (by simpa [comparatorTop] using hc)


private def sourceExtend {E : Type*} (X : Set E) (r : ℕ → X → ℝ) (t : ℕ) : E → ℝ :=
  Function.extend Subtype.val (r t) (fun _ => 0)

private theorem sourceExtend_restrict {E : Type*} (X : Set E) (r : ℕ → X → ℝ)
    (t : ℕ) (v : X) : sourceExtend X r t v = r t v := by
  exact Subtype.val_injective.extend_apply (r t) (fun _ => 0) v

private theorem objective_subtype_restrict {E : Type*} (X : Set E) (r : ℕ → X → ℝ)
    (loss : ℕ → E → EReal) (t : ℕ) (v : X) :
    objective (sourceExtend X r) loss t v = objective r (fun i (w : X) => loss i w) t v := by
  simp only [objective, sourceExtend_restrict]

private theorem initial_subtype_image {E : Type*} (X V : Set E) (hVX : V ⊆ X)
    (r : ℕ → X → ℝ) : sourceExtend X r 0 '' V = r 0 '' {v : X | (v : E) ∈ V} := by
  ext y
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨⟨v, hVX hv⟩, hv, ?_⟩
    exact (sourceExtend_restrict X r 0 ⟨v, hVX hv⟩).symm
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, hv, sourceExtend_restrict X r 0 v⟩

private theorem sourceRHS_subtype_restrict {E : Type*} (T : ℕ) (X V : Set E)
    (hVX : V ⊆ X) (r : ℕ → X → ℝ) (loss : ℕ → E → EReal)
    (xs : ℕ → X) (u : X) :
    sourceRHS T V (sourceExtend X r) loss (fun t => (xs t : E)) (u : E) =
      sourceRHS T {v : X | (v : E) ∈ V} r (fun i (w : X) => loss i w) xs u := by
  simp only [sourceRHS, objective_subtype_restrict, sourceExtend_restrict,
    initial_subtype_image X V hVX r]

private theorem source_subtype_backtransport
    (d T : ℕ) (X V : Set (EuclideanSpace ℝ (Fin d)))
    (hVX : V ⊆ X) (hVclosed : IsClosed V) (hV : V.Nonempty)
    (r : ℕ → X → ℝ) (loss : ℕ → EuclideanSpace ℝ (Fin d) → EReal)
    (hbot : ∀ i < T, ∀ v, loss i v ≠ ⊥)
    (xs : ℕ → X) (u : X)
    (hx : ∀ t ≤ T, (xs t : EuclideanSpace ℝ (Fin d)) ∈ V)
    (hmin : ∀ t ≤ T, IsMinOn (objective r (fun i (v : X) => loss i v) t)
      {v : X | (v : EuclideanSpace ℝ (Fin d)) ∈ V} (xs t))
    (hselected : ∀ t ≤ T, objective r (fun i (v : X) => loss i v) t (xs t) ≠ ⊤)
    (hexclusive : ¬ (playedTop T (fun i (v : X) => loss i v) xs ∧
      comparatorTop T (fun i (v : X) => loss i v) u)) :
    sourceLHS T (fun i (v : X) => loss i v) xs u =
      sourceRHS T {v : X | (v : EuclideanSpace ℝ (Fin d)) ∈ V}
        r (fun i (v : X) => loss i v) xs u ∧
      (sourceLHS T (fun i (v : X) => loss i v) xs u).isSome := by
  let psi := sourceExtend X r
  let x := fun t => (xs t : EuclideanSpace ℝ (Fin d))
  have hm : ∀ t ≤ T, IsMinOn (objective psi loss t) V (x t) := by
    intro t ht v hv
    have hh := hmin t ht (show (⟨v, hVX hv⟩ : X) ∈ {v : X | (v : EuclideanSpace ℝ (Fin d)) ∈ V} from hv)
    change objective psi loss t (xs t : EuclideanSpace ℝ (Fin d)) ≤ objective psi loss t v
    rw [show objective psi loss t (xs t : EuclideanSpace ℝ (Fin d)) =
      objective r (fun i (w : X) => loss i w) t (xs t) from objective_subtype_restrict X r loss t (xs t)]
    rw [show objective psi loss t v = objective r (fun i (w : X) => loss i w) t ⟨v, hVX hv⟩ from
      objective_subtype_restrict X r loss t ⟨v, hVX hv⟩]
    exact hh
  have hs : ∀ t ≤ T, objective psi loss t (x t) ≠ ⊤ := by
    intro t ht
    change objective (sourceExtend X r) loss t (xs t : EuclideanSpace ℝ (Fin d)) ≠ ⊤
    rw [objective_subtype_restrict]
    exact hselected t ht
  have h := lawful_source_identity d T X V hVX hVclosed hV psi loss hbot x (u : EuclideanSpace ℝ (Fin d))
    u.property hx hm hs hexclusive
  change sourceLHS T loss x (u : EuclideanSpace ℝ (Fin d)) = _ ∧ _
  rw [← sourceRHS_subtype_restrict T X V hVX r loss xs u]
  exact h


private theorem zero_horizon_source_value {E : Type*} (V : Set E)
    (psi : ℕ → E → ℝ) (loss : ℕ → E → EReal) (x : ℕ → E) (u : E)
    (hx : x 0 ∈ V) (hmin : IsMinOn (objective psi loss 0) V (x 0)) :
    sourceLHS 0 loss x u = some 0 ∧ sourceRHS 0 V psi loss x u = some 0 := by
  constructor
  · rfl
  · rw [sourceRHS_finite 0 V psi loss x u (by intro i hi; omega)
      (by
        intro i hi
        have hi0 : i = 0 := by omega
        subst i
        simp [objective])
      (by intro i hi; omega) (by intro i hi; omega)]
    rw [attained_initial_minimum V psi loss x hx hmin]
    simp only [sum_range_zero, objective, add_zero, EReal.toReal_coe]
    congr 2
    ring

end BanditRL.OnlineFTRLSourceArithmetic
