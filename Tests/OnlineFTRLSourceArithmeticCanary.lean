-- Concrete models for lawful and undefined source-arithmetic regimes.
import BanditRLProof.OnlineFTRLSourceArithmetic
noncomputable section
attribute [local instance] Classical.propDecidable
open Set Finset
namespace BanditRL.OnlineFTRLSourceArithmeticCanary
abbrev E := EuclideanSpace ℝ (Fin 1)
def v (s : ℝ) : E := EuclideanSpace.single (0 : Fin 1) s
def coord (w : E) : ℝ := w 0
structure Model where
  T : ℕ
  X : Set E
  V : Set E
  psi : ℕ → E → ℝ
  loss : ℕ → E → EReal
  x : ℕ → E
  u : E
-- These model records contain data only. Every source premise must be proved separately.
def finiteModel : Model :=
  ⟨1, {v 0, v 1, v 2}, {v 0, v 1},
    (fun t w => if t = 0 then (coord w)^2 else (coord w - 3)^2),
    (fun _ w => if w = v 3 then ⊤ else (coord w : EReal)),
    (fun t => if t = 0 then v 0 else v 1), v 2⟩
def playedModel : Model :=
  ⟨1, {v 0, v 1}, {v 0, v 1}, (fun _ _ => 0),
    (fun _ w => if w = v 0 then ⊤ else 0),
    (fun t => if t = 0 then v 0 else v 1), v 1⟩
def comparatorModel : Model :=
  { playedModel with x := fun _ => v 1, u := v 0 }
def sameIndexModel : Model := { playedModel with u := v 0 }
def differentIndexModel : Model :=
  ⟨2, {v 0, v 1, v 2}, {v 0, v 1}, (fun _ _ => 0),
    (fun t w => if (t = 0 ∧ w = v 0) ∨ (t = 1 ∧ w = v 2) then ⊤ else 0),
    (fun t => if t = 0 then v 0 else v 1), v 2⟩
def selectedTopModel : Model :=
  ⟨1, {v 0, v 1}, {v 0}, (fun _ _ => 0),
    (fun _ w => if w = v 0 then ⊤ else 0), (fun _ => v 0), v 1⟩
def zeroModel : Model :=
  ⟨0, {v 0, v 1, v 2}, {v 0, v 1}, (fun _ w => (coord w)^2),
    (fun _ _ => ⊤), (fun _ => v 0), v 2⟩

open BanditRL.OnlineFTRLSourceArithmetic

def lhs (m : Model) : Option EReal := sourceLHS m.T m.loss m.x m.u
def rhs (m : Model) : Option EReal := sourceRHS m.T m.V m.psi m.loss m.x m.u
def selectedFinite (m : Model) : Prop :=
  ∀ t ≤ m.T, objective m.psi m.loss t (m.x t) ≠ ⊤
def domainClaim (m : Model) : Prop :=
  (rhs m).isSome ↔ selectedFinite m ∧
    ¬ (playedTop m.T m.loss m.x ∧ comparatorTop m.T m.loss m.u)
def lawfulClaim (m : Model) : Prop := lhs m = rhs m ∧ (lhs m).isSome
def positiveClaim (m : Model) : Prop := lhs m = some ⊤ ∧ rhs m = some ⊤
def negativeClaim (m : Model) : Prop := lhs m = some ⊥ ∧ rhs m = some ⊥
def undefinedClaim (m : Model) : Prop := lhs m = none ∧ rhs m = none

@[simp] private theorem coord_v (s : ℝ) : coord (v s) = s := by simp [coord, v]
@[simp] private theorem v_eq_iff (s t : ℝ) : v s = v t ↔ s = t := by
  constructor
  · intro h; simpa using congrArg coord h
  · rintro rfl; rfl
private structure Ready (m : Model) : Prop where
  subset : m.V ⊆ m.X
  closed : IsClosed m.V
  nonempty : m.V.Nonempty
  nobot : ∀ i < m.T, ∀ w, m.loss i w ≠ ⊥
  comparator : m.u ∈ m.X
  feasible : ∀ t ≤ m.T, m.x t ∈ m.V
  minimal : ∀ t ≤ m.T, IsMinOn (objective m.psi m.loss t) m.V (m.x t)

private theorem finiteModel_ready : Ready finiteModel := by
  constructor
  · simp [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, selectedTopModel, zeroModel, Set.subset_def]
  · simp [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, selectedTopModel, zeroModel, isClosed_singleton]
  · simp [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, selectedTopModel, zeroModel]
  · intro i hi w
    simp only [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, selectedTopModel, zeroModel] at hi ⊢
    (try split_ifs) <;> simp
  · simp [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, selectedTopModel, zeroModel]
  · intro t ht
    simp only [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, selectedTopModel, zeroModel] at ht ⊢
    (try split_ifs) <;> simp
  · intro t ht
    simp only [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, selectedTopModel, zeroModel] at ht
    interval_cases t <;> intro w hw
    all_goals simp only [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, selectedTopModel, zeroModel, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    all_goals rcases hw with rfl | rfl
    all_goals norm_num [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, selectedTopModel, zeroModel, objective, Finset.sum_range_succ, coord_v, v_eq_iff, ← EReal.coe_add, ← EReal.coe_sub, ← EReal.coe_pow]
    all_goals norm_cast
    all_goals norm_num

private theorem playedModel_ready : Ready playedModel := by
  constructor
  · simp [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, selectedTopModel, zeroModel, Set.subset_def]
  · simp [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, selectedTopModel, zeroModel, isClosed_singleton]
  · simp [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, selectedTopModel, zeroModel]
  · intro i hi w
    simp only [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, selectedTopModel, zeroModel] at hi ⊢
    (try split_ifs) <;> simp
  · simp [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, selectedTopModel, zeroModel]
  · intro t ht
    simp only [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, selectedTopModel, zeroModel] at ht ⊢
    (try split_ifs) <;> simp
  · intro t ht
    simp only [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, selectedTopModel, zeroModel] at ht
    interval_cases t <;> intro w hw
    all_goals simp only [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, selectedTopModel, zeroModel, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    all_goals rcases hw with rfl | rfl
    all_goals norm_num [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, selectedTopModel, zeroModel, objective, Finset.sum_range_succ, coord_v, v_eq_iff, ← EReal.coe_add, ← EReal.coe_sub, ← EReal.coe_pow]
    all_goals norm_cast
    all_goals norm_num

private theorem comparatorModel_ready : Ready comparatorModel := by
  constructor
  · simp [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, selectedTopModel, zeroModel, Set.subset_def]
  · simp [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, selectedTopModel, zeroModel, isClosed_singleton]
  · simp [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, selectedTopModel, zeroModel]
  · intro i hi w
    simp only [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, selectedTopModel, zeroModel] at hi ⊢
    (try split_ifs) <;> simp
  · simp [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, selectedTopModel, zeroModel]
  · intro t ht
    simp only [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, selectedTopModel, zeroModel] at ht ⊢
    (try split_ifs) <;> simp
  · intro t ht
    simp only [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, selectedTopModel, zeroModel] at ht
    interval_cases t <;> intro w hw
    all_goals simp only [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, selectedTopModel, zeroModel, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    all_goals rcases hw with rfl | rfl
    all_goals norm_num [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, selectedTopModel, zeroModel, objective, Finset.sum_range_succ, coord_v, v_eq_iff, ← EReal.coe_add, ← EReal.coe_sub, ← EReal.coe_pow]
    all_goals norm_cast
    all_goals norm_num

private theorem sameIndexModel_ready : Ready sameIndexModel := by
  constructor
  · simp [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, selectedTopModel, zeroModel, Set.subset_def]
  · simp [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, selectedTopModel, zeroModel, isClosed_singleton]
  · simp [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, selectedTopModel, zeroModel]
  · intro i hi w
    simp only [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, selectedTopModel, zeroModel] at hi ⊢
    (try split_ifs) <;> simp
  · simp [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, selectedTopModel, zeroModel]
  · intro t ht
    simp only [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, selectedTopModel, zeroModel] at ht ⊢
    (try split_ifs) <;> simp
  · intro t ht
    simp only [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, selectedTopModel, zeroModel] at ht
    interval_cases t <;> intro w hw
    all_goals simp only [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, selectedTopModel, zeroModel, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    all_goals rcases hw with rfl | rfl
    all_goals norm_num [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, selectedTopModel, zeroModel, objective, Finset.sum_range_succ, coord_v, v_eq_iff, ← EReal.coe_add, ← EReal.coe_sub, ← EReal.coe_pow]
    all_goals norm_cast
    all_goals norm_num

private theorem differentIndexModel_ready : Ready differentIndexModel := by
  constructor
  · simp [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, selectedTopModel, zeroModel, Set.subset_def]
  · simp [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, selectedTopModel, zeroModel, isClosed_singleton]
  · simp [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, selectedTopModel, zeroModel]
  · intro i hi w
    simp only [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, selectedTopModel, zeroModel] at hi ⊢
    (try split_ifs) <;> simp
  · simp [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, selectedTopModel, zeroModel]
  · intro t ht
    simp only [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, selectedTopModel, zeroModel] at ht ⊢
    (try split_ifs) <;> simp
  · intro t ht
    simp only [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, selectedTopModel, zeroModel] at ht
    interval_cases t <;> intro w hw
    all_goals simp only [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, selectedTopModel, zeroModel, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    all_goals rcases hw with rfl | rfl
    all_goals norm_num [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, selectedTopModel, zeroModel, objective, Finset.sum_range_succ, coord_v, v_eq_iff, ← EReal.coe_add, ← EReal.coe_sub, ← EReal.coe_pow]
    all_goals norm_cast
    all_goals norm_num

private theorem selectedTopModel_ready : Ready selectedTopModel := by
  constructor
  · simp [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, selectedTopModel, zeroModel, Set.subset_def]
  · simp [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, selectedTopModel, zeroModel, isClosed_singleton]
  · simp [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, selectedTopModel, zeroModel]
  · intro i hi w
    simp only [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, selectedTopModel, zeroModel] at hi ⊢
    (try split_ifs) <;> simp
  · simp [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, selectedTopModel, zeroModel]
  · intro t ht
    simp only [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, selectedTopModel, zeroModel] at ht ⊢
    (try split_ifs) <;> simp
  · intro t ht
    simp only [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, selectedTopModel, zeroModel] at ht
    interval_cases t <;> intro w hw
    all_goals simp only [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, selectedTopModel, zeroModel, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    all_goals subst w
    all_goals norm_num [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, selectedTopModel, zeroModel, objective, Finset.sum_range_succ, coord_v, v_eq_iff, ← EReal.coe_add, ← EReal.coe_sub, ← EReal.coe_pow]
    all_goals norm_cast
    all_goals norm_num

private theorem zeroModel_ready : Ready zeroModel := by
  constructor
  · simp [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, selectedTopModel, zeroModel, Set.subset_def]
  · simp [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, selectedTopModel, zeroModel, isClosed_singleton]
  · simp [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, selectedTopModel, zeroModel]
  · intro i hi w
    simp only [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, selectedTopModel, zeroModel] at hi ⊢
    (try split_ifs) <;> simp
  · simp [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, selectedTopModel, zeroModel]
  · intro t ht
    simp only [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, selectedTopModel, zeroModel] at ht ⊢
    (try split_ifs) <;> simp
  · intro t ht
    simp only [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, selectedTopModel, zeroModel] at ht
    interval_cases t <;> intro w hw
    all_goals simp only [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, selectedTopModel, zeroModel, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    all_goals rcases hw with rfl | rfl
    all_goals norm_num [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, selectedTopModel, zeroModel, objective, Finset.sum_range_succ, coord_v, v_eq_iff, ← EReal.coe_add, ← EReal.coe_sub, ← EReal.coe_pow]
    all_goals norm_cast
    all_goals norm_num

private theorem finiteModel_finite : selectedFinite finiteModel := by
  intro t ht
  simp only [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, zeroModel, selectedTopModel] at ht
  interval_cases t <;> norm_num [selectedFinite, finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, zeroModel, selectedTopModel, objective, Finset.sum_range_succ, ← EReal.coe_add, ← EReal.coe_sub, ← EReal.coe_pow] <;> norm_cast
  exact EReal.natCast_ne_top 5

private theorem playedModel_finite : selectedFinite playedModel := by
  intro t ht
  simp only [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, zeroModel, selectedTopModel] at ht
  interval_cases t <;> norm_num [selectedFinite, finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, zeroModel, selectedTopModel, objective, Finset.sum_range_succ, ← EReal.coe_add, ← EReal.coe_sub, ← EReal.coe_pow] <;> norm_cast

private theorem comparatorModel_finite : selectedFinite comparatorModel := by
  intro t ht
  simp only [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, zeroModel, selectedTopModel] at ht
  interval_cases t <;> norm_num [selectedFinite, finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, zeroModel, selectedTopModel, objective, Finset.sum_range_succ, ← EReal.coe_add, ← EReal.coe_sub, ← EReal.coe_pow] <;> norm_cast

private theorem sameIndexModel_finite : selectedFinite sameIndexModel := by
  intro t ht
  simp only [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, zeroModel, selectedTopModel] at ht
  interval_cases t <;> norm_num [selectedFinite, finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, zeroModel, selectedTopModel, objective, Finset.sum_range_succ, ← EReal.coe_add, ← EReal.coe_sub, ← EReal.coe_pow] <;> norm_cast

private theorem differentIndexModel_finite : selectedFinite differentIndexModel := by
  intro t ht
  simp only [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, zeroModel, selectedTopModel] at ht
  interval_cases t <;> norm_num [selectedFinite, finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, zeroModel, selectedTopModel, objective, Finset.sum_range_succ, ← EReal.coe_add, ← EReal.coe_sub, ← EReal.coe_pow] <;> norm_cast

private theorem zeroModel_finite : selectedFinite zeroModel := by
  intro t ht
  simp only [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, zeroModel, selectedTopModel] at ht
  interval_cases t <;> norm_num [selectedFinite, finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, zeroModel, selectedTopModel, objective, Finset.sum_range_succ, ← EReal.coe_add, ← EReal.coe_sub, ← EReal.coe_pow] <;> norm_cast

private theorem finiteModel_P : ¬ playedTop finiteModel.T finiteModel.loss finiteModel.x := by
  rintro ⟨i, hi, h⟩
  simp only [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, zeroModel, selectedTopModel] at hi
  interval_cases i <;> norm_num [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, zeroModel, selectedTopModel] at h

private theorem finiteModel_C : ¬ comparatorTop finiteModel.T finiteModel.loss finiteModel.u := by
  rintro ⟨i, hi, h⟩
  simp only [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, zeroModel, selectedTopModel] at hi
  interval_cases i <;> norm_num [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, zeroModel, selectedTopModel] at h

private theorem playedModel_P : playedTop playedModel.T playedModel.loss playedModel.x := by
  refine ⟨0, by norm_num [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, zeroModel, selectedTopModel], ?_⟩
  norm_num [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, zeroModel, selectedTopModel]

private theorem playedModel_C : ¬ comparatorTop playedModel.T playedModel.loss playedModel.u := by
  rintro ⟨i, hi, h⟩
  simp only [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, zeroModel, selectedTopModel] at hi
  interval_cases i <;> norm_num [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, zeroModel, selectedTopModel] at h

private theorem comparatorModel_P : ¬ playedTop comparatorModel.T comparatorModel.loss comparatorModel.x := by
  rintro ⟨i, hi, h⟩
  simp only [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, zeroModel, selectedTopModel] at hi
  interval_cases i <;> norm_num [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, zeroModel, selectedTopModel] at h

private theorem comparatorModel_C : comparatorTop comparatorModel.T comparatorModel.loss comparatorModel.u := by
  refine ⟨0, by norm_num [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, zeroModel, selectedTopModel], ?_⟩
  norm_num [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, zeroModel, selectedTopModel]

private theorem sameIndexModel_P : playedTop sameIndexModel.T sameIndexModel.loss sameIndexModel.x := by
  refine ⟨0, by norm_num [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, zeroModel, selectedTopModel], ?_⟩
  norm_num [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, zeroModel, selectedTopModel]

private theorem sameIndexModel_C : comparatorTop sameIndexModel.T sameIndexModel.loss sameIndexModel.u := by
  refine ⟨0, by norm_num [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, zeroModel, selectedTopModel], ?_⟩
  norm_num [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, zeroModel, selectedTopModel]

private theorem differentIndexModel_P : playedTop differentIndexModel.T differentIndexModel.loss differentIndexModel.x := by
  refine ⟨0, by norm_num [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, zeroModel, selectedTopModel], ?_⟩
  norm_num [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, zeroModel, selectedTopModel]

private theorem differentIndexModel_C : comparatorTop differentIndexModel.T differentIndexModel.loss differentIndexModel.u := by
  refine ⟨1, by norm_num [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, zeroModel, selectedTopModel], ?_⟩
  norm_num [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, zeroModel, selectedTopModel]

private theorem zeroModel_P : ¬ playedTop zeroModel.T zeroModel.loss zeroModel.x := by
  rintro ⟨i, hi, h⟩
  simp only [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, zeroModel, selectedTopModel] at hi
  interval_cases i <;> norm_num [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, zeroModel, selectedTopModel] at h

private theorem zeroModel_C : ¬ comparatorTop zeroModel.T zeroModel.loss zeroModel.u := by
  rintro ⟨i, hi, h⟩
  simp only [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, zeroModel, selectedTopModel] at hi
  interval_cases i <;> norm_num [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, zeroModel, selectedTopModel] at h

theorem finite_source_model :
    domainClaim finiteModel ∧ lawfulClaim finiteModel ∧
    lhs finiteModel = some (-2 : EReal) ∧ rhs finiteModel = some (-2 : EReal) ∧
    finiteModel.u ∈ finiteModel.X ∧ finiteModel.u ∉ finiteModel.V ∧
    IsClosed finiteModel.V ∧ ¬ Convex ℝ finiteModel.V ∧
    finiteModel.loss 0 (v 3) = ⊤ := by
  let h := finiteModel_ready
  have hlaw : lawfulClaim finiteModel := lawful_source_identity 1 finiteModel.T finiteModel.X finiteModel.V h.subset h.closed h.nonempty finiteModel.psi finiteModel.loss h.nobot finiteModel.x finiteModel.u h.comparator h.feasible h.minimal finiteModel_finite (by rintro ⟨hp, hc⟩; exact finiteModel_P hp)
  have hn : lhs finiteModel = some (-2 : EReal) := by norm_num [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, selectedTopModel, zeroModel, lhs, sourceLHS, sourceSum, sourceSub, sourceAdd, ← EReal.coe_sub, ← EReal.coe_add] <;> norm_cast
  refine ⟨source_arithmetic_domain 1 finiteModel.T finiteModel.X finiteModel.V h.subset h.closed h.nonempty finiteModel.psi finiteModel.loss h.nobot finiteModel.x finiteModel.u h.comparator h.feasible h.minimal, hlaw, hn, ?_, h.comparator, ?_, h.closed, ?_, ?_⟩
  · rw [← hlaw.1]; exact hn
  · norm_num [finiteModel]
  · intro hc
    have hh := hc (by simp [finiteModel] : v 0 ∈ finiteModel.V) (by simp [finiteModel] : v 1 ∈ finiteModel.V)
      (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ)+1/2=1)
    simp only [finiteModel, Set.mem_insert_iff, Set.mem_singleton_iff] at hh
    rcases hh with hh | hh
    all_goals have he := congrArg (fun w : E => w 0) hh
    all_goals norm_num [v] at he
  · simp [finiteModel]

theorem lawful_played_top :
    domainClaim playedModel ∧ positiveClaim playedModel ∧ lawfulClaim playedModel ∧
    selectedFinite playedModel ∧ playedTop playedModel.T playedModel.loss playedModel.x ∧
    ¬ comparatorTop playedModel.T playedModel.loss playedModel.u := by
  let h := playedModel_ready
  have hlaw : lawfulClaim playedModel := lawful_source_identity 1 playedModel.T playedModel.X playedModel.V h.subset h.closed h.nonempty playedModel.psi playedModel.loss h.nobot playedModel.x playedModel.u h.comparator h.feasible h.minimal playedModel_finite (by rintro ⟨hp, hc⟩; exact playedModel_C hc)
  refine ⟨source_arithmetic_domain 1 playedModel.T playedModel.X playedModel.V h.subset h.closed h.nonempty playedModel.psi playedModel.loss h.nobot playedModel.x playedModel.u h.comparator h.feasible h.minimal, played_top_source_identity 1 playedModel.T playedModel.X playedModel.V h.subset h.closed h.nonempty playedModel.psi playedModel.loss h.nobot playedModel.x playedModel.u h.comparator h.feasible h.minimal playedModel_finite playedModel_P playedModel_C, hlaw, playedModel_finite, playedModel_P, playedModel_C⟩

theorem lawful_comparator_top :
    domainClaim comparatorModel ∧ negativeClaim comparatorModel ∧ lawfulClaim comparatorModel ∧
    selectedFinite comparatorModel ∧ ¬ playedTop comparatorModel.T comparatorModel.loss comparatorModel.x ∧
    comparatorTop comparatorModel.T comparatorModel.loss comparatorModel.u := by
  let h := comparatorModel_ready
  have hlaw : lawfulClaim comparatorModel := lawful_source_identity 1 comparatorModel.T comparatorModel.X comparatorModel.V h.subset h.closed h.nonempty comparatorModel.psi comparatorModel.loss h.nobot comparatorModel.x comparatorModel.u h.comparator h.feasible h.minimal comparatorModel_finite (by rintro ⟨hp, hc⟩; exact comparatorModel_P hp)
  refine ⟨source_arithmetic_domain 1 comparatorModel.T comparatorModel.X comparatorModel.V h.subset h.closed h.nonempty comparatorModel.psi comparatorModel.loss h.nobot comparatorModel.x comparatorModel.u h.comparator h.feasible h.minimal, comparator_top_source_identity 1 comparatorModel.T comparatorModel.X comparatorModel.V h.subset h.closed h.nonempty comparatorModel.psi comparatorModel.loss h.nobot comparatorModel.x comparatorModel.u h.comparator h.feasible h.minimal comparatorModel_finite comparatorModel_P comparatorModel_C, hlaw, comparatorModel_finite, comparatorModel_P, comparatorModel_C⟩

theorem same_index_undefined :
    domainClaim sameIndexModel ∧ undefinedClaim sameIndexModel ∧
    selectedFinite sameIndexModel ∧
    sameIndexModel.loss 0 (sameIndexModel.x 0) = ⊤ ∧
    sameIndexModel.loss 0 sameIndexModel.u = ⊤ := by
  let h := sameIndexModel_ready
  refine ⟨source_arithmetic_domain 1 sameIndexModel.T sameIndexModel.X sameIndexModel.V h.subset h.closed h.nonempty sameIndexModel.psi sameIndexModel.loss h.nobot sameIndexModel.x sameIndexModel.u h.comparator h.feasible h.minimal, both_top_source_undefined 1 sameIndexModel.T sameIndexModel.X sameIndexModel.V h.subset h.closed h.nonempty sameIndexModel.psi sameIndexModel.loss h.nobot sameIndexModel.x sameIndexModel.u h.comparator h.feasible h.minimal sameIndexModel_finite sameIndexModel_P sameIndexModel_C, sameIndexModel_finite, ?_⟩
  norm_num [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, selectedTopModel, zeroModel, sourceSub, sourceAdd]

theorem different_index_undefined :
    domainClaim differentIndexModel ∧ undefinedClaim differentIndexModel ∧
    selectedFinite differentIndexModel ∧
    sourceSub (differentIndexModel.loss 0 (differentIndexModel.x 0))
      (differentIndexModel.loss 0 differentIndexModel.u) = some ⊤ ∧
    sourceSub (differentIndexModel.loss 1 (differentIndexModel.x 1))
      (differentIndexModel.loss 1 differentIndexModel.u) = some ⊥ := by
  let h := differentIndexModel_ready
  refine ⟨source_arithmetic_domain 1 differentIndexModel.T differentIndexModel.X differentIndexModel.V h.subset h.closed h.nonempty differentIndexModel.psi differentIndexModel.loss h.nobot differentIndexModel.x differentIndexModel.u h.comparator h.feasible h.minimal, both_top_source_undefined 1 differentIndexModel.T differentIndexModel.X differentIndexModel.V h.subset h.closed h.nonempty differentIndexModel.psi differentIndexModel.loss h.nobot differentIndexModel.x differentIndexModel.u h.comparator h.feasible h.minimal differentIndexModel_finite differentIndexModel_P differentIndexModel_C, differentIndexModel_finite, ?_⟩
  norm_num [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, selectedTopModel, zeroModel, sourceSub, sourceAdd]

theorem selected_top_only_rhs_undefined :
    domainClaim selectedTopModel ∧
    lhs selectedTopModel = some ⊤ ∧ rhs selectedTopModel = none ∧
    objective selectedTopModel.psi selectedTopModel.loss 1 (selectedTopModel.x 1) = ⊤ ∧
    selectedTopModel.u ∈ selectedTopModel.X ∧ selectedTopModel.u ∉ selectedTopModel.V := by
  let h := selectedTopModel_ready
  have hd : domainClaim selectedTopModel := source_arithmetic_domain 1 selectedTopModel.T selectedTopModel.X selectedTopModel.V h.subset h.closed h.nonempty selectedTopModel.psi selectedTopModel.loss h.nobot selectedTopModel.x selectedTopModel.u h.comparator h.feasible h.minimal
  have hn : rhs selectedTopModel = none := by
    have hn : ¬ (rhs selectedTopModel).isSome := by
      intro hh
      have hf := (hd.mp hh).1 1 (by norm_num [selectedTopModel])
      simpa [selectedTopModel, objective] using hf
    cases he : rhs selectedTopModel with
    | none => rfl
    | some z => simp [he] at hn
  refine ⟨hd, ?_, hn, ?_, ?_, ?_⟩
  all_goals norm_num [finiteModel, playedModel, comparatorModel, sameIndexModel, differentIndexModel, selectedTopModel, zeroModel, lhs, sourceLHS, sourceSum, sourceSub, sourceAdd, ← EReal.coe_sub, ← EReal.coe_add, objective]

theorem zero_horizon_lawful :
    domainClaim zeroModel ∧ lawfulClaim zeroModel ∧
    lhs zeroModel = some 0 ∧ rhs zeroModel = some 0 ∧ selectedFinite zeroModel ∧
    zeroModel.loss 0 (v 0) = ⊤ ∧
    ¬ playedTop zeroModel.T zeroModel.loss zeroModel.x ∧
    ¬ comparatorTop zeroModel.T zeroModel.loss zeroModel.u := by
  let h := zeroModel_ready
  have hlaw : lawfulClaim zeroModel := lawful_source_identity 1 zeroModel.T zeroModel.X zeroModel.V h.subset h.closed h.nonempty zeroModel.psi zeroModel.loss h.nobot zeroModel.x zeroModel.u h.comparator h.feasible h.minimal zeroModel_finite (by rintro ⟨hp, hc⟩; exact zeroModel_P hp)
  have hz : lhs zeroModel = some 0 := rfl
  refine ⟨source_arithmetic_domain 1 zeroModel.T zeroModel.X zeroModel.V h.subset h.closed h.nonempty zeroModel.psi zeroModel.loss h.nobot zeroModel.x zeroModel.u h.comparator h.feasible h.minimal, hlaw, hz, ?_, zeroModel_finite, ?_, zeroModel_P, zeroModel_C⟩
  · rw [← hlaw.1]; exact hz
  · rfl

end BanditRL.OnlineFTRLSourceArithmeticCanary
