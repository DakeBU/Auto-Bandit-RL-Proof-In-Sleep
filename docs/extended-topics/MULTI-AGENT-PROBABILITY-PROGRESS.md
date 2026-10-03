# Static MC probability producer: second prototype

2026-09-20. This advances the compiled coordination component from the previous
4b05e79 checkpoint. It does not promote either scratch to the public root and
does not claim full MC, source Theorem 1, or topic acceptance. The source remains
Rosenski--Shamir--Szlak, ICML 2016, main Algorithm 2 and supplement A.1 Lemma 4;
use MULTI-AGENT-CONTRACT.md for the exact unknown-N full-learning target and
explicit source repairs. The previous prototype and its review-bound files
are retained unchanged. The second file retains its definitions/proofs in a
separate scratch namespace so the old evidence is reproducible; only one
canonical implementation should be promoted into production.

## Actual new mathematical edge

Let C_i be any nonempty finite candidate set. Sample a uniform element of the
finite Cartesian product of the C_i and project to arm labels. For arbitrary
finite restrictions B_i, including empty restrictions, the constructed law
satisfies the exact rectangle formula

    Pr(for every i, draw_i in B_i)
      = product_i |C_i intersect B_i| / product_i |C_i|
      = product_i (|C_i intersect B_i| / |C_i|).

The proof constructs an equivalence between the restricted product event and
the product of the intersections, uses uniform-event counting, then finite
product cardinalities. Factorization is proved for events, without assuming
marginal independence. No `iIndepFun` wrapper is claimed. The ENNReal division
factorization discharges the finite-denominator side conditions explicitly.
All spaces here are finite; the outer-measure event formulas are genuine
probabilities of their finite PMFs and need no omitted measurability premise.

The same actual transition preserves membership of each fixed arm in that
player's own candidates. Its one-step update is proved equal to a local
function of the old local state, played arm and observed collision bit. The
collision bit is produced from the joint action vector. This improves the
previous action-coordinate locality theorem to a one-step feedback adapter;
it does not yet construct the full exploration history or prove full-policy
information measurability.

For a still-unfixed player i and an arm a unoccupied by fixed players, restrict
i's draw to a and every other unfixed player's draw to avoid a. Fixed players'
unused draw coordinates may be unrestricted. This rectangular event implies
that the actual next state fixes i to a. The exact counting probability is
therefore a lower bound for that event under the actual transition PMF. This
works for different candidate sets too; the bound may then be zero.

When all candidate sets equal a common S of cardinality n (the number of
players), a simpler rectangle restricts every other private draw to avoid a,
even if it will be ignored by an already fixed player. Its exact probability is

    h_n = (1/n) ((n-1)/n)^(n-1).

The unused-draw restrictions only make this event smaller. They do not change
the policy. Existence of such an unused a in S is proved: the given unfixed
player leaves at most n-1 fixed coordinates, so the image of their labels has
cardinality less than |S|. A cardinality contradiction constructs a label in
S outside that image. This proof needs neither a supplied unused-arm witness
nor successful settlement. Combining it with the rectangle producer gives

    Pr(next_state_i is fixed | current state s) >= h_n,
    whenever s_i is unfixed and |S|=n.

This is the statewise transition-kernel statement: a full-history conditional
probability identity still needs the path-law/filtration adapter. Common S and
its cardinality are explicit premises of the coordination component. The
full learner must produce them from its own exploration-good event. The
hazard theorem does not receive a hazard, concentration or successful-fixation
premise. A coordinate i:Fin n excludes n=0; n=1 is valid and the formula gives
one via the natural exponent-zero convention.

## Concrete checks and exact remaining boundary

The instance uses n=2, k=3 and S={0,1}. From the actual all-unfixed initial
state, the theorem produces fixation probability at least 1/4 for player 0.
A second theorem gives exactly 1/4 for the specific event draw_0=0, draw_1=1.
This is not a claim that total fixation probability equals 1/4: the symmetric
successful event is additional. It is not the mandatory full-learner canary
with stochastic rewards and estimated candidate sets.

The file contains 25 proved propositions, retaining the earlier 10 and adding
15. Axiom audit covers every proposition; only standard Lean axioms are
allowed. Compiler and independent-review hashes are recorded in
`runs/extended-topics-20260920/multi-agent-probability-review.json` after the
reviews finish. Exact code is folded below, with no theorem omitted.

Still absent: the numerical uniform estimate h_n>=1/(4n), repeated conditional
survival/finite waiting-time sums, the 2U regret charge, actual arbitrary-bounded
reward exploration, count/estimator/ranking concentration, learned candidates,
full regret endpoints, full-learner canary, recent-source proof comparison,
public-root/registry/reader integration and controlled all-topic evaluation.
The supplied common-set premise is allowed only at this intermediate boundary;
it cannot be an assumption of the final full MC theorem.

Reuse is the same actual PMF constructor plus uniform event counting,
`Fintype.card_congr`, `Fintype.card_pi`, finite product factorization and
map-event transport. The first prototype's deterministic transition and
invariant proofs are retained, not counted as newly discovered mathematics.
No production declaration graph, website milestone or measured efficiency
claim is created by this scratch checkpoint. The semantic audit accepts only
this explicit component boundary if the independent comparison passes.

<details>
<summary>Exact probability prototype: definitions and proofs</summary>

```lean
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Tactic

/-! Second scratch coordination producer, retaining the first prototype as an
immutable reviewed checkpoint. Exact rectangle probabilities, local collision
feedback, candidate preservation and a statewise fixation hazard are proved.
No unknown-N estimator, reward process, exploration concentration, waiting-time
sum or complete regret theorem is claimed. Local candidate correctness remains
to be produced by the exploration phase. Not imported by the public root. -/
namespace MusicalChairsProbabilityPrototype
open scoped Classical ENNReal
set_option autoImplicit false

abbrev State (n k : ℕ) := Fin n → Option (Fin k)

def action {n k : ℕ} (s : State n k) (draw : Fin n → Fin k) (i : Fin n) : Fin k :=
  (s i).getD (draw i)

def CollisionFree {n k : ℕ} (a : Fin n → Fin k) (i : Fin n) : Prop :=
  ∀ j, j ≠ i → a j ≠ a i

noncomputable def step {n k : ℕ} (s : State n k) (draw : Fin n → Fin k) : State n k :=
  fun i => match s i with
  | some a => some a
  | none => if CollisionFree (action s draw) i then some (action s draw i) else none

def DistinctFixed {n k : ℕ} (s : State n k) : Prop :=
  ∀ i j a, s i = some a → s j = some a → i = j

theorem action_of_fixed {n k : ℕ} (s : State n k) (draw : Fin n → Fin k)
    (i : Fin n) (a : Fin k) (h : s i = some a) : action s draw i = a := by
  simp [action, h]

theorem step_preserves_fixed {n k : ℕ} (s : State n k) (draw : Fin n → Fin k)
    (i : Fin n) (a : Fin k) (h : s i = some a) : step s draw i = some a := by
  simp [step, h]

theorem step_fixed_action {n k : ℕ} (s : State n k) (draw : Fin n → Fin k)
    (i : Fin n) (a : Fin k) (h : step s draw i = some a) : action s draw i = a := by
  cases hs : s i with
  | none =>
    by_cases hc : CollisionFree (action s draw) i
    · simpa [step, hs, hc] using h
    · simp [step, hs, hc] at h
  | some b =>
    have hab : b = a := by simpa [step, hs] using h
    simp [action, hs, hab]

theorem new_fixed_collisionFree {n k : ℕ} (s : State n k) (draw : Fin n → Fin k)
    (i : Fin n) (a : Fin k) (hn : s i = none) (h : step s draw i = some a) :
    CollisionFree (action s draw) i := by
  by_contra hc
  simp [step, hn, hc] at h

theorem step_distinct {n k : ℕ} (s : State n k) (draw : Fin n → Fin k)
    (hs : DistinctFixed s) : DistinctFixed (step s draw) := by
  intro i j a hi hj
  by_contra hij
  have hai := step_fixed_action s draw i a hi
  have haj := step_fixed_action s draw j a hj
  cases hsi : s i with
  | none =>
    exact (new_fixed_collisionFree s draw i a hsi hi) j (Ne.symm hij) (haj.trans hai.symm)
  | some b =>
    have hbi : b = a := by simpa [step, hsi] using hi
    cases hsj : s j with
    | none =>
      exact (new_fixed_collisionFree s draw j a hsj hj) i hij (hai.trans haj.symm)
    | some c =>
      have hcj : c = a := by simpa [step, hsj] using hj
      exact hij (hs i j a (hsi.trans (congrArg some hbi)) (hsj.trans (congrArg some hcj)))

def initial (n k : ℕ) : State n k := fun _ => none

theorem initial_distinct (n k : ℕ) : DistinctFixed (initial n k) := by
  intro i j a hi
  simp [initial] at hi

noncomputable def trajectory {n k : ℕ} (draws : ℕ → Fin n → Fin k) : ℕ → State n k
  | 0 => initial n k
  | t+1 => step (trajectory draws t) (draws t)

theorem trajectory_distinct {n k : ℕ} (draws : ℕ → Fin n → Fin k) (t : ℕ) :
    DistinctFixed (trajectory draws t) := by
  induction t with
  | zero => exact initial_distinct n k
  | succ t ih => exact step_distinct _ _ ih

/-- The action of player i uses only its own fixed arm and its own private draw. -/
theorem action_local {n k : ℕ} (s s' : State n k) (draw draw' : Fin n → Fin k)
    (i : Fin n) (hs : s i = s' i) (hd : draw i = draw' i) :
    action s draw i = action s' draw' i := by
  simp only [action, hs, hd]

/-- Uniform law on the finite Cartesian product of local candidate sets. -/
noncomputable def jointDraw {n k : ℕ} (candidates : Fin n → Finset (Fin k))
    (hne : ∀ i, (candidates i).Nonempty) : PMF (Fin n → Fin k) := by
  letI : ∀ i, Nonempty {a : Fin k // a ∈ candidates i} := fun i =>
    ⟨⟨(hne i).choose, (hne i).choose_spec⟩⟩
  exact (PMF.uniformOfFintype ((i : Fin n) → {a : Fin k // a ∈ candidates i})).map
    (fun draws i => (draws i).val)

noncomputable def transition {n k : ℕ} (candidates : Fin n → Finset (Fin k))
    (hne : ∀ i, (candidates i).Nonempty) (s : State n k) : PMF (State n k) :=
  (jointDraw candidates hne).map (step s)

noncomputable def stateLaw {n k : ℕ} (candidates : Fin n → Finset (Fin k))
    (hne : ∀ i, (candidates i).Nonempty) : ℕ → PMF (State n k)
  | 0 => PMF.pure (initial n k)
  | t+1 => (stateLaw candidates hne t).bind (transition candidates hne)

theorem transition_distinct {n k : ℕ} (candidates : Fin n → Finset (Fin k))
    (hne : ∀ i, (candidates i).Nonempty) (s s' : State n k)
    (hs : DistinctFixed s) (h : s' ∈ (transition candidates hne s).support) :
    DistinctFixed s' := by
  obtain ⟨draw, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp h
  exact step_distinct s draw hs

theorem stateLaw_distinct {n k : ℕ} (candidates : Fin n → Finset (Fin k))
    (hne : ∀ i, (candidates i).Nonempty) (t : ℕ) (s : State n k)
    (h : s ∈ (stateLaw candidates hne t).support) : DistinctFixed s := by
  induction t generalizing s with
  | zero =>
    have heq : s = initial n k := by simpa [stateLaw] using h
    subst s
    exact initial_distinct n k
  | succ t ih =>
    change s ∈ ((stateLaw candidates hne t).bind (transition candidates hne)).support at h
    obtain ⟨prev, hp, ht⟩ := (PMF.mem_support_bind_iff _ _ _).mp h
    exact transition_distinct candidates hne prev s (ih prev hp) ht

/-- A player's update consumes only its own old state, action, and collision bit. -/
def localUpdate {k : ℕ} (old : Option (Fin k)) (played : Fin k)
    (collided : Bool) : Option (Fin k) :=
  match old with
  | some a => some a
  | none => if collided then none else some played

noncomputable def collisionBit {n k : ℕ} (a : Fin n → Fin k) (i : Fin n) : Bool :=
  decide (¬ CollisionFree a i)

theorem step_localUpdate {n k : ℕ} (s : State n k) (draw : Fin n → Fin k)
    (i : Fin n) : step s draw i =
      localUpdate (s i) (action s draw i) (collisionBit (action s draw) i) := by
  cases hs : s i with
  | some a => simp [step, localUpdate, hs]
  | none =>
    by_cases hc : CollisionFree (action s draw) i
    · simp [step, localUpdate, collisionBit, hs, hc]
    · simp [step, localUpdate, collisionBit, hs, hc]

theorem jointDraw_mem {n k : ℕ} (candidates : Fin n → Finset (Fin k))
    (hne : ∀ i, (candidates i).Nonempty) (draw : Fin n → Fin k)
    (h : draw ∈ (jointDraw candidates hne).support) (i : Fin n) :
    draw i ∈ candidates i := by
  unfold jointDraw at h
  obtain ⟨v, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp h
  exact (v i).property

def FixedWithin {n k : ℕ} (candidates : Fin n → Finset (Fin k)) (s : State n k) : Prop :=
  ∀ i a, s i = some a → a ∈ candidates i

theorem step_within {n k : ℕ} (candidates : Fin n → Finset (Fin k))
    (s : State n k) (draw : Fin n → Fin k) (hs : FixedWithin candidates s)
    (hd : ∀ i, draw i ∈ candidates i) : FixedWithin candidates (step s draw) := by
  intro i a h
  cases hi : s i with
  | none =>
    have ha := step_fixed_action s draw i a h
    have heq : draw i = a := by simpa [action, hi] using ha
    exact heq ▸ hd i
  | some b =>
    have heq : b = a := by simpa [step, hi] using h
    exact heq ▸ hs i b hi

theorem stateLaw_within {n k : ℕ} (candidates : Fin n → Finset (Fin k))
    (hne : ∀ i, (candidates i).Nonempty) (t : ℕ) (s : State n k)
    (h : s ∈ (stateLaw candidates hne t).support) : FixedWithin candidates s := by
  induction t generalizing s with
  | zero =>
    have heq : s = initial n k := by simpa [stateLaw] using h
    subst s
    intro i a hi
    simp [initial] at hi
  | succ t ih =>
    change s ∈ ((stateLaw candidates hne t).bind (transition candidates hne)).support at h
    obtain ⟨prev, hp, ht⟩ := (PMF.mem_support_bind_iff _ _ _).mp h
    obtain ⟨draw, hd, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp ht
    exact step_within candidates prev draw (ih prev hp) (jointDraw_mem candidates hne draw hd)

/-- Exact rectangular-event law, including empty restrictions. -/
theorem jointDraw_rectangle {n k : ℕ} (candidates allowed : Fin n → Finset (Fin k))
    (hne : ∀ i, (candidates i).Nonempty) :
    (jointDraw candidates hne).toOuterMeasure {draw | ∀ i, draw i ∈ allowed i} =
      (∏ i, ((candidates i ∩ allowed i).card : ℝ≥0∞)) /
        (∏ i, ((candidates i).card : ℝ≥0∞)) := by
  let D := (i : Fin n) → {a : Fin k // a ∈ candidates i}
  letI : ∀ i, Nonempty {a : Fin k // a ∈ candidates i} := fun i =>
    ⟨⟨(hne i).choose, (hne i).choose_spec⟩⟩
  let E : Set D := {v | ∀ i, (v i).val ∈ allowed i}
  let e : E ≃ ((i : Fin n) → {a : Fin k // a ∈ candidates i ∩ allowed i}) :=
    { toFun := fun v i => ⟨(v.val i).val, Finset.mem_inter.mpr ⟨(v.val i).property, v.property i⟩⟩
      invFun := fun v => ⟨fun i => ⟨(v i).val, (Finset.mem_inter.mp (v i).property).1⟩,
        fun i => (Finset.mem_inter.mp (v i).property).2⟩
      left_inv := fun v => by ext i; rfl
      right_inv := fun v => by ext i; rfl }
  change ((PMF.uniformOfFintype D).map (fun v i => (v i).val)).toOuterMeasure _ = _
  rw [PMF.toOuterMeasure_map_apply]
  change (PMF.uniformOfFintype D).toOuterMeasure E = _
  rw [PMF.toOuterMeasure_uniformOfFintype_apply, Fintype.card_congr e]
  simp only [D, Fintype.card_pi, Fintype.card_coe, Nat.cast_prod]

/-- Rectangle probabilities factor into their coordinate counting ratios. -/
theorem jointDraw_rectangle_product {n k : ℕ} (candidates allowed : Fin n → Finset (Fin k))
    (hne : ∀ i, (candidates i).Nonempty) :
    (jointDraw candidates hne).toOuterMeasure {draw | ∀ i, draw i ∈ allowed i} =
      ∏ i, ((candidates i ∩ allowed i).card : ℝ≥0∞) / ((candidates i).card : ℝ≥0∞) := by
  rw [jointDraw_rectangle]
  symm
  apply ENNReal.prod_div_distrib_of_ne_top
  intros
  simp

noncomputable def fixationWindow {n k : ℕ} (s : State n k) (i : Fin n) (a : Fin k)
    (j : Fin n) : Finset (Fin k) :=
  if j = i then {a} else if s j = none then Finset.univ.erase a else Finset.univ

theorem fixationWindow_fixes {n k : ℕ} (s : State n k) (draw : Fin n → Fin k)
    (i : Fin n) (a : Fin k) (hi : s i = none)
    (ha : ∀ j b, s j = some b → b ≠ a)
    (hd : ∀ j, draw j ∈ fixationWindow s i a j) : step s draw i = some a := by
  have hdi : draw i = a := by simpa [fixationWindow] using hd i
  have hai : action s draw i = a := by simp [action, hi, hdi]
  have hc : CollisionFree (action s draw) i := by
    intro j hj
    rw [hai]
    cases hs : s j with
    | none =>
      have hdj : draw j ≠ a := by simpa [fixationWindow, hj, hs] using hd j
      simpa [action, hs] using hdj
    | some b => simpa [action, hs] using ha j b hs
  simp [step, hi, hc, hai]

/-- A genuine lower bound on the constructed next-state law, obtained from
one explicit collision-free draw event. Candidate sets may differ. -/
theorem transition_fixation_lower {n k : ℕ} (candidates : Fin n → Finset (Fin k))
    (hne : ∀ j, (candidates j).Nonempty) (s : State n k) (i : Fin n) (a : Fin k)
    (hi : s i = none) (ha : ∀ j b, s j = some b → b ≠ a) :
    (∏ j, ((candidates j ∩ fixationWindow s i a j).card : ℝ≥0∞) /
      ((candidates j).card : ℝ≥0∞)) ≤
      (transition candidates hne s).toOuterMeasure {s' | s' i = some a} := by
  rw [← jointDraw_rectangle_product candidates (fixationWindow s i a) hne]
  unfold transition
  rw [PMF.toOuterMeasure_map_apply]
  apply MeasureTheory.measure_mono
  intro draw hd
  exact fixationWindow_fixes s draw i a hi ha hd

noncomputable def isolationWindow {n k : ℕ} (i : Fin n) (a : Fin k) (j : Fin n) : Finset (Fin k) :=
  if j = i then {a} else Finset.univ.erase a

theorem isolationWindow_subset {n k : ℕ} (s : State n k) (i : Fin n) (a : Fin k)
    (j : Fin n) : isolationWindow i a j ⊆ fixationWindow s i a j := by
  by_cases h : j = i
  · simp [isolationWindow, fixationWindow, h]
  · by_cases hs : s j = none <;> simp [isolationWindow, fixationWindow, h, hs]

/-- Exact probability of a tagged draw and avoidance by every other private coin. -/
theorem jointDraw_isolation {n k : ℕ} (S : Finset (Fin k)) (i : Fin n) (a : Fin k)
    (ha : a ∈ S) (hcard : S.card = n) :
    (jointDraw (fun _ : Fin n => S) (fun _ => ⟨a, ha⟩)).toOuterMeasure
      {draw | ∀ j, draw j ∈ isolationWindow i a j} =
      (1 / (n : ℝ≥0∞)) * (((n-1 : ℕ) : ℝ≥0∞) / (n : ℝ≥0∞))^(n-1) := by
  rw [jointDraw_rectangle_product]
  have hentry (j : Fin n) :
      ((S ∩ isolationWindow i a j).card : ℝ≥0∞) / (S.card : ℝ≥0∞) =
        if j = i then (1 / (n : ℝ≥0∞))
        else (((n-1 : ℕ) : ℝ≥0∞) / (n : ℝ≥0∞)) := by
    by_cases h : j = i
    · simp [isolationWindow, h, Finset.inter_singleton_of_mem ha, hcard]
    · simp [isolationWindow, h, Finset.inter_erase, Finset.card_erase_of_mem ha, hcard]
  simp_rw [hentry]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  simp only [ite_true]
  congr 1
  calc
    _ = ∏ _j ∈ (Finset.univ.erase i),
        (((n-1 : ℕ) : ℝ≥0∞) / (n : ℝ≥0∞)) := by
      apply Finset.prod_congr rfl
      intro j hj
      simp [(Finset.mem_erase.mp hj).1]
    _ = _ := by simp

/-- Statewise fixation hazard from the actual joint law on a common N-arm set.
Existence of an unused arm and the numerical 1/(4N) bound are separate obligations. -/
theorem transition_common_fixation_lower {n k : ℕ} (S : Finset (Fin k))
    (s : State n k) (i : Fin n) (a : Fin k) (hmem : a ∈ S) (hcard : S.card = n)
    (hi : s i = none) (ha : ∀ j b, s j = some b → b ≠ a) :
    (1 / (n : ℝ≥0∞)) * (((n-1 : ℕ) : ℝ≥0∞) / (n : ℝ≥0∞))^(n-1) ≤
      (transition (fun _ : Fin n => S) (fun _ => ⟨a, hmem⟩) s).toOuterMeasure
        {s' | s' i = some a} := by
  rw [← jointDraw_isolation S i a hmem hcard]
  unfold transition
  rw [PMF.toOuterMeasure_map_apply]
  apply MeasureTheory.measure_mono
  intro draw hd
  exact fixationWindow_fixes s draw i a hi ha
    (fun j => isolationWindow_subset s i a j (hd j))

/-- One unfixed player leaves at most N-1 occupied labels, so an N-label set
contains an unused label. No successful coordination is assumed. -/
theorem exists_unoccupied {n k : ℕ} (S : Finset (Fin k)) (s : State n k)
    (i : Fin n) (hi : s i = none) (hcard : S.card = n) :
    ∃ a ∈ S, ∀ j b, s j = some b → b ≠ a := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  obtain ⟨a0, ha0⟩ := Finset.card_pos.mp (hcard.symm ▸ hn)
  let F := Finset.univ.filter (fun j : Fin n => s j ≠ none)
  let A := F.image (fun j => (s j).getD a0)
  have hproper : F ⊂ Finset.univ := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.filter_subset _ _, ?_⟩
    intro heq
    have him : i ∈ F := by rw [heq]; simp
    simp [F, hi] at him
  have hFlt : F.card < n := by simpa using Finset.card_lt_card hproper
  have hAlt : A.card < n := (Finset.card_image_le).trans_lt hFlt
  have hnot : ¬ S ⊆ A := by
    intro hsub
    have := Finset.card_le_card hsub
    omega
  obtain ⟨a, ha, hna⟩ := Finset.not_subset.mp hnot
  refine ⟨a, ha, ?_⟩
  intro j b hsj hba
  apply hna
  apply Finset.mem_image.mpr
  refine ⟨j, ?_, ?_⟩
  · simp [F, hsj]
  · simp [hsj, hba]

/-- A statewise hazard for every unfixed player, produced without an externally
supplied unused arm, settling event, or hazard premise. -/
theorem transition_unfixed_hazard {n k : ℕ} (S : Finset (Fin k))
    (hne : S.Nonempty) (s : State n k) (i : Fin n) (hi : s i = none)
    (hcard : S.card = n) :
    (1 / (n : ℝ≥0∞)) * (((n-1 : ℕ) : ℝ≥0∞) / (n : ℝ≥0∞))^(n-1) ≤
      (transition (fun _ : Fin n => S) (fun _ => hne) s).toOuterMeasure
        {s' | s' i ≠ none} := by
  obtain ⟨a, hmem, ha⟩ := exists_unoccupied S s i hi hcard
  have h := transition_common_fixation_lower S s i a hmem hcard hi ha
  apply h.trans
  apply MeasureTheory.measure_mono
  intro s' hs'
  change s' i = some a at hs'
  simp [hs']

/-- Nondegenerate coordination component: two players, three ambient arms,
two distinct candidates, actual transition law and an unfixed initial state. -/
theorem two_player_three_arm_hazard :
    (1 / 4 : ℝ≥0∞) ≤
      (transition (fun _ : Fin 2 => ({0, 1} : Finset (Fin 3)))
        (fun _ => by simp) (initial 2 3)).toOuterMeasure {s' | s' 0 ≠ none} := by
  have h := transition_unfixed_hazard ({0, 1} : Finset (Fin 3)) (by simp)
    (initial 2 3) (0 : Fin 2) rfl (by decide)
  norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one, one_div] at h ⊢
  convert h using 1
  norm_num [← ENNReal.mul_inv]

theorem two_player_isolation_probability :
    (jointDraw (fun _ : Fin 2 => ({0, 1} : Finset (Fin 3))) (fun _ => by simp)).toOuterMeasure
      {draw | ∀ j, draw j ∈ isolationWindow (0 : Fin 2) (0 : Fin 3) j} =
        (1 / 4 : ℝ≥0∞) := by
  have h := jointDraw_isolation ({0, 1} : Finset (Fin 3)) (0 : Fin 2) (0 : Fin 3)
    (by simp) (by decide)
  norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one, one_div] at h ⊢
  convert h using 1
  norm_num [← ENNReal.mul_inv]

#print axioms two_player_three_arm_hazard
#print axioms two_player_isolation_probability
#print axioms transition_unfixed_hazard
#print axioms transition_common_fixation_lower
#print axioms transition_fixation_lower
#print axioms step_localUpdate
#print axioms stateLaw_within
#print axioms jointDraw_rectangle
end MusicalChairsProbabilityPrototype


```

</details>
