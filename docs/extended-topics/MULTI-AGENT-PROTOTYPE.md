# Coordination prototype: exact compiled boundary

2026-09-20. Source: Rosenski--Shamir--Szlak, ICML 2016, static Algorithm 2
(main physical p3) and supplement A.1 Lemma 4 (physical pp6--7).
This scratch is compiled in the shared Lake environment but is not imported
by BanditRLProof or Tests. It is not an accepted production MC theorem.

Each player stores either no fixed arm or one fixed arm. It plays its fixed
arm when present, otherwise its current private candidate draw. An unfixed
player becomes fixed exactly when no other action equals its own; a fixed
player never becomes unfixed. `action_local` proves that changing all other
players' states and draws cannot change this player's action. This is
coordinate locality for the coordination stage; the full observable-history
policy and estimator are not implemented here.

For any sequence of joint draws, all fixed arms stay distinct. The induction
is pathwise: two previously fixed players use the induction hypothesis; a
new fixed player had no matching action, which excludes both old fixed and
simultaneous new fixed players on its arm. This proof imposes no correct-N,
common-candidate-set or success-probability assumption.

The random producer takes arbitrary nonempty local candidate sets, draws a
uniform element of their finite Cartesian product, maps to chosen arms and
then to the next state. Repeated PMF bind constructs the actual state law.
The map/bind support rules transport the pathwise invariant to every supported
state at every finite time. Marginal independence, quantitative fixation hazard,
finite expected waiting time and regret are not yet proved by this file.

The source requires these candidate sets to be generated from exploration.
Here they are explicit parameters, so this is only the coordination transition
component. No means, rewards, exploration, N estimator, top-N correctness,
full learner, canary or concentration statement is encoded. The global finite
player type indexes the process; it is not evidence that a local unknown-N
history policy has already been formalized.

Actual upstream reuse: `PMF.uniformOfFintype`, `PMF.map`, `PMF.bind`,
`PMF.mem_support_map_iff`, `PMF.mem_support_bind_iff`. No ABRL theorem transfer
or efficiency claim is made. The prototype exposes ten proved propositions.
All are included in the axiom audit receipt; standard Lean axioms only.

The first compile diagnosed a missing `noncomputable` annotation on the
trajectory calling the classical transition. Adding that annotation changed
no definition or theorem contract. The subsequent focused compiler run passed.
Independent decoding/source comparison and source repair receipts are bound in
`runs/extended-topics-20260920/multi-agent-source-review.json`.

<details>
<summary>Exact compiled scratch: definitions and proofs</summary>

```lean
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Tactic

/-! Scratch coordination producer. Not imported by the public root. No unknown-N
estimator, reward process, concentration or complete regret theorem is claimed.
Candidate sets are local phase-one outputs; their correctness remains to be
produced by that phase. Fresh finite joint draws and permanent fixation are
constructed here, not assumed as successful coordination. -/
namespace MusicalChairsCoordinationPrototype
open scoped Classical
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

/-- Uniform law on the finite Cartesian product of local candidate sets.
Independence/marginal and fixation-hazard theorems are still pending. -/
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

#print axioms stateLaw_distinct
#print axioms action_local
end MusicalChairsCoordinationPrototype

```

</details>
