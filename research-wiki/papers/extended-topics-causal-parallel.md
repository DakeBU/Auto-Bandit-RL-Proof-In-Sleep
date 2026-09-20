# Parallel causal allocation: normalized design and actual regret

Source: Lattimore, Lattimore and Reid, *Causal Bandits: Learning Good Interventions via Causal Inference*, official NIPS 2016 supplement p.15, Proposition 8 (arXiv v1 Proposition 9). The consumer is the known-parent-law general-graph Algorithm 2 and repaired Theorem 3, not the separate unknown-marginal parallel algorithm. The frozen mathematical repair is recorded in `docs/extended-topics/CAUSAL-PARALLEL-ROUTE.md` and its independent review receipt.

## Model and constructed complexity

There are N >= 2 independent binary root nodes, success probabilities q_i in [0,1], and a binary reward with an arbitrary conditional PMF on the full root assignment. All roots are reward parents; root parent sets are empty. The action family consists of observation and each atomic do(X_i=b), so K=2N+1. Every intervention leaves the reward table unchanged.

For integer tau in [2,N], let I_tau={i:min(q_i,1-q_i)<1/tau}. Define m(q) as the least tau with |I_tau|<=tau. The implementation constructs this natural-number minimum, proves existence using tau=N, proves its full bounds/cardinality specification and minimality. The cardinality property is not a caller-supplied premise.

For an atomic action a=(i,b), write r_a=Pr(X_i=b). Let S={a:r_a<1/m}. Because m>=2, at most one value of a given coordinate can belong to S. Injecting S into I_m proves |S|<=m. The implementation needs this bound; it does not rely on an unproved exact set cardinality identity.

## Repaired actual allocation

Each rare action gets weight 1/(2m), each other atomic action gets zero, and observation gets 1-D, where D=|S|/(2m)<=1/2. The weights are proved nonnegative and sum to one, and the existing allocationOfWeights constructor makes the actual PMF. Its observation mass is at least 1/2.

This is an explicit source correction: the supplement's printed observation weight 1/2+(1-D) sums with the atomic weights to 3/2, not one. Its later denominator 1/2+D is not reused. The main text's non-strict rare inequality and fixed observation mass also cannot replace the supplement's strict set. At q_i=1/2, that non-strict recipe includes every atomic action, whereas the strict set is empty. These repairs preserve the claimed bound; they do not claim the asymptotic proposition is false.

## Actual-law proof of coverage and cost

The root PMF is defined by sequential joint sampling of independent Bernoulli tables with the selected table replaced by a point mass. Product factorization is a theorem about that construction. For every atomic a=(i,b) and configuration z,

$$ r_a P_a(z)\le P_0(z). $$

It is equality when z_i=b and has zero left side otherwise. This identity remains valid at q_i=0 or 1. For the actual design mixture Q, each component gives Q(z)>=eta_a P_a(z). Consequently:

- Rare a: Q(z)>=P_a(z)/(2m).
- Observation: Q(z)>=P_0(z)/2 and m>=1.
- Nonrare a: r_a>=1/m, so P_a(z)<=m P_0(z)<=2m Q(z).

Thus every action satisfies P_a(z)<=2m Q(z). If Q(z)=0, every P_a(z)=0; coverage is derived even for deterministic coordinates and intervention-created states. On positive Q the ratio is at most 2m, and on zero Q it is genuinely off the entire family support. Summing against P_a gives secondMoment<=2m, hence designCost<=2m. The existing attained optimizer then gives optimal design cost<=2m. This is a cost comparison, not an ordering of actual regrets under two different allocations.

## Full DAG and performance connection

The graph adapter appends the arbitrary reward kernel to those independent roots. It proves that each actual reward-parent intervention law is the root law pushed through the injective parent-configuration map. Thus the parent law is independent of the unknown reward table. Coverage and exact design cost transport through this map, then the actual Algorithm 2 sample/recommendation/expectation producer applies.

For either the repaired allocation or the actual attained optimum, let c be that allocation's true design cost, L=log(2TK), and B=sqrt(cT/L). For each positive fixed T,

$$ E[R_T]\le(2\sqrt{2}+7)\sqrt{2m(q)L/T}+1/T. $$

Only the bound's right side relaxes c to 2m(q); the learner's actual threshold retains c. The source coefficient and probability-direction repairs from the common performance producer remain explicit. The finite action interface takes a fixed total order and a measurable space with measurable singletons. These are finite-set order/measure representations, not an extra reward or confidence assumption. No numerical optimizer, adaptive unknown-q estimator or cumulative-regret result is claimed.

## Current verification and remaining scope

All three production modules compile together (3606 jobs), and the concrete witnesses compile (3607 jobs). Independent production and canary blind/source review accepts the packet with the explicit source deltas above. Shared validation results are recorded in causal-parallel-validation.json. The original noisy and native heterogeneous packets were accepted separately. This packet does not complete the remaining classic/recent source-screening or all-topic ICLR evidence obligations, and is not a whole-topic acceptance, main merge or deployment.

## Concrete boundary witnesses

For N=2 and q=(1/2,1/2), rarity is 2, the strict rare set is empty, observation has allocation mass 1 and each root assignment has observational mass 1/4. Observation second moment is 1, each atomic intervention second moment is 2, so the actual design cost is exactly 2.

For q=(0,0), rarity is 2, observation has mass 1/2, each do(X_i=true) has mass 1/4 and each do(X_i=false) has zero allocation mass. The rare intervention second moment is exactly 4, so the bound 2m(q)=4 is attained. Observation alone is uncovered: the assignment (true,false) is impossible observationally but possible under do(X_0=true).

Both witnesses use the stochastic reward kernel Pr(Y=true|x)=3/4 if either root is true and 1/4 otherwise. Their actual all-horizon learners have K=5 and thresholds sqrt(2T/log(10T)) and sqrt(4T/log(10T)), respectively. The displayed RHS in both concrete instances uses the relaxed cost bound 4. The finite action order is supplied using a chosen equivalence with Fin; no observation-first tie convention is asserted. These are local constructions, not numerical examples attributed to the source paper.

## Reuse and assumption ledger

The new allocation reuses allocationOfWeights and optimalAllocation_minimizes. Actual laws reuse joint_factorization and GraphModel.parentLaw_prefix; injective pushforward reuses covers_map_injective and designCost_map_injective. The two endpoints reuse GraphModel.expected_simpleRegret_source_bound and expected_simpleRegret_optimal. Mathlib supplies Nat.find, finite cardinality/product identities, Bernoulli PMFs and finite integration.

- Same: known q, independent binary roots, all atomic interventions, finite fixed budget and expected simple regret.
- Explicit source correction: strict rare set and normalized observation mass 1-D; inherited coefficient/failure-direction repairs remain visible.
- Source/contract scope: N>=2 and binary reward; no unknown-q learner.
- Finite API representation: supplied action total order, measurable space and measurable singletons.
- Remaining: classic/recent source screening and ICLR evidence; all ten topics remain a larger unfinished Goal.

## Exact Lean implementation

<details>
<summary>BanditRLProof/Algorithms/CausalParallelDesign.lean</summary>

```lean
import BanditRLProof.Algorithms.CausalOptimalAllocation

/-! Constructed rarity parameter and normalized finite intervention design. -/
namespace BanditRLProof.Causal
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 800000

structure ParallelParameters (N : ℕ) where
  q : Fin N → ℝ
  nonneg : ∀ i, 0 ≤ q i
  le_one : ∀ i, q i ≤ 1
  two_le : 2 ≤ N

namespace ParallelParameters
variable {N : ℕ} (p : ParallelParameters N)

noncomputable def rareIndices (tau : ℕ) : Finset (Fin N) :=
  Finset.univ.filter fun i => min (p.q i) (1-p.q i) < 1/(tau:ℝ)

theorem exists_rarity : ∃ m : ℕ, 2 ≤ m ∧ m ≤ N ∧ (p.rareIndices m).card ≤ m := by
  refine ⟨N,p.two_le,le_rfl,?_⟩
  exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin N)

noncomputable def rarity : ℕ := Nat.find p.exists_rarity

theorem rarity_spec : 2 ≤ p.rarity ∧ p.rarity ≤ N ∧ (p.rareIndices p.rarity).card ≤ p.rarity :=
  Nat.find_spec p.exists_rarity

theorem rarity_minimal (tau : ℕ) (h2 : 2 ≤ tau) (hN : tau ≤ N)
    (hc : (p.rareIndices tau).card ≤ tau) : p.rarity ≤ tau :=
  Nat.find_min' p.exists_rarity ⟨h2,hN,hc⟩

def valueProbability (a : Fin N × Bool) : ℝ := if a.2 then p.q a.1 else 1-p.q a.1

theorem valueProbability_nonneg (a : Fin N × Bool) : 0 ≤ p.valueProbability a := by
  rcases a with ⟨i,b⟩
  cases b <;> simp [valueProbability, p.nonneg, p.le_one]

theorem rarity_pos : (0 : ℝ) < p.rarity := by
  have h := p.rarity_spec.1
  exact_mod_cast (show 0 < p.rarity by omega)

theorem rarity_reciprocal_le_half : 1/(p.rarity:ℝ) ≤ 1/2 := by
  apply one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2)
  exact_mod_cast p.rarity_spec.1

noncomputable def rareActions : Finset (Fin N × Bool) :=
  Finset.univ.filter fun a => p.valueProbability a < 1/(p.rarity:ℝ)

theorem rareActions_card_le : p.rareActions.card ≤ p.rarity := by
  apply le_trans _ p.rarity_spec.2.2
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro a ha
    change a ∈ p.rareActions at ha
    simp only [rareActions, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    change a.1 ∈ p.rareIndices p.rarity
    simp only [rareIndices, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases a with ⟨i,b⟩
    cases b
    · exact (min_le_right _ _).trans_lt ha
    · exact (min_le_left _ _).trans_lt ha
  · intro a ha b hb heq
    change a ∈ p.rareActions at ha
    change b ∈ p.rareActions at hb
    rcases a with ⟨i,x⟩
    rcases b with ⟨j,y⟩
    change i = j at heq
    subst j
    simp only [rareActions, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    have hh := p.rarity_reciprocal_le_half
    cases x <;> cases y <;> simp_all [valueProbability] <;> linarith

noncomputable def rareWeight : ℝ := 1/(2*p.rarity)
noncomputable def atomicTotal : ℝ := p.rareActions.card * p.rareWeight

theorem rareWeight_pos : 0 < p.rareWeight := by
  unfold rareWeight
  exact one_div_pos.mpr (mul_pos (by norm_num) p.rarity_pos)

theorem atomicTotal_bounds : 0 ≤ p.atomicTotal ∧ p.atomicTotal ≤ 1/2 := by
  constructor
  · exact mul_nonneg (Nat.cast_nonneg _) p.rareWeight_pos.le
  · have hc : (p.rareActions.card:ℝ) ≤ p.rarity := by exact_mod_cast p.rareActions_card_le
    have h := mul_le_mul_of_nonneg_right hc p.rareWeight_pos.le
    have heq : (p.rarity:ℝ)*p.rareWeight = 1/2 := by
      unfold rareWeight
      field_simp [p.rarity_pos.ne']
    exact h.trans_eq heq

noncomputable def allocationWeight : Option (Fin N × Bool) → ℝ
  | none => 1-p.atomicTotal
  | some a => if a ∈ p.rareActions then p.rareWeight else 0

theorem allocationWeight_nonneg (a : Option (Fin N × Bool)) : 0 ≤ p.allocationWeight a := by
  cases a with
  | none => change 0 ≤ 1-p.atomicTotal; linarith [p.atomicTotal_bounds.2]
  | some a => simp only [allocationWeight]; split_ifs; exact p.rareWeight_pos.le; exact le_rfl

theorem allocationWeight_sum : ∑ a, p.allocationWeight a = 1 := by
  rw [Fintype.sum_option]
  simp only [allocationWeight]
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  change (1-p.atomicTotal)+p.atomicTotal = 1
  ring

noncomputable def allocation : PMF (Option (Fin N × Bool)) :=
  allocationOfWeights p.allocationWeight ⟨p.allocationWeight_nonneg,p.allocationWeight_sum⟩

theorem allocation_mass (a : Option (Fin N × Bool)) : mass p.allocation a = p.allocationWeight a := by
  exact allocationOfWeights_mass _ _ _

theorem allocation_empty_ge_half : 1/2 ≤ mass p.allocation none := by
  rw [allocation_mass]
  change 1/2 ≤ 1-p.atomicTotal
  linarith [p.atomicTotal_bounds.2]

end ParallelParameters

theorem covers_of_mass_domination {A Z : Type*} (p : A → PMF Z) (q : PMF Z)
    (C : ℝ) (h : ∀ a z, mass (p a) z ≤ C*mass q z) : Covers p q := by
  intro a z hp hq
  have hh := h a z
  rw [hq,mul_zero] at hh
  exact hp (le_antisymm hh (mass_nonneg _ _))

theorem ratio_le_of_mass_domination {Z : Type*} (p q : PMF Z) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ z, mass p z ≤ C*mass q z) (z : Z) : ratio p q z ≤ C := by
  by_cases hz : mass q z = 0
  · simpa [ratio,hz] using hC
  · exact (div_le_iff₀ (lt_of_le_of_ne (mass_nonneg q z) (Ne.symm hz))).2 (h z)

theorem secondMoment_le_of_mass_domination {Z : Type*} [Fintype Z]
    (p q : PMF Z) (C : ℝ) (hC : 0 ≤ C) (h : ∀ z, mass p z ≤ C*mass q z) :
    secondMoment p q ≤ C := by
  calc
    _ ≤ ∑ z, mass p z*C := Finset.sum_le_sum fun z _ =>
      mul_le_mul_of_nonneg_left (ratio_le_of_mass_domination p q C hC h z) (mass_nonneg p z)
    _ = C := by rw [← Finset.sum_mul, sum_mass, one_mul]

end BanditRLProof.Causal

```

</details>

<details>
<summary>BanditRLProof/Algorithms/CausalParallelLaw.lean</summary>

```lean
import BanditRLProof.Algorithms.CausalParallelDesign

/-! Actual independent-root intervention laws and their covered allocation cost. -/
namespace BanditRLProof.Causal
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem mixture_mass_ge_component {A Z : Type*} [Fintype A]
    (eta : PMF A) (p : A → PMF Z) (a : A) (z : Z) :
    mass eta a * mass (p a) z ≤ mass (mixture eta p) z := by
  rw [mixture_mass]
  exact Finset.single_le_sum (fun b _ => mul_nonneg (mass_nonneg eta b)
    (mass_nonneg (p b) z)) (Finset.mem_univ a)

namespace ParallelParameters
variable {N : ℕ} (p : ParallelParameters N)

noncomputable def rootTable (i : Fin N) : PMF Bool :=
  PMF.bernoulli ⟨p.q i,p.nonneg i⟩ (p.le_one i)

theorem rootTable_mass (i : Fin N) (b : Bool) : mass (p.rootTable i) b = p.valueProbability (i,b) := by
  have hq : (⟨p.q i,p.nonneg i⟩:NNReal) ≤ 1 := p.le_one i
  have he : ENNReal.ofNNReal ⟨p.q i,p.nonneg i⟩ ≤ 1 := ENNReal.coe_le_one_iff.mpr hq
  cases b <;> simp [rootTable, mass, PMF.bernoulli_apply, valueProbability,
    ENNReal.toReal_sub_of_le he ENNReal.one_ne_top]

def rootAction (a : Option (Fin N × Bool)) (i : Fin N) : Option Bool :=
  a.bind fun b => if i = b.1 then some b.2 else none

noncomputable def rootLaw (a : Option (Fin N × Bool)) : PMF (Fin N → Bool) :=
  joint (intervene (fun i _ => p.rootTable i) (rootAction a))

theorem rootLaw_mass (a : Option (Fin N × Bool)) (x : Fin N → Bool) :
    mass (p.rootLaw a) x = ∏ i, match a with
      | none => p.valueProbability (i,x i)
      | some b => if i = b.1 then (if x i = b.2 then 1 else 0)
          else p.valueProbability (i,x i) := by
  unfold mass rootLaw
  rw [joint_factorization, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro i _
  cases a with
  | none => simpa [intervene,rootAction] using p.rootTable_mass i (x i)
  | some b =>
    by_cases hi : i = b.1
    · subst i
      by_cases hx : x b.1 = b.2 <;> simp [intervene,rootAction,hx,PMF.pure_apply]
    · simpa [intervene,rootAction,hi] using p.rootTable_mass i (x i)

theorem rootLaw_atom_mass (i : Fin N) (b : Bool) (x : Fin N → Bool) :
    mass (p.rootLaw (some (i,b))) x =
      (if x i = b then 1 else 0) * ∏ j ∈ Finset.univ.erase i, p.valueProbability (j,x j) := by
  rw [rootLaw_mass, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [if_true]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  simp [(Finset.mem_erase.mp hj).1]

theorem atomic_observational_domination (a : Fin N × Bool) (x : Fin N → Bool) :
    p.valueProbability a * mass (p.rootLaw (some a)) x ≤ mass (p.rootLaw none) x := by
  rcases a with ⟨i,b⟩
  rw [rootLaw_atom_mass]
  by_cases hx : x i = b
  · rw [if_pos hx, one_mul, rootLaw_mass,
      ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    simp only [hx, le_refl]
  · rw [if_neg hx,zero_mul,mul_zero]
    exact mass_nonneg _ _

theorem allocated_mass_domination (a : Option (Fin N × Bool)) (x : Fin N → Bool) :
    mass (p.rootLaw a) x ≤ (2*p.rarity)*mass (mixture p.allocation p.rootLaw) x := by
  have hq := mass_nonneg (mixture p.allocation p.rootLaw) x
  have hm := p.rarity_pos
  have hm2 : (2:ℝ) ≤ p.rarity := by exact_mod_cast p.rarity_spec.1
  have hempty : (1/2)*mass (p.rootLaw none) x ≤ mass (mixture p.allocation p.rootLaw) x :=
    (mul_le_mul_of_nonneg_right p.allocation_empty_ge_half (mass_nonneg _ _)).trans
      (mixture_mass_ge_component p.allocation p.rootLaw none x)
  cases a with
  | none => nlinarith
  | some a =>
    by_cases ha : a ∈ p.rareActions
    · have h := mixture_mass_ge_component p.allocation p.rootLaw (some a) x
      rw [p.allocation_mass] at h
      simp only [allocationWeight,ha,if_true,rareWeight] at h
      have hc : (2*(p.rarity:ℝ)) * (1/(2*p.rarity)) = 1 := by field_simp
      have hh := mul_le_mul_of_nonneg_left h (show 0 ≤ 2*(p.rarity:ℝ) by positivity)
      rw [← mul_assoc,hc,one_mul] at hh
      exact hh
    · have hr : 1/(p.rarity:ℝ) ≤ p.valueProbability a := by
        simpa [rareActions] using ha
      have hdom := p.atomic_observational_domination a x
      have hbase := (mul_le_mul_of_nonneg_right hr (mass_nonneg (p.rootLaw (some a)) x)).trans hdom
      have hscaled := mul_le_mul_of_nonneg_left hbase hm.le
      have hc : (p.rarity:ℝ) * (1/p.rarity) = 1 := by field_simp
      rw [← mul_assoc,hc,one_mul] at hscaled
      have hmix := mul_le_mul_of_nonneg_left hempty hm.le
      nlinarith

theorem allocation_covers : Covers p.rootLaw (mixture p.allocation p.rootLaw) :=
  covers_of_mass_domination _ _ _ p.allocated_mass_domination

theorem allocation_cost_le : designCost p.rootLaw p.allocation ≤ 2*p.rarity := by
  apply Finset.sup'_le
  intro a _
  exact secondMoment_le_of_mass_domination _ _ _ (by positivity)
    (p.allocated_mass_domination a)

theorem optimal_cost_le : designCost p.rootLaw (optimalAllocation p.rootLaw) ≤ 2*p.rarity :=
  (optimalAllocation_minimizes p.rootLaw p.allocation p.allocation_covers).trans p.allocation_cost_le

end ParallelParameters
end BanditRLProof.Causal

```

</details>

<details>
<summary>BanditRLProof/Algorithms/CausalParallelRegret.lean</summary>

```lean
import BanditRLProof.Algorithms.CausalParallelLaw
import BanditRLProof.Algorithms.CausalImportanceTransport
import BanditRLProof.Algorithms.CausalAllocationRegret

/-! Parallel DAG adapter and actual allocation-dependent expected simple regret. -/
namespace BanditRLProof.Causal.ParallelParameters
open scoped Classical
open MeasureTheory
set_option autoImplicit false
set_option maxHeartbeats 800000

variable {N : ℕ} (p : ParallelParameters N) (reward : (Fin N → Bool) → PMF Bool)

noncomputable def graph : GraphModel Bool (N+1) where
  parents := Fin.lastCases Finset.univ (fun _ => ∅)
  table := Fin.lastCases reward (fun i _ => p.rootTable i)
  local_table := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · intro h h' heq
      simp only [Fin.lastCases_last] at heq ⊢
      have hh : h = h' := funext fun j => heq j (Finset.mem_univ _)
      rw [hh]
    · intro h h' _
      simp only [Fin.lastCases_castSucc]

def graphAction (a : Option (Fin N × Bool)) : Fin (N+1) → Option Bool :=
  Fin.lastCases none (rootAction a)

theorem graphAction_reward (a : Option (Fin N × Bool)) : graphAction a (Fin.last N) = none := by
  simp [graphAction]

theorem graph_parentLaw (a : Option (Fin N × Bool)) :
    (p.graph reward).parentLaw (graphAction a) (Fin.last N) =
      (p.rootLaw a).map ((p.graph reward).parentConfig (Fin.last N)) := by
  rw [GraphModel.parentLaw_prefix]
  congr 2
  funext i h
  change intervene (p.graph reward).table (graphAction a) i.castSucc h =
    intervene (fun j _ => p.rootTable j) (rootAction a) i h
  simp [intervene,graph,graphAction]

theorem graph_parentConfig_injective :
    Function.Injective ((p.graph reward).parentConfig (Fin.last N)) := by
  intro x y h
  funext i
  exact congrFun h ⟨i,by simp only [graph,Fin.lastCases_last]; exact Finset.mem_univ _⟩

theorem graph_allocation_covers :
    Covers (fun a => (p.graph reward).parentLaw (graphAction a) (Fin.last N))
      (mixture p.allocation (fun a => (p.graph reward).parentLaw (graphAction a) (Fin.last N))) := by
  simp only [p.graph_parentLaw,mixture_map]
  exact covers_map_injective p.rootLaw _ p.allocation_covers _ (p.graph_parentConfig_injective reward)

theorem graph_designCost (eta : PMF (Option (Fin N × Bool))) :
    designCost (fun a => (p.graph reward).parentLaw (graphAction a) (Fin.last N)) eta =
      designCost p.rootLaw eta := by
  simp only [p.graph_parentLaw]
  exact designCost_map_injective p.rootLaw eta _ (p.graph_parentConfig_injective reward)

theorem graph_allocation_cost_le :
    designCost (fun a => (p.graph reward).parentLaw (graphAction a) (Fin.last N)) p.allocation ≤
      2*p.rarity := by
  rw [p.graph_designCost]
  exact p.allocation_cost_le

theorem graph_optimal_cost_le :
    let laws := fun a => (p.graph reward).parentLaw (graphAction a) (Fin.last N)
    designCost laws (optimalAllocation laws) ≤ 2*p.rarity := by
  exact (optimalAllocation_minimizes _ p.allocation (p.graph_allocation_covers reward)).trans
    (p.graph_allocation_cost_le reward)

variable [LinearOrder (Option (Fin N × Bool))]
variable [MeasurableSpace (Option (Fin N × Bool))]
variable [MeasurableSingletonClass (Option (Fin N × Bool))]

theorem expected_simpleRegret_parallel (T : ℕ) (hT : 0 < T) :
    let m := designCost p.rootLaw p.allocation
    let L := sourceLog T (Fintype.card (Option (Fin N × Bool)))
    let B := sourceThreshold m T L
    (∫ w, (p.graph reward).simpleRegret id graphAction p.allocation (Fin.last N) B w
      ∂(p.graph reward).sampleLaw graphAction p.allocation T) ≤
      (2*Real.sqrt 2+7)*Real.sqrt ((2*p.rarity)*L/T)+1/(T:ℝ) := by
  have h := (p.graph reward).expected_simpleRegret_source_bound id graphAction p.allocation
    (Fin.last N) graphAction_reward (p.graph_allocation_covers reward) T hT
  dsimp only at h ⊢
  rw [p.graph_designCost] at h
  refine h.trans (add_le_add ?_ le_rfl)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.sqrt_le_sqrt
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_right p.allocation_cost_le
    (sourceLog_pos T _ hT Fintype.card_pos).le

theorem expected_simpleRegret_parallel_optimal (T : ℕ) (hT : 0 < T) :
    let laws := fun a => (p.graph reward).parentLaw (graphAction a) (Fin.last N)
    let eta := optimalAllocation laws
    let m := designCost laws eta
    let L := sourceLog T (Fintype.card (Option (Fin N × Bool)))
    let B := sourceThreshold m T L
    (∫ w, (p.graph reward).simpleRegret id graphAction eta (Fin.last N) B w
      ∂(p.graph reward).sampleLaw graphAction eta T) ≤
      (2*Real.sqrt 2+7)*Real.sqrt ((2*p.rarity)*L/T)+1/(T:ℝ) := by
  have h := (p.graph reward).expected_simpleRegret_optimal id graphAction
    (Fin.last N) graphAction_reward T hT
  dsimp only at h ⊢
  refine h.trans (add_le_add ?_ le_rfl)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.sqrt_le_sqrt
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_right (p.graph_optimal_cost_le reward)
    (sourceLog_pos T _ hT Fintype.card_pos).le

end BanditRLProof.Causal.ParallelParameters

```

</details>

<details>
<summary>Tests/CausalParallelCanary.lean</summary>

```lean
import BanditRLProof.Algorithms.CausalParallelRegret

/-! Full-support and deterministic-root witnesses for the actual parallel construction. -/
namespace Tests.CausalParallelCanary
open BanditRLProof.Causal MeasureTheory
open scoped Classical
set_option maxHeartbeats 1600000
set_option maxRecDepth 4000
noncomputable section

def fair : ParallelParameters 2 where
  q _ := 1/2
  nonneg _ := by norm_num
  le_one _ := by norm_num
  two_le := by norm_num

def deterministic : ParallelParameters 2 where
  q _ := 0
  nonneg _ := le_rfl
  le_one _ := by norm_num
  two_le := by norm_num

theorem two_node_rarity (p : ParallelParameters 2) : p.rarity = 2 := by
  have h := p.rarity_spec
  omega

theorem fair_rare_empty : fair.rareActions = ∅ := by
  ext a
  rcases a with ⟨i,b⟩
  cases b <;> norm_num [ParallelParameters.rareActions,two_node_rarity,
    ParallelParameters.valueProbability,fair]

theorem deterministic_rare_card : deterministic.rareActions.card = 2 := by
  simp only [ParallelParameters.rareActions,two_node_rarity,
    ParallelParameters.valueProbability,deterministic,Finset.card_eq_sum_ones,
    Finset.sum_filter,Fintype.sum_prod_type,Fin.sum_univ_two,Fintype.sum_bool]
  norm_num

theorem fair_weights (a : Option (Fin 2 × Bool)) : mass fair.allocation a =
    match a with | none => 1 | some _ => 0 := by
  rw [ParallelParameters.allocation_mass]
  cases a <;> simp [ParallelParameters.allocationWeight,ParallelParameters.atomicTotal,
    fair_rare_empty]

theorem deterministic_weights (a : Option (Fin 2 × Bool)) : mass deterministic.allocation a =
    match a with | none => 1/2 | some b => if b.2 then 1/4 else 0 := by
  rw [ParallelParameters.allocation_mass]
  cases a with
  | none => norm_num [ParallelParameters.allocationWeight,ParallelParameters.atomicTotal,
      deterministic_rare_card,ParallelParameters.rareWeight,two_node_rarity]
  | some a => rcases a with ⟨i,b⟩; cases b <;>
      norm_num [ParallelParameters.allocationWeight,ParallelParameters.rareActions,
        ParallelParameters.rareWeight,two_node_rarity,ParallelParameters.valueProbability,deterministic]

def stateEquiv : (Fin 2 → Bool) ≃ Bool × Bool where
  toFun x := (x 0,x 1)
  invFun s := ![s.1,s.2]
  left_inv x := by funext i; fin_cases i <;> rfl
  right_inv s := by rcases s with ⟨x,y⟩; rfl

theorem fair_full_support (x : Fin 2 → Bool) : mass (fair.rootLaw none) x = 1/4 := by
  rw [ParallelParameters.rootLaw_mass]
  simp only [Fin.prod_univ_two,ParallelParameters.valueProbability,fair]
  rcases Bool.eq_false_or_eq_true (x 0) with h0 | h0 <;>
    rcases Bool.eq_false_or_eq_true (x 1) with h1 | h1 <;> norm_num [h0,h1]

theorem fair_secondMoment (a : Option (Fin 2 × Bool)) :
    secondMoment (fair.rootLaw a) (mixture fair.allocation fair.rootLaw) =
      match a with | none => 1 | some _ => 2 := by
  unfold secondMoment ratio
  rw [← Equiv.sum_comp stateEquiv.symm]
  simp only [mixture_mass, fair_weights]
  cases a with
  | none =>
    norm_num [Fintype.sum_prod_type,Fintype.sum_bool,mixture_mass,Fintype.sum_option,
      fair_weights,fair_full_support]
  | some a =>
    rcases a with ⟨i,b⟩
    fin_cases i <;> cases b <;>
      (simp only [Fintype.sum_prod_type,Fintype.sum_bool,mixture_mass,Fintype.sum_option,
        fair_weights,ParallelParameters.rootLaw_mass,Fin.prod_univ_two,
        ParallelParameters.valueProbability,fair,stateEquiv,Matrix.cons_val_zero,Matrix.cons_val_one,
        Fin.reduceFinMk,Fin.ext_iff]
       norm_num)

theorem fair_cost : designCost fair.rootLaw fair.allocation = 2 := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro a _
    rw [fair_secondMoment]
    cases a <;> norm_num
  · have h := secondMoment_le_designCost fair.rootLaw fair.allocation (some (0,true))
    rwa [fair_secondMoment] at h

theorem deterministic_rare_secondMoment :
    secondMoment (deterministic.rootLaw (some (0,true)))
      (mixture deterministic.allocation deterministic.rootLaw) = 4 := by
  unfold secondMoment ratio
  rw [← Equiv.sum_comp stateEquiv.symm]
  simp only [mixture_mass, deterministic_weights]
  simp only [Fintype.sum_prod_type,Fintype.sum_bool,mixture_mass,Fintype.sum_option,
    Fin.sum_univ_two,deterministic_weights,ParallelParameters.rootLaw_mass,
    Fin.prod_univ_two,ParallelParameters.valueProbability,deterministic,stateEquiv,
    Matrix.cons_val_zero,Matrix.cons_val_one,Fin.reduceFinMk,Fin.ext_iff]
  norm_num

theorem deterministic_cost_tight : designCost deterministic.rootLaw deterministic.allocation =
    2*deterministic.rarity := by
  apply le_antisymm deterministic.allocation_cost_le
  have h := secondMoment_le_designCost deterministic.rootLaw deterministic.allocation (some (0,true))
  rw [deterministic_rare_secondMoment] at h
  norm_num only [two_node_rarity, Nat.cast_ofNat] at ⊢
  exact h

theorem deterministic_observation_not_covering :
    ¬ Covers deterministic.rootLaw (deterministic.rootLaw none) := by
  intro h
  have hx := h (some (0,true)) ![true,false]
  simp only [ParallelParameters.rootLaw_mass,Fin.prod_univ_two,
    ParallelParameters.valueProbability,deterministic,Matrix.cons_val_zero,Matrix.cons_val_one,Fin.reduceFinMk,
    Fin.ext_iff] at hx
  norm_num at hx

local instance : LinearOrder (Option (Fin 2 × Bool)) :=
  LinearOrder.lift' (Fintype.equivFin _) (Fintype.equivFin _).injective
local instance : MeasurableSpace (Option (Fin 2 × Bool)) := ⊤
local instance : MeasurableSingletonClass (Option (Fin 2 × Bool)) := ⟨fun _ => trivial⟩

def noisyReward (x : Fin 2 → Bool) : PMF Bool :=
  PMF.bernoulli (if x 0 || x 1 then 3/4 else 1/4) (by split_ifs <;> norm_num [div_le_iff₀])

theorem fair_actual_rate (T : ℕ) (hT : 0 < T) :
    let L := sourceLog T 5
    let B := sourceThreshold 2 T L
    (∫ w, (fair.graph noisyReward).simpleRegret id ParallelParameters.graphAction
      fair.allocation (Fin.last 2) B w
      ∂(fair.graph noisyReward).sampleLaw ParallelParameters.graphAction fair.allocation T) ≤
      (2*Real.sqrt 2+7)*Real.sqrt (4*L/T)+1/(T:ℝ) := by
  have h := fair.expected_simpleRegret_parallel noisyReward T hT
  dsimp only at h ⊢
  norm_num only [fair_cost,two_node_rarity,Fintype.card_option,Fintype.card_prod,
    Fintype.card_fin,Fintype.card_bool,Nat.cast_ofNat] at h
  exact h

theorem deterministic_actual_rate (T : ℕ) (hT : 0 < T) :
    let L := sourceLog T 5
    let B := sourceThreshold 4 T L
    (∫ w, (deterministic.graph noisyReward).simpleRegret id ParallelParameters.graphAction
      deterministic.allocation (Fin.last 2) B w
      ∂(deterministic.graph noisyReward).sampleLaw ParallelParameters.graphAction deterministic.allocation T) ≤
      (2*Real.sqrt 2+7)*Real.sqrt (4*L/T)+1/(T:ℝ) := by
  have h := deterministic.expected_simpleRegret_parallel noisyReward T hT
  dsimp only at h ⊢
  norm_num only [deterministic_cost_tight,two_node_rarity,Fintype.card_option,Fintype.card_prod,
    Fintype.card_fin,Fintype.card_bool,Nat.cast_ofNat] at h
  exact h

#print axioms fair_cost
#print axioms deterministic_cost_tight
#print axioms deterministic_observation_not_covering
#print axioms fair_actual_rate
#print axioms deterministic_actual_rate
#print axioms ParallelParameters.expected_simpleRegret_parallel_optimal

end
end Tests.CausalParallelCanary
```

</details>
