# Source-blind exact propositions
Read ONLY this packet. GPT-6 Astra/medium, no escalation/runtime attestation. Reused actor prior history must be disclosed. Reconstruct EVERY N01-N13 in natural language AND LaTeX; seven semantic slots for EACH: objects, quantifiers, assumptions, conclusion, constants/indices, probability/feedback/information, boundary. a is empty-prefix mean0 but b at0 is1/2, they differ. c is explicit test target sequence. Do not look up source identity, original aliases, theorem bodies or verdicts. Distinguish universal hypotheses, closed numerical tests and prefix agreement. No source/proof acceptance verdict. Write ONLY blind-decoder-v1.md and blind-decoder-receipt-v1.json in this RUN; receipt actor.task=/root/osd_blind; input/report nested path/sha256_raw_bytes, proposition_ids N01-N13, semantic_slots_per_proposition7, prior_history_disclosure; requested_model GPT-6 Astra/requested_reasoning_effort medium/runtime_model_attested false.
```lean
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic
namespace Neutral
noncomputable def a (y : ℕ → ℝ) (n : ℕ) : ℝ := (∑ t ∈ Finset.range n, y t) / n
noncomputable def b (y : ℕ → ℝ) (t : ℕ) : ℝ := if t = 0 then 1/2 else a y t
def c (t : ℕ) : ℝ := if t = 0 then 0 else 1
def N01 : Prop :=
    ∀ (y z : ℕ → ℝ) (t : ℕ) (h : ∀ i < t, y i = z i),
    b y t = b z t

def N02 : Prop :=
    ∀ (y : ℕ → ℝ) (t : ℕ)
    (hy : ∀ i < t, y i ∈ Set.Icc (0 : ℝ) 1),
    b y t ∈ Set.Icc (0 : ℝ) 1

def N03 : Prop :=
    ∀ (y : ℕ → ℝ) (t : ℕ) (ht : 0 < t),
    a y (t+1) = a y t +
      (y t - a y t) / (t+1)

def N04 : Prop :=
    ∀ (y : ℕ → ℝ) (t : ℕ)
    (hy : ∀ i ≤ t, y i ∈ Set.Icc (0 : ℝ) 1),
    (b y t - y t)^2 - (a y (t+1) - y t)^2 ≤
      4 / (t+1)

def N05 : Prop :=
    ∀ (y : ℕ → ℝ) (T : ℕ) (hT : 0 < T)
    (hy : ∀ t < T, y t ∈ Set.Icc (0 : ℝ) 1),
    (∑ t ∈ Finset.range T, (b y t - y t)^2) -
      (∑ t ∈ Finset.range T, (a y T - y t)^2) ≤
        4 + 4 * Real.log T

def N06 : Prop :=
    ∀ (y : ℕ → ℝ)
    (hy : y 0 ∈ Set.Icc (0 : ℝ) 1),
    (b y 0 - y 0)^2 - (a y 1 - y 0)^2 ≤ (1 : ℝ) / 4

def N07 : Prop :=
    ∀ (y : ℕ → ℝ) (T : ℕ) (hT : 0 < T)
    (hy : ∀ t < T, y t ∈ Set.Icc (0 : ℝ) 1),
    (∑ t ∈ Finset.range T, (b y t - y t)^2) -
      (∑ t ∈ Finset.range T, (a y T - y t)^2) ≤
        (1 : ℝ) / 4 + ∑ t ∈ Finset.range (T - 1), 4 / ((t : ℝ) + 2)

def N08 : Prop :=
    (b (fun _ => 0) 0 - 0)^2 - (a (fun _ => 0) 1 - 0)^2 = (1 : ℝ) / 4 ∧
    (b (fun _ => 1) 0 - 1)^2 - (a (fun _ => 1) 1 - 1)^2 = (1 : ℝ) / 4 ∧
    (b (fun _ => 0) 0 - 0)^2 - (a (fun _ => 0) 1 - 0)^2 ≤ (1 : ℝ) / 4 ∧
    (b (fun _ => 1) 0 - 1)^2 - (a (fun _ => 1) 1 - 1)^2 ≤ (1 : ℝ) / 4

def N09 : Prop :=
    (b (fun _ => (1 : ℝ) / 2) 0 - 1 / 2)^2 -
      (a (fun _ => (1 : ℝ) / 2) 1 - 1 / 2)^2 = 0 ∧
    (b (fun _ => (1 : ℝ) / 2) 0 - 1 / 2)^2 -
      (a (fun _ => (1 : ℝ) / 2) 1 - 1 / 2)^2 < (1 : ℝ) / 4

def N10 : Prop :=
    (b (fun _ => 2) 0 - 2)^2 - (a (fun _ => 2) 1 - 2)^2 = (9 : ℝ) / 4 ∧
    (b (fun _ => 2) 0 - 2)^2 - (a (fun _ => 2) 1 - 2)^2 > (1 : ℝ) / 4

def N11 : Prop :=
    ((∑ t ∈ Finset.range 1, (b (fun _ => 0) t - 0)^2) -
      (∑ t ∈ Finset.range 1, (a (fun _ => 0) 1 - 0)^2) = (1 : ℝ) / 4) ∧
    ((∑ t ∈ Finset.range 1, (b (fun _ => 0) t - 0)^2) -
      (∑ t ∈ Finset.range 1, (a (fun _ => 0) 1 - 0)^2) ≤
        (1 : ℝ) / 4 + ∑ t ∈ Finset.range (1 - 1), 4 / ((t : ℝ) + 2))

def N12 : Prop :=
    ((∑ t ∈ Finset.range 2, (b c t - c t)^2) -
      (∑ t ∈ Finset.range 2, (a c 2 - c t)^2) = (3 : ℝ) / 4) ∧
    ((∑ t ∈ Finset.range 2, (b c t - c t)^2) -
      (∑ t ∈ Finset.range 2, (a c 2 - c t)^2) ≤
        (1 : ℝ) / 4 + ∑ t ∈ Finset.range (2 - 1), 4 / ((t : ℝ) + 2)) ∧
    ((1 : ℝ) / 4 + ∑ t ∈ Finset.range (2 - 1), 4 / ((t : ℝ) + 2)) = 9 / 4

def N13 : Prop :=
    b (fun _ => 0) 1 = b c 1 ∧
    (0 : ℝ) ≠ c 1
#check N01
#check N02
#check N03
#check N04
#check N05
#check N06
#check N07
#check N08
#check N09
#check N10
#check N11
#check N12
#check N13
#check Finset.sum_range_succ'
end Neutral

```
