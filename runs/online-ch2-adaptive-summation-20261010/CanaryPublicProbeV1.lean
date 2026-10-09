import Tests.OnlineAdaptiveSummationCanary

open Set Finset MeasureTheory

#check Tests.OnlineAdaptiveSummationCanary.nonconstant_zero_increment_canary
example : (    (∑ t ∈ range 3, (fun t : ℕ => if t = 1 then (0 : ℝ) else 1 / 2) t * (fun x : ℝ => max (1 - x) 0) (0 + ∑ i ∈ range (t + 1), (fun t : ℕ => if t = 1 then (0 : ℝ) else 1 / 2) i)) ≤ (∫ x in (0 : ℝ)..(0 + ∑ i ∈ range 3, (fun t : ℕ => if t = 1 then (0 : ℝ) else 1 / 2) i), (fun x : ℝ => max (1 - x) 0) x) ∧
    (∑ t ∈ range 3, (fun t : ℕ => if t = 1 then (0 : ℝ) else 1 / 2) t * (fun x : ℝ => max (1 - x) 0) (0 + ∑ i ∈ range (t + 1), (fun t : ℕ => if t = 1 then (0 : ℝ) else 1 / 2) i)) = 1 / 4 ∧
    (∫ x in (0 : ℝ)..(0 + ∑ i ∈ range 3, (fun t : ℕ => if t = 1 then (0 : ℝ) else 1 / 2) i), (fun x : ℝ => max (1 - x) 0) x) = 1 / 2 ∧
    (∑ t ∈ range 3, (fun t : ℕ => if t = 1 then (0 : ℝ) else 1 / 2) t * (fun x : ℝ => max (1 - x) 0) (0 + ∑ i ∈ range (t + 1), (fun t : ℕ => if t = 1 then (0 : ℝ) else 1 / 2) i)) < (∫ x in (0 : ℝ)..(0 + ∑ i ∈ range 3, (fun t : ℕ => if t = 1 then (0 : ℝ) else 1 / 2) i), (fun x : ℝ => max (1 - x) 0) x) ∧
    (fun x : ℝ => max (1 - x) 0) 0 ≠ (fun x : ℝ => max (1 - x) 0) 1 ∧
    (fun t : ℕ => if t = 1 then (0 : ℝ) else 1 / 2) 0 = 1 / 2 ∧ (fun t : ℕ => if t = 1 then (0 : ℝ) else 1 / 2) 1 = 0 ∧ (fun t : ℕ => if t = 1 then (0 : ℝ) else 1 / 2) 2 = 1 / 2) := Tests.OnlineAdaptiveSummationCanary.nonconstant_zero_increment_canary
#print axioms Tests.OnlineAdaptiveSummationCanary.nonconstant_zero_increment_canary
#check Tests.OnlineAdaptiveSummationCanary.zero_boundaries_canary
example : (    (∑ t ∈ range 0, (1 : ℝ) * (fun x : ℝ => max (3 - x) 0) (2 + ∑ _i ∈ range (t + 1), (1 : ℝ))) ≤
      (∫ x in (2 : ℝ)..(2 + ∑ _i ∈ range 0, (1 : ℝ)), (fun x : ℝ => max (3 - x) 0) x) ∧
    (∑ t ∈ range 3, (0 : ℝ) * (fun x : ℝ => max (3 - x) 0) (2 + ∑ _i ∈ range (t + 1), (0 : ℝ))) ≤
      (∫ x in (2 : ℝ)..(2 + ∑ _i ∈ range 3, (0 : ℝ)), (fun x : ℝ => max (3 - x) 0) x) ∧
    (fun x : ℝ => max (3 - x) 0) 2 = 1) := Tests.OnlineAdaptiveSummationCanary.zero_boundaries_canary
#print axioms Tests.OnlineAdaptiveSummationCanary.zero_boundaries_canary
