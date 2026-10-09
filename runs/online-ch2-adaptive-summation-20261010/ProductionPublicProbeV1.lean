import BanditRLProof.OnlineAdaptiveSummation

open Set Finset MeasureTheory

#check BanditRL.OnlineAdaptiveSummation.lemma_4_13
example : ∀ (a₀ : ℝ) (a : ℕ → ℝ) (f : ℝ → ℝ) (T : ℕ),
    0 ≤ a₀ → (∀ t < T, 0 ≤ a t) →
    ContinuousOn f (Set.Ici 0) → AntitoneOn f (Set.Ici 0) →
    (∀ x ∈ Set.Ici 0, 0 ≤ f x) →
    (∑ t ∈ range T, a t * f (a₀ + ∑ i ∈ range (t + 1), a i)) ≤
      ∫ x in a₀..(a₀ + ∑ i ∈ range T, a i), f x := BanditRL.OnlineAdaptiveSummation.lemma_4_13
#print axioms BanditRL.OnlineAdaptiveSummation.lemma_4_13
#print BanditRL.OnlineAdaptiveSummation.lemma_4_13
