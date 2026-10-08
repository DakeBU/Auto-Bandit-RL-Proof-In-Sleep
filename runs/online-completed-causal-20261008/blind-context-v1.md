Neutral scoped context only; no source title/pages/identity, proof, proposed route or prior verdict. Reused decoder history disclosed; this is a statement-only staged reconstruction, not absolute historical blindness.

```lean
def privateSeedPastInformation {Ω : Type u} {Seed : Type v} [MeasurableSpace Seed]
    (S : Ω → Seed) (Y : ℕ → Ω → ℝ) (t : ℕ) : MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω => (S ω, fun i : (↑(Finset.range t) : Type) => Y i ω))
    inferInstance
```

```lean
noncomputable def expectedFixedMinimum {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Y : ℕ → Ω → ℝ) (T : ℕ) : ℝ :=
  sInf ((fun u : ℝ => ∫ ω, ∑ t ∈ Finset.range T, (u - Y t ω)^2 ∂μ) ''
    Set.Icc (0 : ℝ) 1)

noncomputable def expectedFixedRegret {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Y prediction : ℕ → Ω → ℝ) (T : ℕ) : ℝ :=
  (∫ ω, ∑ t ∈ Finset.range T, (prediction t ω - Y t ω)^2 ∂μ) -
    expectedFixedMinimum μ Y T
```

eventuallyMeasurableSpace F (ae mu) has exactly the sets A with some F-measurable B and A =^ae(mu) B. Measurable[F] means measurability for the explicitly supplied sigma field; mu keeps its ambient sigma field. Natural time0 has empty Finset.range0 history. Reconstruct all four full types and seven semantic slots, quantifier order, assumptions and degeneracies. Do not prove them or issue source acceptance. Write only blind-reconstruction-v1.md and blind-receipt-v1.json with exact input RAW before/after/reportSHA, actual reconstructed count and ambiguities.
