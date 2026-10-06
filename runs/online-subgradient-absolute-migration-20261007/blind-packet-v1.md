Restricted neutral decoder packet. Requested GPT-6 Astra / medium. Read ONLY this packet, no source identity, proofs, repository searches, prior verdicts or other current files. Write ONLY blind-reconstruction-v1.md and blind-receipt-v1.json in this run; receipt binds raw packet/report SHA and honest restricted input/history limits. Seven semantic slots for ALL FOUR exact targets. Distinct decoder actor; no source/package/Goal/human/external/runtime-model certification.

Neutral context: scalar ℝ with intrinsic real inner product; real values embed in EReal. S below is a GLOBAL predicate testing every ambient point and can accept arbitrary EReal functions. Actual four targets use a fixed function y↦coe(|y|), finite everywhere. There are no additional E/FiniteDimensional/CompleteSpace parameters or convexity/differentiability/domain qualifications in their actual signatures. All constants are exact; real Icc is inclusive, singleton equality characterizes every element. Deterministic static assertion.

Complete borrowed support definition (not new local owned definition):
```lean
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
def S (f : E → EReal) (x : E) : Set E :=
  {g | ∀ y, f x + (inner ℝ g (y - x) : EReal) ≤ f y}
```

Exact neutral headers:
```lean
theorem N01 : S (fun y : ℝ => ((|y| : ℝ) : EReal)) 0 = Icc (-1 : ℝ) 1

theorem N02 (x : ℝ) (hx : 0 < x) : S (fun y : ℝ => ((|y| : ℝ) : EReal)) x = {(1 : ℝ)}

theorem N03 (x : ℝ) (hx : x < 0) : S (fun y : ℝ => ((|y| : ℝ) : EReal)) x = {(-1 : ℝ)}

theorem N04 (x : ℝ) : S (fun y : ℝ => ((|y| : ℝ) : EReal)) x = if 0 < x then {(1 : ℝ)} else if x = 0 then Icc (-1 : ℝ) 1 else {(-1 : ℝ)}
```

Actual neutral types:
```text
N01 : S (fun y => ↑|y|) 0 =
  Set.Icc (-1) 1
N02 : ∀ (x : ℝ),
  0 < x → S (fun y => ↑|y|) x = {1}
N03 : ∀ x < 0,
  S (fun y => ↑|y|) x = {-1}
N04 : ∀ (x : ℝ),
  S (fun y => ↑|y|) x =
    if 0 < x then {1} else if x = 0 then Set.Icc (-1) 1 else {-1}

```

Reconstruct allx terminal and sign leaves, necessity AND sufficiency for every slope, full zero interval and closed endpoints, nested conditional's final branch, exact allambient support test. Do any statements choose only one slope or assume a supporting inequality? Do not infer algorithms, differentiability at zero, a multidimensional norm result, probability, measurable/computable selection or chapter coverage. Describe generic S versus the fixed finite function without identifying a source.
