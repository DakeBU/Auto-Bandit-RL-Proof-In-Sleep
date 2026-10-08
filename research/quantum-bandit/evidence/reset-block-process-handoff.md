# ResetBlockProcess pre-proof amendment / handoff

Before proof search (2026-10-09), exact support consumer is frozen as:

```lean
theorem historyLaw_length_support {K D : ℕ}
    (policy : List ι → Plan K D ι)
    (oracle : Fin K → Matrix.unitaryGroup ι ℂ)
    (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) (n : ℕ) :
    ∀ h ∈ (historyLaw policy oracle ψ hψ n).support, h.length = n
```

The definition signatures are unchanged from `ResetProcessSeal.md`. Additional
literal mass-access theorem signatures are also frozen before search:

```lean
theorem basisPMF_apply (x : EuclideanSpace ℂ ι) (hx : ‖x‖ = 1) (j : ι) :
    basisPMF x hx j = ENNReal.ofReal (BasisHellinger.basisProbability x j)
theorem blockPMF_apply {K D : ℕ} (plan : Plan K D ι)
    (oracle : Fin K → Matrix.unitaryGroup ι ℂ)
    (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) (j : ι) :
    blockPMF plan oracle ψ hψ j = ENNReal.ofReal
      (BasisHellinger.basisProbability
        (BasisHellinger.wordOutput plan.word (oracle plan.arm) ψ) j)
```

All above are in namespace `QuantumBlockEncoding.ResetBlockProcess`, with
`{ι : Type*} [Fintype ι] [DecidableEq ι]`. No new assumptions, no claim of arbitrary
POVM or estimator realization. This is the `FC-WO-reset-basis-v1` refinement.
Each step samples the actual computational-basis law of a chronological same-arm
word on the same freshly supplied normalized ψ; only history list is carried.

Proof/build results and residual frontier will be appended after validation.

Before proof code for the parent's optional query-accounting extension, these
additional exact signatures are frozen (no signature above changes):

```lean
def historyQueryCost {K D : ℕ} (policy : List ι → Plan K D ι) (h : List ι) : ℕ :=
  (Finset.range h.length).sum
    (fun t => QuantumQueryWord.queryCount (policy (h.take t)).word)
theorem historyQueryCost_le {K D : ℕ} (policy : List ι → Plan K D ι) (h : List ι) :
    historyQueryCost policy h ≤ h.length * D
theorem historyLaw_queryCost_le {K D : ℕ}
    (policy : List ι → Plan K D ι)
    (oracle : Fin K → Matrix.unitaryGroup ι ℂ)
    (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) (n : ℕ) :
    ∀ h ∈ (historyLaw policy oracle ψ hψ n).support,
      historyQueryCost policy h ≤ n * D
theorem historyLaw_queryCost_le_budget {K D : ℕ}
    (policy : List ι → Plan K D ι)
    (oracle : Fin K → Matrix.unitaryGroup ι ℂ)
    (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) (n : ℕ)
    {T : ℕ} (hT : n * D ≤ T) :
    ∀ h ∈ (historyLaw policy oracle ψ hψ n).support,
      historyQueryCost policy h ≤ T
```

This is exact classical prefix accounting for fixed n blocks; the supplied
`n*D≤T` is only a total-budget comparison. It introduces no stopping or clipping
procedure and assumes no supported-history length or query-normalization premise.
