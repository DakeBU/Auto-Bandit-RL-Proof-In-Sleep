# Pre-proof exact accounting bridge amendment
Before adding proof code, freeze these exact signatures in QuantumQueryAccounting:
def expandedAction {K D : ℕ} (blocks : List (Block K D)) (fallback : Fin K) : ActionTrace (Fin K) := fun t => (expanded blocks).getD t fallback
 theorem chargedRegret_eq_realMeanRegret {K D : ℕ} (mean : Fin K → ℝ) (blocks : List (Block K D)) (fallback : Fin K) : chargedRegret mean blocks = realMeanRegret mean (expandedAction blocks fallback) (expanded blocks).length
 theorem chargedRegret_eq_gap_pullCount {K D : ℕ} (mean : Fin K → ℝ) (blocks : List (Block K D)) (fallback : Fin K) : chargedRegret mean blocks = ∑ i : Fin K, realMeanGap mean i * (pullCount (expandedAction blocks fallback) i (expanded blocks).length : ℝ)
Literal chronological list expansion. Fallback is an explicit arbitrary arm used strictly beyond consumed query horizon, never a substitute observation. No clipping or reset process here. SOURCE counters and arm for list accounting; actual query-word adapter supplies counters separately. RULED gap sum equals existing real mean regret then existing pull count decomposition. No confidence, nonempty typeclass or probability hypothesis added.
