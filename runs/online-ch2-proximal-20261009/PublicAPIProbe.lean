import BanditRLProof.OnlineProximalComparison
open Set
namespace OnlineProximalAudit
theorem public_value {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : Set E) (f h : E → ℝ) (p : E) (hp : p ∈ V)
    (hf : ConvexOn ℝ V f) (hmin : IsMinOn (fun z => f z + h z) V p)
    (h' : E →L[ℝ] ℝ) (hd : HasFDerivAt h h' p) :
    ∀ u ∈ V, f p - f u ≤ h' (u - p) :=
  BanditRL.OnlineProximal.convex_minimizer_comparison V f h p hp hf hmin h' hd
#check BanditRL.OnlineProximal.convex_minimizer_comparison
#print BanditRL.OnlineProximal.convex_minimizer_comparison
#print axioms BanditRL.OnlineProximal.convex_minimizer_comparison
#print axioms public_value
end OnlineProximalAudit
