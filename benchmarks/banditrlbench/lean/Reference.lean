import BanditRLProof.RealMeanRegretPullCount
import BanditRLProof.ConcentrationConfidenceSchedule

namespace BanditRLBench
-- Two library-application references; not novel proof-synthesis benchmarks.
theorem BRB_001 {K : Nat} (mean : Fin K → ℝ)
    (action : BanditRLProof.ActionTrace (Fin K)) (n : Nat) :
    BanditRLProof.realMeanRegret mean action n =
      ∑ a : Fin K, BanditRLProof.realMeanGap mean a *
        (BanditRLProof.pullCount action a n : ℝ) := by
  exact BanditRLProof.realMeanRegret_eq_sum_gap_mul_pullCount mean action n

-- The formal target is the deterministic schedule only, not the whole NL argument.
theorem BRB_003 {delta : ℝ} (h : 0 ≤ delta) :
    ∑' n, ENNReal.ofReal (BanditRLProof.Concentration.geometricConfidenceShare delta n) =
      ENNReal.ofReal delta := by
  exact BanditRLProof.Concentration.tsum_ofReal_geometricConfidenceShare h
end BanditRLBench

#print axioms BanditRLBench.BRB_001
#print axioms BanditRLBench.BRB_003
