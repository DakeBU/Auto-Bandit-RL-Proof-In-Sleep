import WeierstrassExtendedCandidate
import BanditRLProof.OnlineClosedProper

open Set
namespace BanditRL.Tests.OnlineWeierstrassExtendedCanary
open BanditRL.OnlineConvex

def objective (_ : ℝ) : EReal := ⊥
def feasible : Set ℝ := {0}

#check
    (∃ p ∈ feasible, IsMinOn objective feasible p) ∧
    LowerSemicontinuous objective ∧
    IsCompact feasible ∧
    (feasible ∩ effectiveDomain objective).Nonempty ∧
    objective 0 = ⊥ ∧
    ¬ SourceProper objective

end BanditRL.Tests.OnlineWeierstrassExtendedCanary
