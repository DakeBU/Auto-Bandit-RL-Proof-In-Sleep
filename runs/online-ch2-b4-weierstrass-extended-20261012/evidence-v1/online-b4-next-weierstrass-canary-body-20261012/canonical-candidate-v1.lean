import BanditRLProof.OnlineWeierstrassExtended
import BanditRLProof.OnlineClosedProper

open Set
namespace BanditRL.Tests.OnlineWeierstrassExtendedCanary
open BanditRL.OnlineConvex

def objective (_ : ℝ) : EReal := ⊥
def feasible : Set ℝ := {0}

theorem bottom_singleton_attains :
    (∃ p ∈ feasible, IsMinOn objective feasible p) ∧
    LowerSemicontinuous objective ∧
    IsCompact feasible ∧
    (feasible ∩ effectiveDomain objective).Nonempty ∧
    objective 0 = ⊥ ∧
    ¬ SourceProper objective := by
  have hlsc : LowerSemicontinuous objective := lowerSemicontinuous_const
  have hcompact : IsCompact feasible := isCompact_singleton
  have hdom : (feasible ∩ effectiveDomain objective).Nonempty := by
    refine ⟨0, ?_, ?_⟩
    · simp [feasible]
    · simp [effectiveDomain, objective]
  have hmin := source_weierstrass_extended objective feasible hlsc hcompact hdom
  refine ⟨hmin, hlsc, hcompact, hdom, rfl, ?_⟩
  intro hproper
  exact (hproper.1 0) rfl

end BanditRL.Tests.OnlineWeierstrassExtendedCanary
