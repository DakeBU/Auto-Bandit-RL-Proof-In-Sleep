import BanditRLProof.OnlineGuessingIIDBenchmark

open MeasureTheory ProbabilityTheory
universe u v w z

namespace BanditRL.OnlineLearning

/-- Information available before round t: one private tape and strict-past targets. -/
def privateSeedPastInformation {Ω : Type u} {Σ : Type v} [MeasurableSpace Σ]
    (S : Ω → Σ) (Y : ℕ → Ω → ℝ) (t : ℕ) : MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω => (S ω, fun i : (↑(Finset.range t) : Type) => Y i ω))
    inferInstance

end BanditRL.OnlineLearning
