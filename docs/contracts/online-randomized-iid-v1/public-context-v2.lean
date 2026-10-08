import BanditRLProof.OnlineGuessingIIDBenchmark

open MeasureTheory ProbabilityTheory
universe u v w z

namespace BanditRL.OnlineLearning

/-- Information available before round t: one private tape and strict-past targets. -/
def privateSeedPastInformation {Ω : Type u} {Seed : Type v} [MeasurableSpace Seed]
    (S : Ω → Seed) (Y : ℕ → Ω → ℝ) (t : ℕ) : MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω => (S ω, fun i : (↑(Finset.range t) : Type) => Y i ω))
    inferInstance

end BanditRL.OnlineLearning
