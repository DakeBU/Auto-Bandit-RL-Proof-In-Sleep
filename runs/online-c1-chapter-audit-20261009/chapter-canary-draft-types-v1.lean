import BanditRLProof.OnlineFTLInitializationRegret
import Tests.OnlineLearningChapterOneCanary
import Tests.OnlineLearningRegretDomainsCanary
import Tests.OnlineSquareMinimumCanary
import Tests.OnlineGuessingIIDSuccessCanary
import Tests.OnlineGuessingKernelCausalCanary
import Tests.OnlineFTLOscillationCanary
import Tests.OnlineGuessingLogLowerCanary

noncomputable section
open Filter Asymptotics MeasureTheory ProbabilityTheory BanditRL.OnlineLearning
open scoped ENNReal
open Tests.OnlineGuessingIIDBenchmark
namespace Tests.OnlineLearningChapterAudit

def rising (t : ℕ) : ℝ := if t = 0 then 0 else 1
def falling (t : ℕ) : ℝ := if t = 0 then 1 else 0

#check (squaredBestRegret (fun _ => (1 : ℝ)) (ftlPredict 0 (fun _ => 1)) 1 = 1 ∧
      squaredBestRegret (fun _ => (1 : ℝ)) (ftlPredict 0 (fun _ => 1)) 1 > (1 : ℝ) / 4 : Prop)
#check (squaredBestRegret falling (ftlPredict 0 falling) 2 =
      squaredBestRegret falling (meanPredict falling) 2 + (3 : ℝ) / 4 : Prop)
#check (squaredBestRegret rising (ftlPredict 0 rising) 2 = (1 : ℝ) / 2 ∧
      squaredBestRegret rising (meanPredict rising) 2 = (3 : ℝ) / 4 ∧
      ((0 - rising 0)^2 - ((1 : ℝ) / 2 - rising 0)^2) = -(1 : ℝ) / 4 : Prop)
#check (squaredBestRegret falling (ftlPredict 0 falling) 2 = (3 : ℝ) / 2 ∧
      squaredBestRegret falling (ftlPredict 0 falling) 2 ≤ (3 : ℝ) ∧
      squaredBestRegret (fun _ => (1 : ℝ)) (ftlPredict 0 (fun _ => 1)) 1 ≤ 1 : Prop)
#check (ftlState 0 rising 1 = ftlState 0 (fun _ => 0) 1 ∧
      rising 1 ≠ (0 : ℝ) ∧ ftlState 0 rising 2 ≠ ftlState 0 (fun _ => 0) 2 : Prop)
#check (ftlState ((3 : ℝ) / 4) rising 0 = (0, (3 : ℝ) / 4) ∧
      ftlState ((3 : ℝ) / 4) rising 1 = (1, 0) ∧
      ftlState ((3 : ℝ) / 4) rising 2 = (2, (1 : ℝ) / 2) : Prop)
#check (∀ initial ∈ Set.Icc (0 : ℝ) 1,
      NoRegret (Set.Icc (0 : ℝ) 1) (fun t x => (x - dyadicObservation t)^2)
        (ftlPredict initial dyadicObservation) : Prop)
#check (Tendsto (fun T : ℕ => squaredBestRegret dyadicObservation
      (ftlPredict ((3 : ℝ) / 4) dyadicObservation) T / (T : ℝ)) atTop (nhds (0 : ℝ)) : Prop)
#check (squaredBestRegret (fun _ => (3 : ℝ)) (ftlPredict 2 (fun _ => 3)) 1 =
      squaredBestRegret (fun _ => (3 : ℝ)) (meanPredict (fun _ => 3)) 1 - (21 : ℝ) / 4 : Prop)
#check (squaredBestRegret falling (ftlPredict 0 falling) 0 = 0 ∧
      squaredBestRegret falling (meanPredict falling) 0 = 0 ∧
      ((0 - falling 0)^2 - ((1 : ℝ) / 2 - falling 0)^2) = (3 : ℝ) / 4 : Prop)
#check (comparatorRegret (fun t x => (x - falling t)^2) (ftlPredict 0 falling) 0 2 = 1 ∧
      squaredBestRegret falling (ftlPredict 0 falling) 2 = (3 : ℝ) / 2 : Prop)
#check (variance (observation 0) iidLaw = (1 : ℝ) / 4 ∧
      expectedFixedRegret iidLaw observation (fun t ω => meanPredict ω t) 2 = (1 : ℝ) / 4 ∧
      expectedFixedRegret iidLaw observation (fun t ω => meanPredict ω t) 2 / (2 : ℝ) = (1 : ℝ) / 8 : Prop)
#check (IsLeast ((fun u : ℝ => ∫ ω, ∑ t ∈ Finset.range 2, (u - observation t ω)^2 ∂iidLaw)
      '' Set.Icc (0 : ℝ) 1) ((1 : ℝ) / 2) ∧
      expectedFixedRegret iidLaw observation (fun _ _ => (1 / 2 : ℝ)) 2 = 0 : Prop)
#check ((∫ ω, hindsightMinimum ω 2 ∂iidLaw) = (1 : ℝ) / 4 ∧
      expectedFixedMinimum iidLaw observation 2 = (1 : ℝ) / 2 : Prop)
#check (Tendsto (fun T => expectedFixedRegret iidLaw observation (fun t ω => meanPredict ω t) T /
      (T : ℝ)) atTop (nhds (0 : ℝ)) ∧
      (fun T => expectedFixedRegret iidLaw observation (fun t ω => meanPredict ω t) T) =o[atTop]
        (fun T : ℕ => (T : ℝ)) : Prop)
#check ((RegretDomainsProbe.output 0).val ∈ RegretDomainsProbe.outputW ∧
      (RegretDomainsProbe.output 0).val ∉ RegretDomainsProbe.sourceV ∧
      comparatorRegret RegretDomainsProbe.domainLoss RegretDomainsProbe.output
        RegretDomainsProbe.referenceOne 2 = -2 ∧
      comparatorRegret (fun t x => 2 * RegretDomainsProbe.domainLoss t x)
        RegretDomainsProbe.output RegretDomainsProbe.referenceOne 2 = -4 : Prop)
#check (empiricalMean rising 2 = (1 : ℝ) / 2 ∧
      sInf ((fun u : ℝ => ∑ t ∈ Finset.range 2, (u - rising t)^2) '' Set.Icc (0 : ℝ) 1) = (1 : ℝ) / 2 ∧
      ∀ u ∈ Set.Icc (0 : ℝ) 1, (∑ t ∈ Finset.range 0, (u - rising t)^2) = 0 : Prop)
#check (∀ u : ℝ,
      (∑ t ∈ Finset.range 2, (u - rising t)^2) ≤
        (∑ t ∈ Finset.range 2, (empiricalMean rising 2 - rising t)^2) → u = (1 : ℝ) / 2 : Prop)
#check ((∑ t ∈ Finset.range 2, ChapterOneCase0.demoLoss t (ChapterOneCase0.demoLeader (t + 1))) = -2 ∧
      (∑ t ∈ Finset.range 2, ChapterOneCase0.demoLoss t (ChapterOneCase0.demoLeader 2)) = 0 ∧
      (∑ t ∈ Finset.range 2, ChapterOneCase0.demoLoss t (ChapterOneCase0.demoLeader (t + 1))) ≤
        ∑ t ∈ Finset.range 2, ChapterOneCase0.demoLoss t (ChapterOneCase0.demoLeader 2) : Prop)
#check (squaredBestRegret rising (meanPredict rising) 2 = (3 : ℝ) / 4 ∧
      squaredBestRegret rising (meanPredict rising) 2 ≤ (9 : ℝ) / 4 ∧
      squaredBestRegret rising (meanPredict rising) 2 ≤ 4 + 4 * Real.log 2 : Prop)
#check ((meanPredict rising 1 - rising 1)^2 - (meanPredict rising 2 - rising 1)^2 = (3 : ℝ) / 4 ∧
      (meanPredict rising 1 - rising 1)^2 - (meanPredict rising 2 - rising 1)^2 ≤ 4 / ((1 : ℝ) + 1) : Prop)
#check ((∀ T : ℕ, expectedFixedRegret Tests.OnlineGuessingKernelCausal.gameLaw
      Tests.OnlineGuessingKernelCausal.target
      (fun t ω => (Tests.OnlineGuessingKernelCausal.prediction t ω : ℝ)) T = (T : ℝ) / 4) ∧
      Tests.OnlineGuessingKernelCausal.decisionKernel 1 (Tests.OnlineGuessingKernelCausal.oneHistory 0 1) {1} = (1 / 4 : ℝ≥0∞) ∧
      Tests.OnlineGuessingKernelCausal.decisionKernel 1 (Tests.OnlineGuessingKernelCausal.oneHistory 1 1) {1} = (3 / 4 : ℝ≥0∞) : Prop)
#check (expectedFixedRegret iidLaw (fun _ => observation 0)
      (fun t ω => meanPredict (fun _ => observation 0 ω) t) 2 = -(1 : ℝ) / 4 ∧
      expectedFixedRegret iidLaw observation (fun t ω => meanPredict ω t) 2 = (1 : ℝ) / 4 : Prop)
#check (NoRegret (Set.Icc (0 : ℝ) 1) (fun t x => (x - dyadicObservation t)^2) (meanPredict dyadicObservation) ∧
      Tendsto (fun T : ℕ => squaredBestRegret dyadicObservation (meanPredict dyadicObservation) T / (T : ℝ)) atTop (nhds (0 : ℝ)) ∧
      (¬ ∃ a : ℝ, Tendsto (fun T : ℕ => comparatorRegret (fun t x => (x - dyadicObservation t)^2)
        (meanPredict dyadicObservation) 0 T / (T : ℝ)) atTop (nhds a)) ∧
      ¬ LimitNoRegret (Set.Icc (0 : ℝ) 1) (fun t x => (x - dyadicObservation t)^2) (meanPredict dyadicObservation) : Prop)
#check (∃ v : List.Vector Bool 2, Real.log 4 / 6 ≤
      ∫ b, BanditRL.OnlineLearning.GuessingLower.pathRegret (GuessingLogLowerProbe.seededPolicy b) v.toList
        ∂GuessingLogLowerProbe.coinMeasure : Prop)
#check ((harmonic 2 : ℝ) = (3 : ℝ) / 2 ∧ (harmonic 2 : ℝ) ≤ 1 + Real.log 2 : Prop)
#check ((fun T : ℕ => (5 + 3 * (T : ℝ)) - (T : ℝ) * 3) =o[atTop]
      (fun T : ℕ => (T : ℝ)) ∧
      ((5 + 3 * (0 : ℝ)) / (0 : ℝ) - 3) = -(3 : ℝ) : Prop)
end Tests.OnlineLearningChapterAudit
