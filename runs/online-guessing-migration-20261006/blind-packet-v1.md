Required restricted reconstruction, requested GPT-6 Astra/medium. Read ONLY this packet in this pass, no other source/numbered original names/prior verdicts/proof bodies or imports browsing. No compilation, no source lookup, history not erased. Reconstruct N01–N12 in seven semantic slots/natural language/formulas, separate N01–N09 existing statements from N10–N12 planned type expressions (no new body exists). Write ONLY blind-reconstruction-v1.md/blind-receipt-v1.json here, sole packet/report SHA/actor/reading boundary. Actual definitions below are supplied notation, not decoder-inspected original bodies.

All scalar quantities use real arithmetic; time/horizon/n/N are natural, real casts explicit, real division is total with zero inverse zero. A Domain is a nonempty closed convex subset of real Hilbert space. unitInterval carrier is Icc0,1 with proved nonempty/closed/convex fields. project(V,z) chooses the actual nearest point using existence of an exact distance minimizer; it is not a freely supplied clamp map. RegularLoss(V,f) means exists open U containing V.carrier with ConvexOn real U f and DifferentiableOn real f U. gradient is the actual ambient Fréchet real-Hilbert gradient. step(V,eta,f,x)=project(V,x-eta*gradient(f,x)). iterate(V,eta,loss,x0,0)=x0; iterate(...,t+1)=step(V,eta,loss(t),iterate(...,t)). regret(V,eta,loss,x0,u,T)=sum t<T [loss(t,iterate(...,t))-loss(t,u)]. empiricalMean(y,t)=(sum i<t y(i))/t; meanPredict(y,t)=if t=0 then1/2 else empiricalMean(y,t). These causal scalar definitions use the strict prefix to predict before the current label. No stochastic law/expectation/filtration assumed; C any real threshold, N any natural index lower bound. No inference of every initialization/all algorithm lower bounds or printed attribution from these neutral statements.

```lean
open Set Finset BanditRL.OnlineGradientDescent
theorem N01 (z : ℝ) : project unitInterval z = min (max z 0) 1

theorem N02 (y : ℝ) : RegularLoss unitInterval (fun x : ℝ => (x-y)^2)

theorem N03 (y x : ℝ) : gradient (fun x : ℝ => (x-y)^2) x = 2 * (x-y)

theorem N04 (y x : ℝ) (hy : y ∈ Icc (0 : ℝ) 1) (hx : x ∈ Icc (0 : ℝ) 1) : ‖gradient (fun x : ℝ => (x-y)^2) x‖ ≤ 2

theorem N05 (η y x : ℝ) : step unitInterval η (fun x : ℝ => (x-y)^2) x = min (max (x - 2 * η * (x-y)) 0) 1

theorem N06 (y : ℕ → ℝ) (x0 : ℝ) (hx0 : x0 ∈ Icc (0 : ℝ) 1) (T : ℕ) (hT : 0 < T) (hy : ∀ t < T, y t ∈ Icc (0 : ℝ) 1) : ∀ u ∈ Icc (0 : ℝ) 1, regret unitInterval (1 / (2 * Real.sqrt T)) (fun t x => (x-y t)^2) x0 u T ≤ 2 * Real.sqrt T

theorem N07 (n : ℕ) (hn : 0 < n) (t : ℕ) : iterate unitInterval (1/(4*(n:ℝ))) (fun _ x => (x-0)^2) 1 t = (1 - 1/(2*(n:ℝ)))^t

theorem N08 (n : ℕ) : 1/(2*Real.sqrt (((2*n)^2 : ℕ) : ℝ)) = 1/(4*(n:ℝ))

theorem N09 (n : ℕ) (hn : 0 < n) : (n:ℝ)/4 ≤ regret unitInterval (1/(2*Real.sqrt (((2*n)^2 : ℕ) : ℝ))) (fun _ x => (x-0)^2) 1 0 ((2*n)^2)

theorem N10 (T : ℕ) (hT : 0 < T) :
    (∑ t ∈ range T,
      (BanditRL.OnlineLearning.meanPredict (fun _ : ℕ => (0 : ℝ)) t)^2) = 1/4

theorem N11 (n : ℕ) (hn : 0 < n) :
    (n : ℝ)/4 - 1/4 ≤
      regret unitInterval (1/(2*Real.sqrt (((2*n)^2 : ℕ) : ℝ)))
        (fun _ x => (x-0)^2) 1 0 ((2*n)^2) -
      (∑ t ∈ range ((2*n)^2),
        (BanditRL.OnlineLearning.meanPredict (fun _ : ℕ => (0 : ℝ)) t)^2)

theorem N12 (C : ℝ) (N : ℕ) :
    ∃ n : ℕ, N < n ∧
      C < regret unitInterval (1/(2*Real.sqrt (((2*n)^2 : ℕ) : ℝ)))
        (fun _ x => (x-0)^2) 1 0 ((2*n)^2) -
      (∑ t ∈ range ((2*n)^2),
        (BanditRL.OnlineLearning.meanPredict (fun _ : ℕ => (0 : ℝ)) t)^2)

```
