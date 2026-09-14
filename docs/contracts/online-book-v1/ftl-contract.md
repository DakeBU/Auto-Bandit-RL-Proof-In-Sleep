# Chapter 1 FTL algorithm v1

Source pp3-6, Theorem1.3. Source round t+1 is indexed t in Lean. Prediction at zero is exactly 1/2; all later predictions are the empirical mean of the strict past. The empirical mean after observing the current loss is the auxiliary leader and must not be confused with the actual prediction. Prefix equality ensures no future access.

The update equation requires t>0 since empiricalMean zero is only a bookkeeping convention, not the first prediction. Stability includes round zero by a separate direct bound; positive rounds follow the update equation and interval feasibility. Target is precisely loss at actual prediction minus loss at current leader <=4/(t+1), supplying the source's harmonic bound. No regret or stability certificates may be assumed. These frozen leaves feed Theorem1.3; no Chapter2 proving before the Chapter1 gate.

Terminal theorem_1_3 is the exact 4+4 log T bound for T>0 and observations in [0,1]. Source min is represented by empiricalMean y T, whose feasibility and global minimization were proved in OnlineLearningMean. This conversion is explicit, not a choice of arbitrary comparator that weakens the best-fixed result.
