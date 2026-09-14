# Empirical mean uniqueness v1, source audit repair

Source printed p3 writes the argmin as the empirical mean. Existing decomposition and minimizing inequality show it is a minimizer. The remaining interface states that for positive n, any real u whose cumulative squared loss is no greater than the mean's loss must equal that mean. This implies uniqueness on [0,1] once mean feasibility is supplied. No boundedness or attainment assumption is needed beyond that comparison.

Frozen intended Lean header (native fence to be captured before implementation):

    theorem empiricalMean_unique (y : Nat -> Real) (n : Nat) (hn : 0 < n) (u : Real)
      (hu : (sum t in range n, (u-y t)^2) <=
            (sum t in range n, (empiricalMean y n-y t)^2)) :
      u = empiricalMean y n

DAG: empiricalMean_decomposition -> n*(u-mean)^2 <=0 -> square zero -> equality. Proof may not assume uniqueness or change the old decomposition. Add to the existing mean module after current full-gate process terminates, then rerun impacted Lean and chapter checks. No prior passing gate can verify this not-yet-written theorem.
