# Chapter 1 empirical mean v1

Source printed p3: x-star_T = sum y / T minimizes squared loss over [0,1]. Require positive horizon; observations in [0,1] for feasibility only. Decomposition and minimization hold for arbitrary real observations and comparator. No future information is claimed: this is the hindsight leader; actual predictor will use the strict past and initial 1/2.

DAG: sum expansion -> exact decomposition -> nonnegative squared residual -> minimization. Sum bounds -> interval membership. These interfaces supply hmem and hmin to Lemma1.2, hence are necessary dependencies of Theorem1.3. Definitions/imports frozen with the leaf headers before proof. Edit window is OnlineLearningMean.lean plus evidence; original Lemma1.2 file and prefix are unchanged.
