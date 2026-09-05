# MOSS large-gap occupancy route

Source TXT-LATTIMORE-SZEPESVARI-2020, author-online p.126, Theorem 9.1
and Lemma 8.2. Parent TEXTBOOK-PART-IV-CHAPTER-13-BASIC-LOWER-BOUND-SPINE.
Project-local first bridge: for delta>0, gap>0 and s*gap^2>=1,
logPlus(1/(s*delta)) <= logPlus(gap^2/delta). Thus the variable-radius
index exceedance is contained in the fixed-log exceedance. Split the finite
indicator count into s*gap^2<1 and the fixed-log count, pointwise, without
assuming a probability or occupancy bound. APIs: existing MOSS.logPlus_mono,
sqrt_le_sqrt, positive denominator multiplication, finite indicator sums.
No new model assumptions; deterministic leaf. Next: bound the small-count
correction by gap^-2; integrate the fixed-log count using independent centered
unit-subgaussian coordinates and the source Lemma 8.2 constants. Actual
pull-count/history connection remains a separate required node.

Compiled progress: `Algorithms/MOSSOccupancy.lean` proves the radius
comparison, pointwise indicator-count split, and exact small-sample count
bound gap^-2. The resulting source correction inequality is
`indexExceedanceCount <= gap^-2 + fixedLogExceedanceCount`.
Focused module build passed 3508 jobs. No expectation bound for the fixed-log
count or actual selected-arm count is yet claimed. API repairs concerned
explicit sum_range_succ unfolding and inequality addition; route unchanged.

Next source target (Lemma 8.2): for epsilon>0 and a>0,
E[sum_{s=1}^n 1{mean_s+sqrt(2a/s)>=epsilon}]
<= 1 + 2/epsilon^2*(a+sqrt(pi*a)+1).
For MOSS substitute epsilon=gap/2 and a=2*logPlus(gap^2/delta).
The large-gap condition gap>=8*sqrt(delta) ensures the logarithm is positive.
The source final arithmetic is gap*E[kappa] <= gap+15/sqrt(delta).
These numerical/count expectation claims are not yet compiled; the current
proof establishes only the deterministic radius/correction reduction.
