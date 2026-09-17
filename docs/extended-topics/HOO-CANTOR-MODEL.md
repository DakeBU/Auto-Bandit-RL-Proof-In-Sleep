# Infinite-arm HOO witness and finite-scale packing

The model in `BanditRLProof/HOOCantorModel.lean` instantiates every field of
`RegularCovering` and the probability/mean/smoothness hypotheses of the actual
expected-visits theorem. `Tests/HOOCantorCanary.lean` checks this through the
public root. This is a complete A1/A2 model witness, not the still-open full
Theorem 6 regret endpoint or a proved near-optimality dimension.

* Arms are all infinite binary sequences. The canary checks that the arm type
  is infinite. Regions are finite-prefix cylinders, with centers extending
  the prefix by false forever.
* The dissimilarity is zero on identical arms and `2^(-k)` otherwise, where
  `k` is the first differing coordinate. The implementation reuses Mathlib's
  `PiNat` distance and cylinder results.
* `nu1=nu2=1` and `rho=1/2`. The proof verifies the full binary cover, region
  nonemptiness and measurability, diameter bounds, center membership, contained
  open balls and disjoint same-depth balls.
* Means are `1/2` in the false first-bit cylinder and `1/4` in the true one.
  A2 weak Lipschitz smoothness and the global supremum `1/2` are proved.
* Every reward law gives mass `1/2` to zero and mass `1/2` to either 1 or
  `1/2`, according to the first bit. The kernel is measurable and Markov,
  supported in `[0,1]`, and its integral equals the declared mean. Every arm's
  law is proved unequal to every Dirac measure.

For the depth-three node `[true,false,false]`, the regional supremum is `1/4`
and the diameter budget is `1/8`. Instantiating the existing actual HOO
trajectory/expected-visits chain therefore proves

```
E[T_[true,false,false](N)] <= 512 log(max(N,2)) + 4.
```

No confidence, path-comparison or expected-count premise is supplied by the
canary. It does not claim the displayed upper bound is numerically sharp.

`BanditRLProof/HOOLevels.lean` also proves that every complete depth `h` has
exactly `2^h` nodes and covers the entire arm space. For a general A1 covering,
if `nu1*rho^h < epsilon`, every finite family of pairwise disjoint open balls
of radius `epsilon` has at most `2^h` members. Assign centers to depth-h
regions: two centers in the same region contradict disjointness because one
lies in both balls. Only the diameter bound and zero self-dissimilarity are
used; symmetry and a triangle inequality are not assumed. Geometric decay
then gives a finite bound at every positive radius, addressing the source
proof's coarse-scale finiteness obligation.

Source Definition 4 uses **balls contained in the target set**, not merely
centers belonging to it. The current finite-family bound applies in the
ambient space and will bound those contained packings as well. It does not
yet define the source packing number, formalize Definition 5's limsup, or
derive the required uniform `C*epsilon^(-d')` bound from `d'>d`.

Remaining work includes that near-optimality producer, the actual selected-node
regret partition, geometric summation and depth optimization, the full rate
and regret-expectation identity, independent semantic review, shared topic
acceptance and all-topic ICLR evaluation. Accepted topics remain 0/10.
