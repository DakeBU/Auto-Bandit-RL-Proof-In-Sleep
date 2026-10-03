# CMOSS v2: literal logarithmic endpoint boundary

This independently reviewed mathematical observation concerns the literal
endpoint formulas of Ye, Wang, Liu and Li, *Near-Optimal Regret for Efficient
Stochastic Combinatorial Semi-Bandits*, arXiv:2508.06247v2 (28 December 2025).
The frozen PDF SHA-256 is
`951b7fcc133295f7ac22c3f0346b65b5b1c792fe1fe6236a48f1b9d77d0b82d7`.
It is not a Lean certificate, a complete paper audit or a replacement for the
frozen general CUCB contract.

Physical PDF page 4 defines `log` as base two, separately from the positive
truncation used in `ln+`. Theorem 1 displays

$$
O((\log k)\sqrt{kmT})\quad(k\le m/2),\qquad
O((m-k)\sqrt{\log k\log(m-k)T})\quad(k>m/2).
$$

The displayed statement does not exclude $k=1$ or $m-k=1$. On the linear,
at-most-$k$ subset model used in Section 3.2, both endpoints admit a positive
first-round regret, whereas the corresponding displayed factor is zero.

Algorithm 1 initializes every optimistic index to one. Fix the permissible
lexicographic tie rule selecting the first $k$ arms. For $m=2,k=1$, choose
deterministic means $(0,1)$. The first action earns zero instead of the optimum
one. For $m=3,k=2$, choose means $(0,1,1)$. The first action selects arms
$\{0,1\}$ and earns one instead of the optimum two. Both cases have first-round
regret exactly one. Every later gap is nonnegative, so every well-defined
continuation has cumulative regret at least one for all $T\ge1$.

At fixed endpoint dimensions, the respective rate functions vanish identically
because $\log_2 1=0$. A literal $O(0)$ upper bound would require regret to be
zero eventually, so increasing the starting horizon does not remove the
obstruction. These examples fix a legal tie rule; they do not claim that the
same instance defeats every possible tie convention.

There is a separate parameter-domain issue. Physical page 5 chooses
$\delta=m(\log k)^2/(kT)$, and physical page 16 chooses
$\delta=(m-k)^2\log k\log(m-k)/(k^2T)$ for the other branch. These recipes
give zero at the corresponding endpoints. The positive-count radius uses
$1/(\delta T_i)$, which is then undefined over the reals. The explicit
zero-count infinity branch still determines the initial action, but does not
define the entire later algorithm. The regret calculation above therefore
explicitly concerns any well-defined continuation, not a purported complete
execution of the undefined recipe.

An intended positive-log convention, added residual or restricted parameter
domain would change the claim and is not refuted by this literal calculation.
No such repair is certified here. Interior-parameter regret, the complete
action-classification and integration proof, cascading feedback, lower bounds,
experiments, implementations and other versions remain outside this review.
The recent-source audit remains incomplete.

The original extraction-based locator "page 30" was wrong: the PDF has 26
physical pages, and mathematical form-feed characters polluted text-based
page splitting. Independent page-specific extraction and rendering verified
physical pages 4, 5 and 16 before acceptance. Review and working-derivation
hashes are bound in `runs/extended-topics-20260919/cmoss-boundary-review.json`.
No formal dependency edge or topic-completion claim follows from this note.
