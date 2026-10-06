# Restricted blind reconstruction: scalar absolute value, v1

## Input and actor limits

For this task I read only the current designated blind-packet-v1.md. This actor previously reconstructed separate restricted differentiability and finite-sum packets. I therefore do not claim a new actor with no prior context; those earlier files were not reread here. I read no source identity, proof body, old verdict, compilation result, or other current project file, and performed no repository search. Requested configuration remains GPT-6 Astra / medium; runtime model provenance is not independently attested. This is a restricted machine reconstruction, not human/external review, source acceptance, compilation verification, or completion of a package, chapter, or user Goal.

The seven slots used consistently below are: (1) objects/types, (2) supplied premises, (3) quantifiers, (4) ambient/domain scope, (5) exact conclusion, (6) supplied versus derived regularity, and (7) limits/degeneracies.

## Complete borrowed support definition

The packet borrows S; it does not introduce it as a new locally owned definition. For any normed additive group E with a real inner-product space structure, any f : E -> EReal, and x : E,

S(f,x) = {g in E | for every y in E, f(x) + coe(inner_real(g,y-x)) <= f(y)}.

Thus there are two separate universal levels in a set characterization: every candidate vector g is classified by membership, and its membership tests every ambient point y. There is no restriction to nearby y, positive y, a finite domain, or a selected sample. The generic definition itself imposes no convexity, properness, local finiteness, differentiability, finite-dimensionality, or completeness condition and permits arbitrary EReal-valued functions. It does not bake in an empty-set convention for infinite function values.

Here ALL FOUR target statements specialize to E=real and the fixed everywhere-finite function f(y)=coe(|y|). Its intrinsic real inner product gives inner_real(g,y-x)=g*(y-x). Because all terms here are real finite, the exact support test is equivalent to

for every y : real, |x| + g*(y-x) <= |y|.

The target signatures have no free ambient E, FiniteDimensional, or CompleteSpace parameters and no convexity, differentiability, or domain qualification premises. Their assertions are deterministic, static, and use exact real constants.

## N01 — full closed interval at zero

1. **Objects/types:** the fixed scalar absolute-value function embedded into EReal; query point exactly x=0; the output is a set of real slopes.
2. **Supplied premises:** none. In particular, no supporting inequality, selected slope, convexity certificate, or differentiability assumption is supplied.
3. **Quantifiers:** for EVERY g : real, membership in S(f,0) is equivalent to -1 <= g AND g <= 1. Membership itself means for EVERY y : real, g*y <= |y|. Both necessity and sufficiency are asserted.
4. **Ambient/domain scope:** the support line passes through (0,0), and must lie below |y| at every real y, including both signs and zero; this is not only a local condition.
5. **Exact conclusion:** S(f,0)=Icc(-1,1). Both endpoints -1 and 1 are included, as is every intermediate real slope; no slope less than -1 or greater than 1 is included.
6. **Supplied versus derived regularity:** finiteness comes from the fixed function. The result classifies supporting slopes without asserting differentiability at zero. Necessity is transparently consistent with testing y=1 and y=-1; sufficiency uses g<=1 on nonnegative y and g>=-1 on negative y. This explains the statement's content and is not a claim to have inspected its proof.
7. **Limits/degeneracies:** the conclusion is a whole interval, not one chosen slope such as 0, a singleton, an open interval, or merely existence of a support. At y=0 the inequality is equality for every g, so that single test does not characterize membership. There is no approximate tolerance on the endpoints.

## N02 — positive-query singleton

1. **Objects/types:** x : real, fixed f(y)=coe(|y|), and the entire set of real supporting slopes at x.
2. **Supplied premises:** strictly 0<x. No candidate g or assumed support inequality appears as a premise.
3. **Quantifiers:** for every positive x and every g : real, [for every y : real, |x|+g*(y-x)<=|y|] iff g=1. This asserts both that 1 supports globally and that every other slope fails at some ambient query.
4. **Ambient/domain scope:** positivity restricts x only. The tested y still ranges over all real numbers, including negative y and zero.
5. **Exact conclusion:** S(f,x)={1}; the unique supporting slope is exactly +1.
6. **Supplied versus derived regularity:** |x|=x follows from hx; for g=1 the left side simplifies to y, which is <=|y| globally. Necessity can be understood from y=0 and y=2*x, forcing g>=1 and g<=1 respectively. No differentiability premise is needed by the signature, and no derivative theorem is itself the stated output.
7. **Limits/degeneracies:** x=0 is excluded by strict positivity and is handled by N01. The statement neither picks a slope from a larger set nor only proves that 1 is one admissible slope. It is not a claim about the norm in a general multidimensional space.

## N03 — negative-query singleton

1. **Objects/types:** x : real, fixed f(y)=coe(|y|), and a set of scalar slopes.
2. **Supplied premises:** strictly x<0, with no supplied candidate support or other function regularity hypotheses.
3. **Quantifiers:** for every negative x and every g : real, [for every y : real, |x|+g*(y-x)<=|y|] iff g=-1. Both inclusion directions of the singleton equality are present.
4. **Ambient/domain scope:** negativity constrains x, not the global test y. Positive y, negative y, and zero all remain among the tests.
5. **Exact conclusion:** S(f,x)={-1}; the only supporting slope is exactly -1, and it actually supports.
6. **Supplied versus derived regularity:** |x|=-x follows from hx; g=-1 reduces the left side to -y, which is <=|y| globally. Necessity is consistent with y=0 and y=2*x giving g<=-1 and g>=-1. These are semantic checks, not reported proof-body dependencies. No differentiability or convexity assumption is supplied.
7. **Limits/degeneracies:** zero is excluded here. The minus sign is essential. The result is not just existence, a one-sided local slope, or a derivative claim for arbitrary functions.

## N04 — complete all-real terminal

1. **Objects/types:** arbitrary x : real and the fixed finite absolute-value function; output the entire real support set at x.
2. **Supplied premises:** no sign restriction or other premise beyond x being real.
3. **Quantifiers:** for every x : real and EVERY candidate g : real, the global support condition holds exactly in the appropriate sign case: (x>0 AND g=1) OR (x=0 AND -1<=g AND g<=1) OR (x<0 AND g=-1). Each admissible g satisfies the inequality for EVERY ambient y, and each excluded g fails at at least one y.
4. **Ambient/domain scope:** all x are covered and all real y are tested for each x and g. No neighborhood, domain interior, boundary exclusion, or multidimensional ambient generalization is introduced.
5. **Exact conclusion:** S(f,x) equals if 0<x then {1}, else if x=0 then Icc(-1,1), else {-1}. In the final nested branch, failure of 0<x together with x!=0 implies x<0 by the total order on real numbers. It is therefore precisely the negative branch, not an unspecified residual case.
6. **Supplied versus derived regularity:** the three sign cases are exhaustive and disjoint. The leaf statements N01–N03 have exactly the matching semantic conclusions; I have not inspected whether N04's proof calls them. No additional smoothness or qualification assumption is added. The zero branch retains the full closed interval and both endpoints.
7. **Limits/degeneracies:** this is a set-valued equality, not an algorithm or instruction to choose a slope. In particular it does not reduce the zero case to g=0 or to either endpoint. It claims no measurable/computable selection, probability, differentiability at zero, multidimensional norm formula, source correspondence, or chapter coverage.

## Contract checks across the four targets

None of N01–N04 assumes that an arbitrary given slope already supports the function. Each equality classifies every slope with necessity AND sufficiency. Singleton equality in the nonzero cases includes existence as well as uniqueness; interval equality at zero includes every real value in the closed interval. All targets retain the global test against all real y, even in the strictly positive or negative branches for x. Generic EReal subtleties do not introduce nonfinite values into this particular function: coe(|y|) is finite at every y.

## Access accounting

Actor task: /root/differentiability_blind.
Content read during this task: E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/blind-packet-v1.md only.
Written during this task: E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/blind-reconstruction-v1.md and E:/ABRL/worktrees/research-online-book/runs/online-subgradient-absolute-migration-20261007/blind-receipt-v1.json only.
Raw-byte hashing reads the packet and those two outputs; these accesses are listed in the receipt. No other path is accessed for this task. Earlier actor tasks are acknowledged above but their files were not accessed again here.
