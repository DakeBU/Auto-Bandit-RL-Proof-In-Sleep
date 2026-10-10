# Two complete neutral energy canary reconstructions

Actor /root/osd_blind; requested GPT-6 Astra / medium, without independent runtime model/effort attestation. This reused automated decoder has related staged history; this packet is source-withheld, not absolutely context-blind, human or externally reviewed. Only the specified new neutral canary packet was read. No source, contract, proof or review was consulted.

Both transcripts end in “:= by” with no body. They are header-only proposition transcripts, not completed proofs or compilation evidence.

## Shared formula and local-let scope

In each theorem the definitions A and B are separate local lets that scope the whole ensuing conjunction:
\[
A(z,m)=\sum_{t=0}^{m-1}
\frac{|z_t|^2}{\sqrt{\sum_{i=0}^{t}|z_i|^2}},
\qquad
B(z,m)=\sum_{i=0}^{m-1}|z_i|^2,
\quad z:\mathbb N\to\mathbb R,\ m:\mathbb N.
\]
The Lean norm is the real norm, hence absolute value. The current squared entry is included in each denominator's prefix. Real.sqrt and real division are total; in particular 0/0=0. There is no positive offset or epsilon in the denominator. Empty sums are zero. A,B are fixed local function definitions, not new global declarations or universally asserted inequalities.

## finite_example

The additional local let defines
\[
w_t=\begin{cases}3&t=1\\4&t=3\\0&\text{otherwise}.\end{cases}
\]
The eight top-level conjuncts assert a scale-2 inequality at horizon 4, exact values A(w,4)=31/5 and B(w,4)=25, a strict unscaled inequality, and the four displayed coordinate values:
\[
\begin{aligned}
&\frac22 A(w,4)\le2\sqrt{B(w,4)}
\land A(w,4)=31/5
\land B(w,4)=25\\
&\land A(w,4)<2\sqrt{B(w,4)}
\land w_0=0\land w_2=0\land w_1=3\land w_3=4.
\end{aligned}
\]
In natural language, the tested prefix has a leading zero, then 3, another zero, then 4. Its normalized energy sum is asserted to be 31/5, its total squared energy 25, and the sum is both non-strictly bounded as written in the scaled expression and strictly less than twice the square root of that total.

1. **Model:** Concrete scalar sequence w, local A/B functions and finite natural horizon 4. Deterministic, with no probability, learner or loss stream.
2. **Objective:** Compare the inclusive-prefix-normalized squared-norm sum against twice the square root of total squared norm; report exact values and individual sequence entries.
3. **Hypotheses:** No external assumptions. The three local lets fix all objects, and every inequality/equality in the conjunction is an asserted conclusion, not a premise or proof.
4. **Quantifiers and scope:** Closed eight-part conjunction after w,A,B. Indices t and i are bound within sums; there is no universal scale, horizon or sequence quantifier. The coordinate conjunct order is exactly 0,2,1,3.
5. **Algorithm-information:** The term at t uses w0,…,w_t, including the current entry. The type defines no adaptive algorithm or timing restriction on choosing a step size. Entries outside 0,…,3 are defined as zero but not used in these finite sums.
6. **Conclusion, constants and boundaries:** range 4={0,1,2,3}; inclusive squared-energy prefixes are 0,9,9,25. Thus the first displayed quotient uses denominator zero and numerator zero, interpreted as zero. At t=2 the numerator is zero but the denominator is sqrt 9, a different zero-contribution case. The scale prefactor is (2/2)=1 and RHS is 2sqrt25; neither is a normalization by horizon. The exact values 31/5 and 25 and the strict comparison are separate conjuncts. No term at t=4 occurs.
7. **Evidence and exclusions:** This reconstructs all eight assertions, not only the first inequality. The transcript supplies no proof of the exact values or strictness. It does not assert a theorem for arbitrary w, all horizons or all scales, nor a performance guarantee.

## boundary_example

The local sequences are v1_t=1 and v0_t=0 for every natural t. With the same local A/B formulas, the type is the conjunction of three distinct boundary comparisons:
\[
\left[\frac22 A(v_1,0)\le2\sqrt{B(v_1,0)}\right]
\land
\left[\frac22 A(v_0,3)\le2\sqrt{B(v_0,3)}\right]
\land
\left[\frac02 A(v_1,2)\le0\sqrt{B(v_1,2)}\right].
\]
The first uses an empty horizon despite nonzero entries; the second uses three zero entries; the third uses two nonzero entries but zero scale.

1. **Model:** Two fixed constant real sequences and three fixed horizon/scale combinations, with local A and B shared across the conjunction.
2. **Objective:** Test the same inequality expression at horizon zero, zero accumulated energy and zero multiplicative scale, preserving the different mechanisms.
3. **Hypotheses:** None external. Four lets fix v1,v0,A,B; there is no universal nonnegative-scale hypothesis here.
4. **Quantifiers and scope:** Closed three-part conjunction. In order: scale 2/horizon 0/ones; scale 2/horizon 3/zeros; scale 0/horizon 2/ones. No quantified arbitrary horizon or sequence.
5. **Algorithm-information:** No algorithm, randomness or feedback semantics. Each A is determined by an inclusive finite prefix, although in the first case no term is evaluated.
6. **Conclusion, constants and boundaries:** First clause: outer range 0 and B(v1,0) are empty, so it has the zero-versus-zero form without encountering an actual summand denominator. Second: range 3 is nonempty, each numerator and inclusive-prefix denominator is zero; three totalized 0/0 terms and total energy zero give the same form. Third: B(v1,2)=2 and the prefixes are 1 and 2, so denominators are nonzero; it is the zero prefactor and zero RHS factor that yield zero versus zero. There is no division by the scale: 0/2 is zero with nonzero denominator 2.
7. **Evidence and exclusions:** The three mechanisms are not interchangeable, and the third does not assert A(v1,2)=0 or B(v1,2)=0. No strict inequality or exact A value is asserted here. Header-only text does not prove any clause or certify a general result.

## Completeness and ambiguity

Both full local-let propositions have been reconstructed with all eight/three top-level conjuncts and seven semantic slots each. No unresolved type or semantic ambiguity was identified. The denominator conventions distinguish leading zero energy from an empty sum and from zero external scale. No proof, compilation, source matching or acceptance claim is made.
