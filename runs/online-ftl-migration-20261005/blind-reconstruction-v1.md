# Restricted-input decoding of Q0–Q2 and M01–M07

This pass used only `blind-packet-v1.md` in this directory as mathematical file input. No source, public name map, project proof, prior judgment, compilation log, or other file was read. The definitions below are supplied algorithm context; the seven theorem headers have no supplied proofs. The actor is a distinct automated decoder, requested GPT-6 Astra with medium reasoning. Earlier unrelated actor history is not erased and is not claimed absent. This is neither human nor external-model review. No source acceptance, proof validation, compilation, chapter certification, or Goal certification is claimed.

Independent SHA-256 of the packet's exact raw bytes:
`60ba567cec00c4f2e93fd67069c4da01c338bc198ca80153237f5e80d5217708`.

For readability, write S_t(z)=Q0(z,t), a_t(z,x₀)=Q1(z,x₀,t), and b_t=Q2(t). All times and horizons are natural numbers, all sequence values/actions are real numbers, and [−1,1] is the closed real interval. The expressions z_i u can be read as linear losses at action u; this is a direct interpretation of the products in the packet, not attribution to an external algorithm or source. There is no probability, randomness, expectation, filtration, or hidden distribution in any supplied statement.

## Q0 — cumulative sequence definition

1. **Objects:** A full real sequence z:ℕ→ℝ and its recursively defined cumulative sequence S:ℕ→ℝ.
2. **Quantifiers:** The definition applies to every z and every natural time t.
3. **Assumptions:** None on signs, boundedness, or magnitudes of z.
4. **Conclusion:** The defining equations are S₀(z)=0 and S_{t+1}(z)=S_t(z)+z_t.
5. **Constants/index:** Initial value zero; the transition to t+1 adds the entry at t, so S_t contains strictly earlier entries. M01 separately states its finite-sum representation.
6. **Information/probability:** Deterministic recursion on past coefficients; no future entry is needed to evaluate S_t.
7. **Boundary:** Includes t=0. It is an unnormalized cumulative sum, not a mean or a sum including z_t at time t.

## Q1 — action-selection definition

1. **Objects:** A real coefficient sequence z, arbitrary real initialization x₀, time t, and real action a_t.
2. **Quantifiers:** Every z,x₀,t; the definition is a total piecewise formula.
3. **Assumptions:** No feasibility or boundedness premise in the definition itself.
4. **Conclusion:**
   \[
   a_t(z,x_0)=\begin{cases}
   x_0,&t=0,\\
   1,&t>0\text{ and }S_t(z)<0,\\
   -1,&t>0\text{ and }S_t(z)\ge0.
   \end{cases}
   \]
5. **Constants/index:** Endpoints are exactly ±1. At positive time the tie S_t=0 selects −1. Time zero takes precedence over the sign test.
6. **Information/probability:** Deterministic action based only on x₀ and the strict-past cumulative coefficients. The current coefficient z_t is not used for the time-t action.
7. **Boundary:** x₀ can be outside [−1,1] at the definition level; later actions are endpoints regardless. This is not randomized tie-breaking, and the negative-sum branch is strict.

## Q2 — fixed coefficient sequence

1. **Objects:** A fixed real sequence b:ℕ→ℝ.
2. **Quantifiers:** Defined for every natural t, with no free data sequence or initialization.
3. **Assumptions:** None.
4. **Conclusion:**
   \[
   b_t=\begin{cases}-\tfrac12,&t=0,\\1,&t>0\text{ odd},\\-1,&t>0\text{ even}.\end{cases}
   \]
   Its initial entries are −1/2, 1, −1, 1, −1, … .
5. **Constants/index:** The initial −1/2 is exceptional; the parity test uses t modulo 2 equal to 1. Positive even times start at t=2.
6. **Information/probability:** Deterministic sequence fixed by time, with no dependence on actions or x₀; no adaptive or stochastic sequence-generation rule is present.
7. **Boundary:** At t=0 the value is −1/2 rather than the −1 assigned to positive even times. No general claim about arbitrary alternating sequences is included.

## M01 — recursion equals the strict-prefix sum

1. **Objects:** Arbitrary z and S_t(z).
2. **Quantifiers:** Every z:ℕ→ℝ and every t∈ℕ.
3. **Assumptions:** None beyond these types.
4. **Conclusion:** \(S_t(z)=\sum_{i=0}^{t-1}z_i\).
5. **Constants/index:** The finite range is 0,…,t−1, with empty sum zero at t=0.
6. **Information/probability:** Deterministic equality involving only the strict past.
7. **Boundary:** No bound or sign condition on z; no inclusion of current coefficient z_t, averaging, or asymptotic approximation.

## M02 — strict-past invariance of the action

1. **Objects:** Sequences z,w, common real initialization x₀, time t, and the paired actions a_t(z,x₀),a_t(w,x₀).
2. **Quantifiers:** Every z,w,x₀,t, assuming equality of z_i and w_i for every i<t.
3. **Assumptions:** Strict-prefix equality only; the initialization is the same in both runs. No feasibility premise.
4. **Conclusion:** a_t(z,x₀)=a_t(w,x₀).
5. **Constants/index:** Cutoff is strictly i<t, not i≤t; current and future entries may differ.
6. **Information/probability:** Deterministic causality conditional on common fixed initialization. No probabilistic information restriction is asserted.
7. **Boundary:** At t=0 the sequence-equality premise is vacuous. Does not compare different initializations or certify that an externally chosen x₀ itself cannot encode other information.

## M03 — feasibility of every selected action

1. **Objects:** Sequence z, initialization x₀, action a_t and interval [−1,1].
2. **Quantifiers:** Every z, every x₀ in the interval, and every natural t.
3. **Assumptions:** −1≤x₀≤1; no restrictions on z.
4. **Conclusion:** −1≤a_t(z,x₀)≤1.
5. **Constants/index:** Closed endpoints ±1; includes initial time and both later endpoint choices.
6. **Information/probability:** Deterministic feasibility statement, independent of sequence generation.
7. **Boundary:** Infeasible initialization is excluded by this header, although Q1 is defined for it. The conclusion is interval membership, not strict interior membership.

## M04 — current action minimizes cumulative past linear loss

1. **Objects:** Arbitrary z,x₀,t, and comparator u∈[−1,1]; evaluate the one action a_t on every past coefficient.
2. **Quantifiers:** Every z,x₀,t and every feasible u. In particular there is no x₀∈[−1,1] hypothesis.
3. **Assumptions:** Only u∈[−1,1].
4. **Conclusion:**
   \[
   \sum_{i=0}^{t-1}z_i a_t(z,x_0)\le\sum_{i=0}^{t-1}z_i u.
   \]
   Equivalently S_t(z)a_t(z,x₀)≤S_t(z)u. The current action is reused across the whole left sum: it is not \(\sum_{i<t}z_i a_i\).
5. **Constants/index:** Past horizon t, no current coefficient z_t. No approximation term or coefficient scaling.
6. **Information/probability:** Deterministic minimization of the already observed linear objective. It is not a comparison of accumulated actually played losses with a comparator.
7. **Boundary:** t=0 gives two empty sums, regardless of x₀'s feasibility. For t>0, if S_t=0 all feasible actions have equal objective value, while Q1 chooses −1; no unique-minimizer claim is stated.

## M05 — exact prefix sums of the fixed sequence

1. **Objects:** Fixed sequence b=Q2 and S_t(b).
2. **Quantifiers:** Every positive natural t.
3. **Assumptions:** t>0.
4. **Conclusion:**
   \[
   S_t(b)=\begin{cases}-\tfrac12,&t\text{ odd},\\+\tfrac12,&t\text{ even}.\end{cases}
   \]
5. **Constants/index:** Exact alternating half-unit values. The prefix ends at t−1, so its sign is opposite to the positive-time coefficient b_t.
6. **Information/probability:** Deterministic arithmetic characterization of the fixed past sequence; no random fluctuation or expected value.
7. **Boundary:** t=0 is excluded: S₀(b)=0 rather than +1/2. No equality for a general z is asserted.

## M06 — exact actions on the fixed sequence

1. **Objects:** b=Q2, arbitrary initialization x₀∈ℝ, and actual action a_t(b,x₀).
2. **Quantifiers:** Every x₀ and every positive natural t.
3. **Assumptions:** t>0 only; initialization need not be feasible.
4. **Conclusion:**
   \[
   a_t(b,x_0)=\begin{cases}1,&t\text{ odd},\\-1,&t\text{ even}.\end{cases}
   \]
5. **Constants/index:** Exact endpoints and parity at the current index t; no time shift. For t>0 this equals b_t.
6. **Information/probability:** Deterministic realized behavior of the strict-past rule on a fixed sequence. Equality with the current coefficient does not mean the rule reads that coefficient; Q1 and M02 specify its past-only dependence.
7. **Boundary:** At t=0 the action is x₀, not the positive-time parity formula. No dependence on x₀ remains at positive times in this conclusion.

## M07 — exact excess loss against the zero comparator and a linear lower bound

1. **Objects:** The fixed sequence b, its actual actions a_t(b,x₀), feasible initialization, positive horizon T, and the fixed comparator 0∈[−1,1].
2. **Quantifiers:** Every x₀∈[−1,1] and every T∈ℕ with T>0; the same fixed b works for all of them. No existential or action-adaptive coefficient sequence is chosen in the header.
3. **Assumptions:** −1≤x₀≤1 and T>0.
4. **Conclusion:** Define the displayed difference
   \[
   D_T=\sum_{t=0}^{T-1}b_t a_t(b,x_0)-\sum_{t=0}^{T-1}b_t\cdot0.
   \]
   Both clauses hold:
   \[
   D_T=T-1-\frac{x_0}{2},\qquad T-\frac32\le D_T.
   \]
   The first is an exact comparator-loss difference; the second is a uniform lower bound over the allowed initialization interval.
5. **Constants/index:** T is coerced to ℝ. Initial contribution −x₀/2 is retained exactly; the remaining T−1 rounds determine the T−1 term. Lower constant is exactly 3/2, with no unspecified O(1) replacement.
6. **Information/probability:** Deterministic realized cumulative loss, not expected loss. The sequence is fixed independently of x₀, and actions follow the past-based rule. It compares to the specified zero action, not a minimization over all comparators.
7. **Boundary:** T=0 is excluded; T=1 is included and the lower bound may be negative. This is not a lower bound for every online algorithm, nor an assertion that zero is the best comparator. There is no probabilistic, asymptotic-only, or source-level acceptance claim.

## Scope limits

All three context definitions and all seven proof-omitted headers are decoded in seven slots. The distinction between a single current action minimizing past cumulative loss (M04) and the sequence of actually played actions in the cumulative comparator difference (M07) is preserved. No theorem body was supplied or checked, and no original source was consulted; compilation and scientific acceptance remain outside this pass.
