# Candidate semantic review

Same-model GPT-6 Astra/medium sequential reviewer, not independent external review. All seven headers and the exact definition/import prefix match frozen v1. Integration v2 changes only file paths. Source Example2.10 printedp12/PDF24 and hash reread. Arbitrary initial point in[-1,1], source coefficient-1/2 and subsequent alternating coefficients, T>=1 and comparator0 remain explicit.

The running coefficient is recursively initialized at0 and updated using only current feedback. Its sum theorem identifies exactly t past losses. The predictor's prefix invariance is proved for arbitrary streams; feasibility follows from its feasible initial value or endpoint decisions. The historical objective is coefficient times decision, so a negative coefficient chooses1 and a nonnegative coefficient chooses-1. At t=0 every objective is0, making the first choice arbitrary. Hence the implemented predictor actually is FTL, not an assumed alternating sequence.

For the source stream, every positive prefix is plus/minus1/2 and never ties. Its sign determines the alternating predictions, each later incurred loss equals1, and the initial loss is -x0/2. Induction gives exact regret T-1-x0/2 and the feasible upper bound x0<=1 yields T-3/2. The zero comparator sum is explicitly zero. The theorem does not claim a lower bound for every online algorithm.

Public-canary01 uses initial1/3 and six rounds, derives29/6 and checks actual initial predictions1/3,1,-1. Seven public and two canary axiom prints contain only propext, Classical.choice, Quot.sound. Mathematical derivation and source identity are jointly audited; teaching-route links are not claimed to be proof-term dependencies. Actual full-root graph and final root/Tests/harness/site gates are separate requirements, still pending here. No Chapter2/whole-book completion.

Final verdict: accepted-local after every separately recorded gate; see acceptance-decision.md.
