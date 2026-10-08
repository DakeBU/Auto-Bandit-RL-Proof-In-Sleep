# Pre-proof lower-leaf statement seal: computational-basis Hellinger
Model: one fixed chronological QuantumQueryWord.Word, same known gates under U,V,
normalized complex finite Euclidean input. Every forward/inverse oracle use is charged.
No adaptive history or cross-block register enters this leaf.
Anchor: define basis output p(j)=||x(j)||^2 and the unnormalized squared Hellinger
sum H2(p_x,p_y)=sum_j (||x(j)||-||y(j)||)^2. Normalized x,y make genuine probabilities;
convention without factor 1/2 is mandatory. Prove H2 <= ||x-y||^2 by coordinate
reverse-triangle inequality and Euclidean norm identity. Then for the two unitary
word outputs with ||U-V||op<=eta prove H2<=q^2 eta^2<=D q eta^2 when q<=D.
The final output distributions' normalization MUST be proved, not assumed.
SOURCE assumptions: finite index, normalized input, two actual unitary oracles,
same specified known gates, operator distance eta, syntactic query bound q<=D.
RULED: output unitarity, state distance <=q eta, probability normalization, coordinate
reverse triangle, q²<=Dq. Do not add any of these as public assumptions.
Scope: final computational-basis measurement only. General POVM dilation, two-arm
parameter-to-unitary distance, adaptive chain, stopping, testing/regret lower bound
remain open. This is no minimax theorem and no external theorem adapter.
