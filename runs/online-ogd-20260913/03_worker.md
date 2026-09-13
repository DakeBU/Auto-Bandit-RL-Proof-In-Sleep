# Worker report

Frozen interfaces implemented in the new OGD module. The first-order inequality
is proved from convexity along an affine line and a real derivative, not assumed.
The fixed-step proof inducts over the actual generated trajectory and retains the
negative terminal squared distance before dividing by eta. The tuned theorem
uses bounds on that tuned trajectory and supplies all comparators uniformly.

Attempts 01-04 and canary 01-02 are retained. Only proof bodies were repaired;
original ten header hashes and the definition/ambient-instance prefix are guarded.
A failed verifier metadata call was repaired with no mathematical target change.

Public canary: V=[0,1], x1=0, eta=1, losses -2x then x/2. The first unconstrained
step is 2 and projects to 1; the next point is 1/2. Regret to u=0 is 1/2 and the
terminal squared distance is 1/4. A separate tuned endpoint uses D=1,G=2,T=2.
A typed EuclideanSpace R (Fin 3) instance checks finite-dimensional applicability.

All OGD audit lines contain only propext, Classical.choice and Quot.sound.
No independent reviewer claim is made. Full gate and source-map checks remain the
reviewer phase's responsibility; focused compilation alone does not accept the task.
