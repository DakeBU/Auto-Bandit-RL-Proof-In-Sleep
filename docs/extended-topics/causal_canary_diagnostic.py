"""Exact finite source-contract diagnostic; not a Lean proof or evaluation run."""

from fractions import Fraction as F
from itertools import product
import json
import math


def joint(action):
    law = {}
    for x, w, y in product(range(2), repeat=3):
        pw = F(1 + 2 * x, 4)
        wy = (pw if w else 1 - pw) if action is None else F(w == action)
        py = F(1 + x + 2 * w, 5)
        law[x, w, y] = F(1, 2) * wy * (py if y else 1 - py)
    assert sum(law.values()) == 1
    return law


def main():
    actions = [None, 0, 1]  # Also the recommendation tie order.
    laws = [joint(a) for a in actions]
    states = list(product(range(2), repeat=2))
    parents = [{z: sum(p for (x, w, y), p in law.items() if (x, w) == z)
                for z in states} for law in laws]
    means = [sum(y * p for (x, w, y), p in law.items()) for law in laws]
    assert means == [F(1, 2), F(3, 10), F(7, 10)]
    obs = laws[0]
    conditional = (sum(y * p for (x, w, y), p in obs.items() if w == 1)
                   / sum(p for (x, w, y), p in obs.items() if w == 1))
    assert conditional == F(3, 4) and conditional != means[2]
    q = parents[0]  # eta=(1,0,0), genuinely covers all supports.
    ratios = [{z: pa[z] / q[z] for z in states} for pa in parents]
    moments = [sum(pa[z] * ra[z] for z in states)
               for pa, ra in zip(parents, ratios)]
    m = max(moments)
    assert m == F(8, 3)
    biases = [sum(y * p for (x, w, y), p in law.items() if ra[x, w] > 2)
              for law, ra in zip(laws, ratios)]
    assert biases == [0, F(1, 5), F(3, 10)]
    # Numeric log is used only to locate the tuned cutoff, not as formal evidence.
    cutoff = math.sqrt(float(m) / math.log(6))
    assert 1 < cutoff < 4 / 3
    expected_regret = F(0)
    selected = set()
    for (x, w, y), p in obs.items():
        estimates = [y * ra[x, w] if float(ra[x, w]) <= cutoff else F(0)
                     for ra in ratios]
        choice = max(range(3), key=lambda a: estimates[a])
        selected.add(choice)
        expected_regret += p * (max(means) - means[choice])
    assert selected == {0} and expected_regret == F(1, 5)
    # eta=(0,1,0) fails coverage; never silently accept totalized division here.
    uncovered = [z for z in states if parents[1][z] == 0 and
                 any(pa[z] > 0 for pa in parents)]
    assert uncovered == [(0, 1), (1, 1)]
    print(json.dumps({
        "status": "finite diagnostic only; no Lean proof or controlled evaluation",
        "intervention_means": list(map(str, means)),
        "conditioned_mean_W1": str(conditional),
        "covered_allocation": [1, 0, 0],
        "second_moments": list(map(str, moments)),
        "m": str(m), "bias_at_B2": list(map(str, biases)),
        "T1_tuned_cutoff_approx": cutoff,
        "T1_selected_action": "empty",
        "T1_expected_simple_regret": str(expected_regret),
        "uncovered_states_for_allocation_0_1_0": uncovered,
        "limitations": ["log cutoff located using floating point",
                        "all-horizon endpoint and optimizer not checked"]
    }, indent=2))


if __name__ == "__main__":
    main()
