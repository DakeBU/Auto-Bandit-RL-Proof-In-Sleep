"""Exact finite checks of printed SynCD v1 subclaims, not its regret theorem.

Source: arXiv:2510.06683v1, physical pages 4, 9, 12, 14.
These diagnostics interpret the displayed pseudocode literally. They are not
simulations, performance evaluations, or a replacement implementation of SynCD.
"""
import json
from fractions import Fraction


def witnesses():
    # Algorithm 1 line 13, Acc empty, M_t=M=2, K_t=3, ranks j=0,1.
    # The printed arm expression does not use the outer cycle variable.
    # Hold sets fixed and evaluate an uninterrupted block. Communications and
    # updates may interrupt a real Algorithm 1 trace; reachability is not claimed.
    schedule = [
        [(p - (j + 2 - 2)) % 3 for j in range(2)]
        for cycle in range(3) for p in range(2)
    ]
    counts = [[sum(row[j] == k for row in schedule) for k in range(3)]
              for j in range(2)]
    assert schedule == [[0, 2], [1, 0]] * 3
    assert counts == [[3, 3, 0], [3, 0, 3]]
    assert all(len(set(row)) == 2 for row in schedule)
    assert any(0 in count for count in counts)

    # With beta>1, every positive nonincreasing ECR update passes the
    # printed test ECR_t <= beta*ECR_last, even without a factor-beta drop.
    beta, previous, current = Fraction(2), Fraction(1, 2), Fraction(2, 5)
    assert current <= beta * previous
    assert current > previous / beta

    # Lemma 6's square-root ratio step needs more than T_p<=beta^2*T_(p-1).
    before, after, offset = 12, 48, 6
    assert after <= beta * beta * before
    shifted_ratio = Fraction(after - offset, before - offset)
    assert shifted_ratio == 7 and shifted_ratio > beta * beta

    # Lemma 9's displayed threshold alone gives a lower, not upper, count.
    # u denotes log(delta^-1); choose delta=exp(-2), so u=2 exactly.
    u, threshold_beta, n, mk = Fraction(2), Fraction(1, 2), 100, 6
    assert u / (2 * n) <= threshold_beta * threshold_beta
    claimed_upper = u / (2 * threshold_beta * threshold_beta) + mk
    assert claimed_upper == 10 and n > claimed_upper

    # Algorithm 6 emits payload bits on even slots before its terminal even
    # slot. Algorithm 5 treats every even-slot collision as termination.
    # Favorable shared receiver-arm convention; no third-player interference.
    bits = [1, 0, 1]
    length = len(bits)
    collision_slots = [
        slot for slot in range(1, 2 * length + 1)
        if slot == 2 * length
        or (slot % 2 == 0 and bits[slot // 2 - 1] == 1)
    ]
    stop = next(slot for slot in collision_slots if slot % 2 == 0)
    assert stop == 2 and stop < 2 * length

    # DPE1 Appendix A.2's deterministic pairwise rank schedule. Exhaustive
    # small finite checks supplement (and do not replace) its algebraic proof.
    rank_cases = 0
    for arms in range(3, 13):
        def arm(state, step):
            return step - state if 2 * state + 1 <= step <= arms + state - 1 else state
        for low in range(1, arms):
            for high in range(low + 1, arms):
                collisions = [step for step in range(1, 2 * arms - 1)
                              if arm(low, step) == arm(high, step)]
                assert collisions == [low + high]
                assert 2 * low < low + high <= 2 * high
                rank_cases += 1

    return {
        'status': 'finite printed-subclaim diagnostics passed',
        'scope': 'No full SynCD simulation, Lean theorem, regret negation or repaired-algorithm acceptance',
        'source_version': 'arXiv:2510.06683v1',
        'schedule': {'M': 2, 'K': 3, 'actions_by_time': schedule, 'counts_by_player_arm': counts,
                     'scope': 'uninterrupted scheduling expression with fixed sets; full-policy reachability not claimed'},
        'trigger': {'beta': str(beta), 'previous': str(previous), 'current': str(current),
                    'printed_trigger': True, 'factor_drop_trigger': False},
        'shifted_ratio': {'before': before, 'after': after, 'offset': offset,
                          'ratio': str(shifted_ratio), 'beta_squared': str(beta * beta)},
        'threshold_direction': {'log_delta_inverse': str(u), 'beta': str(threshold_beta),
                                'count': n, 'displayed_upper': str(claimed_upper),
                                'first_crossing_assumed': False},
        'communication': {'bits': bits, 'collision_slots': collision_slots,
                          'receiver_stop': stop, 'terminal_slot': 2 * length},
        'dpe_rank_pair_cases': rank_cases,
    }


if __name__ == '__main__':
    print(json.dumps(witnesses(), indent=2))
