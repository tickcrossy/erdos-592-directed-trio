r"""
solve_op1_complete.py -- unified OP1 closed-form dispatcher (Erdos #592, Open Problem 1).

For a hard pattern s (s_0 = s_1 = s_{N-1} = s_N = 2, no two adjacent 2s, at least one
internal even 2) let e <= E be the first / last internal even peak and put
    W_L = (1, e),  W_R = (E, N-1).
The three regimes form a partition of all hard patterns:

  Regime I   : M_od(W_L) = 2  or  M_od(W_R) = 2                 -> Lemma B (TRUE for all N)
  Regime II  : not I, and M_ev(W_L) >= 1 or M_ev(W_R) >= 1       -> Lemma A (TRUE for all N)
  Regime III : not I, not II  (both wings: even positions 0, odd positions <= 1)
                                                                  -> Lemma C
               (TRUE on Regime III \ R and single-odd-peak no-internal-even-peak R;
                OP1 is FALSE on multi-peak R for all even N >= 26, see LEMMA_C_PROOF.md §4)

solve_op1(s) returns (orientation, regime, word) where the word is a directed schedule
for s (orientation 'F') or for s^r (orientation 'R'), always re-verified with
op1_lib.verify_word(..., directed=True).  No search/BFS is used by any solver.
Returns None if no proved branch applies (inevitable on OP1 counterexamples for N >= 26).
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import op1_lib as lib
from prove_lemma_B_v2 import solve_lemma_B_dir
from prove_lemma_A_closed_form import try_closed_form_dir
from prove_lemma_C_closed_form import solve_lemma_C


def wings(s):
    N = len(s) - 1
    evp = [i for i in range(2, N - 1, 2) if s[i] == 2]
    return N, evp[0], evp[-1]


def regime(s):
    N, e, E = wings(s)
    if max(lib.M_od(s, 1, e), lib.M_od(s, E, N - 1)) == 2:
        return 'I'
    if max(lib.M_ev(s, 1, e), lib.M_ev(s, E, N - 1)) >= 1:
        return 'II'
    return 'III'


def _checked(s, w):
    if w is None:
        return None
    try:
        lib.verify_word(s, w, directed=True)
    except AssertionError:
        return None
    return w


def solve_op1(s):
    s = tuple(s)
    reg = regime(s)
    if reg == 'I':
        for d, ss in (('F', s), ('R', s[::-1])):
            w = _checked(ss, solve_lemma_B_dir(ss))
            if w: return d, reg, w
        return None
    if reg == 'II':
        for d, ss in (('F', s), ('R', s[::-1])):
            w = _checked(ss, try_closed_form_dir(ss))
            if w: return d, reg, w
        return None
    r = solve_lemma_C(s)
    if r is None:
        return None
    d, _, w = r
    w = _checked(s if d == 'F' else s[::-1], w)
    return (d, reg, w) if w else None


if __name__ == '__main__':
    s = tuple(int(c) for c in sys.argv[1])
    r = solve_op1(s)
    print(r[:2] if r else None)
    if r:
        print(r[2])
