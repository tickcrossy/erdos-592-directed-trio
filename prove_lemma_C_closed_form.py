r"""
prove_lemma_C_closed_form.py -- Lemma C (Regime III) pure closed-form solver.

Regime III (hard pattern s, first / last internal even peaks e <= E):
    M_ev(s, 1, e) = M_ev(s, E, N-1) = 0,  M_od(s, 1, e) <= 1,  M_od(s, E, N-1) <= 1.

Structure of the solver (100% hand-proved closed-form theorems; NO search, BFS,
empirical templates, or bounded word enumeration):

  Layer 1  (closed-form theorems, see LEMMA_C_PROOF.md, Section 3)
      T0        : no internal odd peak
      TailZero  : right wing has no odd 1
      N3T1      : s[E+1] = 0
      N3T2      : s[N-3] = 1
      N5        : left wing has no odd 1
      N6S       : sandwiched odd weights (s[e+1] = s[E-1] = 1)
      Layer 1 is rigorously proved for every length N; it leaves exactly the
      residual family R (Section 3.7).

  Layer 2  (15 hand-proved positive theorems on R, see LEMMA_C_PROOF.md, Section 5)
      Uses universal exits R-Exit and exit_from_EEe together with 15 explicit
      length-independent phase-program theorems:
        1.  E-Reach (direct / 2 / 1 / 0)
        2.  E-Reach-Super
            [Together with Z1-q1, Theorems 1-2 give a 100% rigorous proof for
             the entire single-odd-peak no-internal-even-peak subfamily of R
             at arbitrary length N.]
        3.  Z0
        4.  Z1-q1
        5.  Q-step-all
        6.  G-Zero (G-adj, G-zero-v2, G-zero-v1)
        7.  G-Zero-Universal (GZ-L1, GZ-Q, GZ-U, GZ-V)
        8.  M-Bridge
        9.  Q-Step-E3
        10. E1-Skip (a, b)
        11. E2-Q1
        12. E3-U
        13. G-Bridge
        14. Q2-Zip
        15. Q-G-N3

      Note: Open Problem 1 is FALSE on R for all even N >= 26 (Section 4 of
      LEMMA_C_PROOF.md); the unique smallest counterexample is
          s* = 220001201200020121012100022   (N = 26, length 27),
      and every wing extension s(W_L, W_R) with the same 15-entry core fails
      OP1 in both orientations.  Consequently, no valid solver can cover all of
      R for N >= 26.  On all N <= 24, Layer 1 + Layer 2 cover 100% of Regime III.

Every returned word is verified via op1_lib.verify_word(s, w, directed=True).
Both orientations s and s^r are tried (OP1 allows either).
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import op1_lib as lib

_LET = (('x', 'y'), ('x', 'z'), ('y', 'z'))


# ----------------------------------------------------------------------------
# Basic phase machinery (identical semantics to op1_lib.Sched.go)
# ----------------------------------------------------------------------------
def run(s, t, phases):
    w = []
    for cur, tgt in phases:
        lets = _LET[cur]
        if tgt < t[cur]:
            return None, None
        while t[cur] < tgt:
            l = lets[(t[cur] + 1) & 1]
            t = lib.step(s, t, l)
            if t is None:
                return None, None
            w.append(l)
    return t, ''.join(w)


def init_word(a):
    return 'x' + ''.join('y' if i % 2 else 'x' for i in range(1, a + 1)) + 'z'


def exec_program(s, a0, phases):
    N = len(s) - 1
    if not (1 <= a0 <= N - 1):
        return None
    t, w = run(s, (a0, 1, 1, 7), phases)
    if t != (N, N, N, 7):
        return None
    full = init_word(a0) + w
    try:
        lib.verify_word(s, full, directed=True)
    except AssertionError:
        return None
    return full


def peaks(s):
    N = len(s) - 1
    evp = [i for i in range(2, N - 1, 2) if s[i] == 2]
    odp = [i for i in range(3, N - 1, 2) if s[i] == 2]
    return N, evp, odp


def is_regime3(s):
    N, evp, _ = peaks(s)
    if not evp:
        return False
    e, E = evp[0], evp[-1]
    return (lib.M_ev(s, 1, e) == 0 and lib.M_ev(s, E, N - 1) == 0
            and lib.M_od(s, 1, e) <= 1 and lib.M_od(s, E, N - 1) <= 1)


# ----------------------------------------------------------------------------
# Layer 1: closed-form theorems covering Regime III \ R
# ----------------------------------------------------------------------------
def layer1_dir(s):
    N, evp, odp = peaks(s)
    e, E = evp[0], evp[-1]
    fin = [(0, N - 1), (2, N), (0, N)]
    odR1 = [i for i in range(E + 1, N - 1, 2) if s[i] == 1]
    odL1 = [i for i in range(3, e, 2) if s[i] == 1]
    # T0: no internal odd peak at all
    if not odp:
        p = max(i for i in range(1, e, 2) if s[i] > 0)
        w = exec_program(s, E - 1, [(2, p), (1, N - 3), (2, e)] + fin)
        if w: return 'T0', w
    # TailZero: right wing without odd 1
    if not odR1:
        w = exec_program(s, E - 1, [(1, N - 2)] + fin)
        if w: return 'TailZero', w
    # N3T1: s[E+1] = 0
    if s[E + 1] == 0 and odR1:
        alpha = odR1[-1]
        t = max(i for i in range(1, e, 2) if s[i] > 0)
        if t == 1:
            w = exec_program(s, E - 1, [(1, N - 3), (2, e)] + fin)
        else:
            w = exec_program(s, E - 1, [(2, 1), (1, alpha), (2, t), (1, N - 3), (2, e)] + fin)
        if w: return 'N3T1', w
    # N3T2: s[N-3] = 1
    if s[N - 3] == 1:
        w = exec_program(s, E - 1, [(1, N - 3), (2, e)] + fin)
        if w: return 'N3T2', w
    # N5: left wing without odd 1
    if not odL1:
        w = exec_program(s, E - 1, [(1, N - 3), (2, e)] + fin)
        if w: return 'N5', w
    # N6S: sandwiched odd weights
    if e < E and odp:
        if lib.M_od(s, 1, e) <= s[E - 1] and lib.M_od(s, E, N - 1) <= s[e + 1]:
            w = exec_program(s, e - 1, [(1, E - 1), (2, e), (0, N - 2), (1, N - 1)] + fin)
            if w: return 'N6S', w
    return None


# ----------------------------------------------------------------------------
# Layer 2: universal right-wing exits and 15 hand-proved theorems on R
# ----------------------------------------------------------------------------
def r_exit_odd(s, c):
    """Proved R-Exit from (E, N-3, c, 7): c < E odd, s[c] >= 1, no odd > 0 in (c, g),
    where g is the first even position in (c, E] with s[g] >= 1."""
    N = len(s) - 1
    E = max(i for i in range(2, N - 1, 2) if s[i] == 2)
    g = next(i for i in range(c + 1, E + 1, 2) if s[i] >= 1)
    if any(s[i] > 0 for i in range(c + 2, g, 2)):
        return None
    return ([] if g == c + 1 else [(0, E + 1), (2, g)]) + [(0, N - 1), (2, N), (0, N)]


def exit_from_EEe(s):
    """Proved universal exit from (E, E, e, 7) on R."""
    N, evp, odp = peaks(s)
    e, E = evp[0], evp[-1]
    q1 = odp[0]
    alpha = max(i for i in range(E + 1, N - 1, 2) if s[i] == 1)
    p1 = next(i for i in range(e + 1, E + 1) if s[i] == 2)
    if s[e + 1] == 1:
        return [(0, N - 3), (1, N - 2), (2, N), (0, N)]
    od_bef = [i for i in range(e + 1, p1, 2) if s[i] == 1]
    if od_bef:
        u0 = od_bef[0]
        if not any(s[i] == 1 for i in range(e + 2, u0, 2)):
            return [(0, N - 4), (2, u0), (1, N - 2), (2, N), (0, N)]
        return ([(0, alpha - 1)] if alpha - 1 > E else []) + [
            (2, u0), (1, N - 2), (0, N - 1), (2, N), (0, N)
        ]
    if p1 == q1 and not any(s[i] == 1 for i in range(e + 2, q1, 2)):
        return [(0, N - 4), (1, E + 1), (0, N - 3), (2, q1),
                (0, N - 2), (1, N - 1), (0, N - 1), (2, N), (0, N)]
    return None


def layer2_dir(s):
    """Apply the 15 hand-proved Layer-2 theorems in orientation s (assuming s in R)."""
    N, evp, odp = peaks(s)
    if not odp:
        return None
    e, E = evp[0], evp[-1]
    q1, qk = odp[0], odp[-1]
    lo1 = [i for i in range(3, e, 2) if s[i] == 1]
    ro1 = [i for i in range(E + 1, N - 1, 2) if s[i] == 1]
    if not lo1 or not ro1 or s[e - 1] != 1 or s[E + 1] != 1 or s[3] != 0 or s[N - 3] != 0:
        return None
    l1 = lo1[0]
    fin = [(0, N - 1), (2, N), (0, N)]
    mod_tail = max((s[i] for i in range(qk + 2, E, 2)), default=0)

    # Theorems 1 & 2: E-Reach and E-Reach-Super -> (E, E, e, 7) -> exit_from_EEe
    ex_e = exit_from_EEe(s)
    if ex_e is not None:
        if s[E - 1] == 1:
            w = exec_program(s, e - 1, [(1, E - 1), (2, e), (0, E)] + ex_e)
            assert w
            return 'E-Reach-direct', w
        for g in evp:
            if not (e <= g <= qk - 3) or s[g + 1] != 0:
                continue
            if s[g + 2] == 2:
                w = exec_program(s, g - 1, [(1, qk), (2, e - 1), (1, E), (0, E)] + ex_e)
                assert w
                return 'E-Reach-2', w
            for u in range(qk, E, 2):
                if s[u] < 1:
                    continue
                mev = max((s[i] for i in range(u + 1, E, 2)), default=0)
                if s[g + 2] == 1 and mev <= 1:
                    w = exec_program(s, g - 1, [(1, u), (2, e - 1), (1, E), (0, E)] + ex_e)
                    assert w
                    return 'E-Reach-1', w
                if s[g + 2] == 0 and mev == 0:
                    w = exec_program(s, g - 1, [(1, u), (2, e - 1), (1, E - 1), (0, E)] + ex_e)
                    assert w
                    return 'E-Reach-0', w
        # Theorem 2 (E-Reach-Super): first nonzero m in (g, qk) is even
        for g in evp:
            if not (e <= g < qk):
                continue
            nz = [i for i in range(g + 1, qk) if s[i] > 0]
            if not nz or nz[0] % 2 != 0:
                continue
            m = nz[0]
            for u in range(qk + 2, E, 2):
                if s[u] != 1:
                    continue
                mev = max((s[i] for i in range(u + 1, E, 2)), default=0)
                if mev <= s[m]:
                    prog = [(1, u - 1)]
                    if m - 2 > g:
                        prog.append((0, m - 2))
                    prog += [(2, e - 1), (1, E), (0, E)] + ex_e
                    w = exec_program(s, g - 1, prog)
                    assert w
                    return 'E-Reach-Super', w

    # Theorem 3: Z0 -- (qk, E) all zeros
    if not any(s[i] > 0 for i in range(qk + 1, E)):
        w = exec_program(s, qk, [(2, qk - 1), (0, E - 1), (1, N - 3), (0, E + 1), (2, E)] + fin)
        assert w
        return 'Z0', w

    # Theorem 4: Z1-q1 -- M_od(qk, E) <= s[q1-1] and R-Exit(q1)
    if mod_tail <= s[q1 - 1]:
        ex = r_exit_odd(s, q1)
        if ex is not None:
            w = exec_program(s, qk - 1, [(1, e - 1), (2, q1 - 1), (0, E), (1, N - 3)] + ex)
            assert w
            return 'Z1-q1', w

    # Theorem 5: Q-step-all -- odd peak qi with s[qi-2] >= 1, s[qi-1] = M_od(qk, E), R-Exit(qi)
    for qi in odp:
        if s[qi - 2] >= 1 and s[qi - 1] == mod_tail:
            ex = r_exit_odd(s, qi)
            if ex is not None:
                w = exec_program(s, qk, [(2, qi - 2), (0, qk + 1), (1, e), (0, E), (1, N - 3)] + ex)
                assert w
                return 'Q-step-all', w

    # Theorems 6 & 7: G-Zero and G-Zero-Universal -- even peak g in (qk, E) with M_od(g, E) = 0
    for g in evp:
        if not (qk < g < E):
            continue
        if any(s[i] > 0 for i in range(g + 1, E, 2)):
            continue
        if g == E - 2:
            w = exec_program(s, E - 3, [(1, qk), (2, e - 2), (1, N - 3)] + fin)
            assert w
            return 'G-adj', w
        for gp in evp:
            if qk < gp <= g and s[gp - 1] == 1:
                w = exec_program(s, g - 1, [(1, gp - 1), (2, e - 2), (0, E), (1, N - 3)] + fin)
                assert w
                return 'G-zero-v2', w
        mev_gE = max((s[i] for i in range(g + 2, E, 2)), default=0)
        if mev_gE <= 1:
            for b in range(qk, g, 2):
                if s[b] >= 1 and s[b + 1] >= mev_gE:
                    w = exec_program(s, g - 1, [(1, b), (2, e - 2), (0, E), (1, N - 3)] + fin)
                    assert w
                    return 'G-zero-v1', w
        # Theorem 7 (G-Zero-Universal): handles remaining Obstruction X (g <= E - 4, s[g-1] = 0)
        if l1 == e - 1 and s[g - 1] == 0:
            w = exec_program(s, g - 1, [(1, g - 2), (2, e - 3), (0, E), (1, N - 3)] + fin)
            assert w
            return 'GZ-L1', w
        mev_qkg = max((s[i] for i in range(qk + 1, g, 2)), default=0)
        mod_qkg = max((s[i] for i in range(qk + 2, g, 2)), default=0)
        if mev_qkg <= s[g + 2] and (s[e - 3] == 1 or mod_qkg == 0):
            w = exec_program(s, g - 1, [(1, qk), (2, e - 3), (1, g), (0, E), (1, N - 3)] + fin)
            assert w
            return 'GZ-Q', w
        if l1 <= e - 5 and s[e - 3] == 0 and mod_qkg == 1:
            u = max(i for i in range(qk + 2, g, 2) if s[i] == 1)
            if u <= g - 3:
                mev_ug = max((s[i] for i in range(u + 1, g, 2)), default=0)
                evs_after = [i for i in range(g + 2, E, 2) if s[i] >= 1]
                m = evs_after[0] if evs_after else g + 2
                if mev_ug <= s[m]:
                    prog = [(1, u - 1)]
                    if m > g + 2:
                        prog.append((0, m - 2))
                    prog += [(2, e - 4), (1, g), (0, E), (1, N - 3)] + fin
                    w = exec_program(s, g - 1, prog)
                    assert w
                    return 'GZ-U', w
        if mev_gE <= 1:
            for v in range(qk - 1, g + 1, 2):
                if v < e:
                    continue
                if s[v] >= mev_gE and ((l1 <= e - 3 and s[v + 1] == 1) or (l1 == e - 1 and s[v + 1] == 0)):
                    w = exec_program(s, g - 1, [(1, v), (0, E - 2), (2, e - 2), (1, N - 3)] + fin)
                    assert w
                    return 'GZ-V', w

    mev_eq1 = max((s[i] for i in range(e + 2, q1, 2)), default=0)
    mod_eq1 = max((s[i] for i in range(e + 1, q1, 2)), default=0)
    mev_eqk = max((s[i] for i in range(e + 2, qk, 2)), default=0)

    # Theorem 8: M-Bridge (q1 < qk)
    if q1 < qk and E - 2 > qk and mev_eq1 <= s[E - 2] and mod_eq1 <= s[e + 1] and mev_eqk == s[E - 1]:
        ex = r_exit_odd(s, qk)
        if ex is not None:
            w = exec_program(s, 1, [(1, e - 2), (2, e - 1), (0, E - 2), (1, q1 - 1), (2, qk - 1), (1, N - 3)] + ex)
            assert w
            return 'M-Bridge', w

    # Theorem 9: Q-Step-E3
    if (qk == E - 3 and s[E - 2] == 1 and s[E - 1] == 0 and s[e + 1] == 0
            and mev_eqk == 1 and mod_eq1 == 0 and mev_eq1 == 1):
        m = max(i for i in range(e + 2, q1, 2) if s[i] == 1)
        tail = [(2, m - 1)] if m - 1 > e + 1 else []
        if m == q1 - 1:
            end = [(0, N - 3), (1, N - 1)] + fin
        else:
            end = [(0, N - 4), (2, q1), (0, N - 2), (1, N - 1)] + fin
        w = exec_program(s, e - 1, [(1, qk), (2, e - 1), (0, qk), (1, E - 1)] + tail + end)
        assert w
        return 'Q-Step-E3', w

    # Theorem 10: E1-Skip (s[e+1] = 1)
    if s[e + 1] == 1:
        for g in evp:
            if not (e <= g < qk):
                continue
            mev_gE = max((s[i] for i in range(g + 2, E, 2)), default=0)
            if mev_gE <= 1 and mev_gE == s[qk + 1]:
                ex1 = r_exit_odd(s, e + 1)
                if ex1 is not None:
                    w = exec_program(s, g - 1, [(1, qk), (2, e), (0, E - 1), (1, N - 3)] + ex1)
                    assert w
                    return 'E1-Skip-a', w
                if mev_eq1 <= 1 and s[q1 - 1] == 1:
                    w = exec_program(s, g - 1, [(1, qk), (2, e), (0, E - 1), (1, E + 1),
                                                (2, q1 - 1), (0, N - 3), (1, N - 1)] + fin)
                    assert w
                    return 'E1-Skip-b', w

    # Theorem 11: E2-Q1
    if E - 2 > q1 and mev_eq1 == s[E - 1] and mod_eq1 <= s[e + 1]:
        ex = r_exit_odd(s, q1)
        if ex is not None:
            w = exec_program(s, 1, [(1, e - 2), (2, e - 1), (0, E - 2), (2, q1 - 1), (1, N - 3)] + ex)
            assert w
            return 'E2-Q1', w

    # Theorem 12: E3-U
    if qk == E - 3 and s[E - 2] == 1 and s[E - 1] == 0 and s[e + 1] == 0 and mev_eqk == 1:
        nz = [i for i in range(e + 1, q1) if s[i] > 0]
        if nz and nz[0] % 2 == 1:
            u = nz[0]
            ex = r_exit_odd(s, u)
            if ex is not None:
                w = exec_program(s, e - 1, [(1, qk), (2, e - 1), (0, E - 2), (2, u - 1), (1, N - 3)] + ex)
                assert w
                return 'E3-U', w

    # Theorem 13: G-Bridge (s[e+1] = 1)
    if s[e + 1] == 1:
        ex1 = r_exit_odd(s, e + 1)
        if ex1 is not None:
            for gp in evp:
                if not (qk < gp < E):
                    continue
                for g1 in evp:
                    if not (e <= g1 <= qk - 3) or s[g1 + 1] != 0:
                        continue
                    for u in range(qk, gp, 2):
                        if s[u] < 1:
                            continue
                        mev_ugp = max((s[i] for i in range(u + 1, gp, 2)), default=0)
                        if s[g1 + 2] == 2 or (s[g1 + 2] <= 1 and mev_ugp == s[g1 + 2]):
                            w = exec_program(s, g1 - 1, [(1, u), (2, e - 1), (1, gp), (0, E), (1, N - 3)] + ex1)
                            assert w
                            return 'G-Bridge', w

    # Theorem 14: Q2-Zip
    if q1 < qk and s[q1 - 1] == 1 and qk >= q1 + 4 and E == qk + 5:
        if (not any(s[i] > 0 for i in range(q1 + 1, qk))
                and max((s[i] for i in range(e + 2, qk + 2, 2)), default=0) == 1
                and s[qk + 1] == 0 and s[qk + 2] == 1 and s[qk + 3] == 0 and s[qk + 4] == 0):
            w = exec_program(s, e - 1, [
                (2, e - 2), (1, q1 - 2), (0, qk + 1), (2, q1 + 1),
                (1, qk - 1), (2, qk + 1), (1, N - 4), (2, E)
            ] + fin)
            assert w
            return 'Q2-Zip', w

    # Theorem 15: Q-G-N3
    for q in odp:
        if q >= qk:
            continue
        for g in evp:
            if not (q < g < qk) or s[g + 1] != 1:
                continue
            if any(s[i] > 0 for i in range(q + 1, g, 2)):
                continue
            mod_qg = max((s[i] for i in range(q + 2, g, 2)), default=0)
            if mod_qg == s[q - 1] and mod_qg == s[E - 1]:
                w = exec_program(s, q - 1, [
                    (2, q - 2), (0, g - 1), (1, E - 2), (2, g),
                    (0, N - 3), (1, N - 2), (2, N), (0, N)
                ])
                assert w
                return 'Q-G-N3', w

    return None


# ----------------------------------------------------------------------------
# Public API
# ----------------------------------------------------------------------------
def solve_lemma_C(s):
    """Return (orientation, branch, word) with orientation in {'F','R'}; the word is
    verified on s (if 'F') or on s[::-1] (if 'R').  Returns None if no proved branch
    applies (which is inevitable on the counterexample family s(W_L, W_R) for N >= 26)."""
    s = tuple(s)
    for d, ss in (('F', s), ('R', s[::-1])):
        r = layer1_dir(ss)
        if r:
            return d, r[0], r[1]
    for d, ss in (('F', s), ('R', s[::-1])):
        r = layer2_dir(ss)
        if r:
            return d, r[0], r[1]
    return None


if __name__ == '__main__':
    tot = bad = 0
    for N in range(8, int(sys.argv[1]) + 1 if len(sys.argv) > 1 else 19, 2):
        for s in lib.hard_patterns(N):
            if s[::-1] < s or not is_regime3(s):
                continue
            tot += 1
            r = solve_lemma_C(s)
            if r is None:
                bad += 1
                continue
            d, br, w = r
            lib.verify_word(s if d == 'F' else s[::-1], w, directed=True)
        print('N<=%d regime-III classes: %d, uncovered: %d' % (N, tot, bad), flush=True)
