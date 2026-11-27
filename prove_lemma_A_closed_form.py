import os, sys, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from itertools import product
import op1_lib as lib

def exec_from_EE1(s, E, phases):
    sc = lib.Sched(s, E - 1, directed=True)
    sc.go(1, E)
    assert sc.t == (E, E, 1, 7)
    for cur, tgt in phases:
        while sc.t[cur] < tgt:
            tpar = (sc.t[cur] + 1) % 2
            l = next(l for l, rs in lib.RULE.items() if (cur, tpar) in rs)
            nxt = lib.step(s, sc.t, l, directed=True)
            if nxt is None:
                return None
            sc.t = nxt
            sc.word += l
    try:
        lib.verify_word(s, sc.word, directed=True)
        return sc.word
    except AssertionError:
        return None

def wing_rank(w):
    """
    Closed-form rank in {0, 1, 2, 3, 4, 5, 6} for any binary wing `w` (indexed outer-to-inner):
      0: no even 1
      1: has even 1, no odd 1
      2: has both, no odd 1 after first even 1 f1
      3: has odd 1 before & after f1, and w[f1 + 1] == 1
      4: Light Reduced Wing: w[f1 + 1] == 0, no even 1 in (f1, last_odd_1)
      5: Heavy Reduced Wing: w[f1 + 1] == 0, exists even 1 f2 in (f1, last_odd_1)
      6: no odd 1 before f1
    """
    ev1 = [i for i in range(0, len(w), 2) if w[i] == 1]
    od1 = [i for i in range(1, len(w), 2) if w[i] == 1]
    if not ev1: return 0
    if not od1: return 1
    f1 = ev1[0]
    if od1[0] > f1: return 6
    if od1[-1] < f1: return 2
    if w[f1 + 1] == 1: return 3
    if len(ev1) >= 2 and ev1[1] < od1[-1]: return 5
    return 4

def reach_e0(E, e0, r1, k1, evR=()):
    """Reaches a state from which `[(1, tgt_b), (2, f1)]` (`tgt_b >= r1` odd 1 in `[r1, mu)`) ALWAYS lands at `(r1, tgt_b, f1, 7)`!"""
    if e0 == E:
        if r1 == E + 1:
            return []
        return [(0, r1 - 2), (2, k1), (1, r1 - 1)]
    if r1 == e0 + 1 and k1 >= 5:
        ev_bef = [i for i in evR if i < e0]
        e_prev = ev_bef[-1] if ev_bef else E
        base = [] if e_prev == E else [(1, e_prev), (0, e_prev)]
        if e0 == e_prev + 2:
            return base + [(0, e0 - 1), (2, k1)]
        return base + [(1, e0 - 2), (0, e0 - 1), (2, k1)]
    ph = [(1, e0), (0, e0)]
    if r1 == e0 + 1:
        ph += [(1, r1), (2, k1)]
    else:
        ph += [(0, r1 - 2), (2, k1), (1, r1 - 1)]
    return ph

def reach_mu_phase1(s, E, k1, f1, e0, r1, q1, mu, evR=(), adv_t_next=None):
    ph = reach_e0(E, e0, r1, k1, evR)
    ph += [(1, q1), (2, f1)]
    if q1 == mu - 1:
        ph += [(0, mu)]
    elif adv_t_next is not None:
        if mu - q1 == 3:
            ph += [(0, mu - 1), (1, mu - 1)]
        else:
            ph += [(0, mu - 2), (1, mu - 1), (0, mu - 1)]
        ph += [(2, adv_t_next - 1), (0, mu)]
    else:
        ph += [(0, mu - 1), (1, mu), (0, mu)]
    return ph

def reach_q1_sync_f1_zero_gap(E, e0, k1, f1, q1):
    """When `r1 == q1`, reaches `(q1, q1, f1, 7)` unconditionally!"""
    if e0 == E:
        if q1 == E + 1:
            return [(1, q1), (2, f1)]
        return [(1, q1 - 1), (0, q1), (1, q1), (2, f1)]
    else:
        if q1 == e0 + 1:
            return [(1, e0), (0, e0), (0, q1), (1, q1), (2, f1)]
        return [(1, e0), (0, e0), (0, q1 - 2), (2, k1), (1, q1 - 1), (1, q1), (0, q1), (2, f1)]

def finish_from_lam_odd_c(s, E, N, e, lam, alpha, ph_to_lam_p, p_cur):
    """Finishes from `(lam, lam, p_cur, 3 or 7)` where `p_cur < e` is an ODD 1."""
    g2 = next(i for i in range(p_cur + 1, e + 1, 2) if s[i] >= 1)
    if g2 < e:
        fin = [(1, alpha), (2, g2), (0, N - 1), (2, N), (0, N)] if alpha == N - 3 else [(1, alpha), (2, g2), (0, N - 2), (1, N - 1), (0, N - 1), (2, N), (0, N)]
        return exec_from_EE1(s, E, ph_to_lam_p + fin)
    t2 = max(i for i in range(p_cur, e, 2) if s[i] == 1)
    if t2 == p_cur or alpha == N - 3:
        return exec_from_EE1(s, E, ph_to_lam_p + [(1, N - 3), (2, e), (0, N - 1), (2, N), (0, N)])
    if s[lam + 1] == 0:
        return exec_from_EE1(s, E, ph_to_lam_p + [(1, alpha), (2, t2), (1, N - 3), (2, e), (0, N - 1), (2, N), (0, N)])
    return None

def leapfrog_from_mu_f2(s, E, N, e, mu, lam, alpha, odR, evR, f2, p2, ph_to_mu_f2):
    """Finishes from `(mu, mu, f2, 3 or 7)` OR `(mu, mu, f2 - 1, 7)` when `od_in_mu_lam` is non-empty!"""
    ph_lam_p2 = ph_to_mu_f2 + [(0, lam - 1), (2, p2), (1, lam)]
    w = finish_from_lam_odd_c(s, E, N, e, lam, alpha, ph_lam_p2, p2)
    if w:
        return w
    # Remaining subcase: `g2 == e`, `t2 > p2`, `s[lam + 1] == 1`, `alpha <= N - 5`!
    t2 = max(i for i in range(p2, e, 2) if s[i] == 1)
    q_lam = max(i for i in odR if mu < i < lam)
    v_after = next(i for i in evR if i > q_lam)
    e_star = max(i for i in evR if mu <= i < q_lam)
    # If `e_star > mu` and `[i for i in odR if mu < i < e_star]` is non-empty, first leapfrog `(mu, mu, f2) -> (e_star, e_star, p2, 7)`!
    od_bef_estar = [i for i in odR if mu < i < e_star]
    if e_star > mu and not od_bef_estar:
        # `(mu, e_star]` has NO odd 1s! Advance `(mu, mu, f2) -> (e_star, e_star, ...)`? Even simpler: `(0, v_after - 1)` already crosses `e_star`!
        pass
    ph = ph_to_mu_f2 + [(0, v_after - 1), (2, p2)]
    if mu + 1 == v_after - 1:
        if v_after == lam:
            return finish_from_lam_odd_c(s, E, N, e, lam, alpha, ph + [(2, t2), (0, lam)], t2)
        return finish_from_lam_odd_c(s, E, N, e, lam, alpha, ph + [(2, t2 - 2), (0, v_after), (0, lam - 1), (1, lam)], t2)
    if q_lam == mu + 1:
        if v_after == lam:
            return finish_from_lam_odd_c(s, E, N, e, lam, alpha, ph + [(2, t2), (1, lam)], t2)
        return finish_from_lam_odd_c(s, E, N, e, lam, alpha, ph + [(2, t2 - 2), (1, v_after), (0, lam - 1), (1, lam)], t2)
    if v_after < lam:
        if t2 == p2 + 2:
            w2 = finish_from_lam_odd_c(s, E, N, e, lam, alpha, ph + [(1, v_after), (0, lam - 1), (1, lam)], t2)
            if w2: return w2
        else:
            # `(1, q_lam)` -> `(v_after, q_lam, p2, 7)`; since `(v_after, lam)` has NO odd 1s, `v_after + 1 <= lam - 1` has `s[v_after + 1] == 0`!
            # If `lam >= v_after + 4`, `lam - 3 >= v_after + 1` is ODD `0` and `lam - 2` is EVEN `0`? Wait: `(v_after, lam)` might have even 1s!
            # Instead, at `(v_after, q_lam, p2, 7)`, `(2, t2)` pushes `A: v_after -> v_after + 1 (0, ODD WITNESSED)` -> `(v_after + 1, q_lam, t2, 7)`!
            # If `(v_after, lam)` has NO even 1s, IMPOSSIBLE since `lam` IS an even 1 (`v_after < lam`), so `B` needs `A` at `lam`!
            # How? `(2, t2 - 2)` -> `(v_after + 1, q_lam, t2 - 2, 7)`, `(0, lam - 1)`? Needs `B` even `1`!
            # Do `(1, v_after)` BEFORE `(2, ...)` -> `(v_after, v_after, p2, 7)`! Now `(v_after, lam)` has NO odd 1s:
            # `[(0, lam - 1), (2, t2), (1, lam)]`: `(0, lam - 1)` pushes `C: p2 -> p2 + 1 (0)` on first `y`, `B = v_after (1)` supports all even 1s in `(v_after, lam)` -> `(lam - 1, v_after, p2 + 1, 7)`! Wait: `(2, t2)` has `B = v_after` -> first `z` pushes `B -> v_after + 1 (0)` which can't support odd `1`s in `(p2 + 1, t2)`!
            # So instead, BEFORE `(1, v_after)`, advance `C` to `t2 - 2` while `B = q_lam (1)` AND `A` is `< v_after`!
            if v_after - q_lam >= 3:
                # `v_after - 2 >= q_lam + 1` EVEN `0`, `v_after - 1` ODD `0`!
                w2 = finish_from_lam_odd_c(s, E, N, e, lam, alpha, ph_to_mu_f2 + [(0, v_after - 3), (2, p2), (1, q_lam), (2, t2 - 2), (1, v_after), (0, lam - 1), (1, lam)], t2)
                if w2: return w2
            elif od_bef_estar:
                ph_es = ph_to_mu_f2 + ([(0, e_star - 1), (2, p2), (1, e_star)] if s[e_star - 1] == 0 else [(0, e_star - 1), (2, p2), (1, e_star - 1), (0, e_star)])
                p3 = next(i for i in range(p2 + 2, e, 2) if s[i] == 1)
                w2 = finish_from_lam_odd_c(s, E, N, e, lam, alpha, ph_es + [(1, q_lam), (2, t2 - 2), (0, v_after), (0, lam - 1), (1, lam)], t2)
                if w2: return w2
    if v_after == lam:
        if e_star == mu and lam - q_lam >= 5:
            ph2 = ph_to_mu_f2 + [(0, lam - 3), (2, p2), (1, q_lam), (2, t2), (1, lam)]
            w2 = finish_from_lam_odd_c(s, E, N, e, lam, alpha, ph2, t2)
            if w2: return w2
        if e_star > mu and od_bef_estar:
            ph_es = ph_to_mu_f2 + ([(0, e_star - 1), (2, p2), (1, e_star)] if s[e_star - 1] == 0 else [(0, e_star - 1), (2, p2), (1, e_star - 1), (0, e_star)])
            if lam - q_lam >= 5:
                w2 = finish_from_lam_odd_c(s, E, N, e, lam, alpha, ph_es + [(1, q_lam), (0, lam - 3), (2, t2), (1, lam)], t2)
                if w2: return w2
            w2 = finish_from_lam_odd_c(s, E, N, e, lam, alpha, ph_es + [(1, q_lam), (2, t2 - 2), (0, lam - 1), (1, lam)], t2)
            if w2: return w2
        # `e_star >= mu`, `not od_bef_estar` (`(mu, e_star]` has NO odd 1s!), `lam - q_lam == 3` (`q_lam == lam - 3`):
        od_bef_qlam = [i for i in odR if e_star < i < q_lam]
        if e_star == mu:
            ph2 = ph_to_mu_f2 + [(0, q_lam), (2, p2), (1, q_lam), (2, t2), (1, lam)]
            w2 = finish_from_lam_odd_c(s, E, N, e, lam, alpha, ph2, t2)
            if w2: return w2
        elif od_bef_qlam:
            # Reach `(q_lam, q_lam, p2, 7)` or `(lam, lam, t2, 3)`!
            u_prev = od_bef_qlam[-1]
            if q_lam == u_prev + 2:
                ph2 = ph_to_mu_f2 + [(0, u_prev), (2, p2), (1, u_prev), (0, q_lam - 1), (1, q_lam), (2, t2), (1, lam)]
            else:
                ph2 = ph_to_mu_f2 + [(0, q_lam - 2), (2, p2), (1, q_lam), (2, t2), (1, lam)]
            w2 = finish_from_lam_odd_c(s, E, N, e, lam, alpha, ph2, t2)
            if w2: return w2
        else:
            # `e_star > mu`, `not od_bef_estar`, `not od_bef_qlam`, `q_lam == lam - 3`:
            if s[f2 + 1] == 0:
                ph_es = ph_to_mu_f2 + [(1, e_star), (0, e_star)]
                if q_lam == e_star + 1:
                    ph2 = ph_es + [(0, q_lam), (1, q_lam), (2, p2), (2, t2 - 2), (0, lam - 1), (1, lam)]
                else:
                    ph2 = ph_es + [(0, q_lam - 2), (2, p2), (1, q_lam), (2, t2), (1, lam)]
                w2 = finish_from_lam_odd_c(s, E, N, e, lam, alpha, ph2, t2)
                if w2: return w2
            else:
                pre_es = [(0, mu + 1), (1, mu + 1), (0, e_star)] if e_star == mu + 2 else [(0, e_star - 1), (1, e_star)]
                if q_lam >= e_star + 3:
                    ph2 = ph_to_mu_f2 + pre_es + [(1, q_lam - 2), (0, q_lam - 2), (1, q_lam), (2, t2), (1, lam)]
                    w2 = finish_from_lam_odd_c(s, E, N, e, lam, alpha, ph2, t2)
                    if w2: return w2
                # Replace final `f2 -> mu` step of `ph_to_mu_f2` so we arrive at `(e_star, e_star, f2, 3)` instead of `(mu, mu, f2, 7)`!
                if ph_to_mu_f2[-2:] == [(2, f2), (0, mu)]:
                    ph_es_f2 = ph_to_mu_f2[:-2] + [(2, f2 - 1), (1, e_star - 1), (0, e_star)]
                else:
                    ph_es_f2 = ph_to_mu_f2[:-2] + [(1, e_star - 1), (0, e_star)]
                ph2 = ph_es_f2 + [(0, q_lam), (1, q_lam), (2, t2 - 2), (0, lam - 1), (1, lam)]
                w2 = finish_from_lam_odd_c(s, E, N, e, lam, alpha, ph2, t2)
                if w2: return w2
    return None

def try_closed_form_dir(s):
    N = len(s) - 1
    ev_peaks = [i for i in range(2, N - 1, 2) if s[i] == 2]
    e, E = ev_peaks[0], ev_peaks[-1]
    if any(s[i] == 2 for i in range(3, e, 2)) or any(s[i] == 2 for i in range(E + 1, N - 1, 2)):
        return None
    L = s[2:e]
    R = s[E + 1:N - 1][::-1]
    rL, rR = wing_rank(L), wing_rank(R)
    if rL == 0 and rR == 0:
        return None

    evL = [i for i in range(2, e, 2) if s[i] == 1]
    odL = [i for i in range(3, e, 2) if s[i] == 1]
    evR = [i for i in range(E + 2, N - 1, 2) if s[i] == 1]
    odR = [i for i in range(E + 1, N - 1, 2) if s[i] == 1]

    # THEOREM A1.1
    if not evR and evL:
        f = evL[0]
        if not odR:
            return exec_from_EE1(s, E, [(1, N - 2), (0, N - 1), (2, N), (0, N)])
        alpha = odR[-1]
        if alpha == N - 3:
            return exec_from_EE1(s, E, [(1, alpha), (2, f), (0, N - 1), (2, N), (0, N)])
        return exec_from_EE1(s, E, [(1, alpha), (2, f), (0, N - 2), (1, N - 1), (0, N - 1), (2, N), (0, N)])

    if not evR:
        return None
    lam = evR[-1]

    # THEOREM A1.2
    if not odR:
        if s[N - 2] == 1:
            return exec_from_EE1(s, E, [(1, N - 2), (0, N - 1), (2, N), (0, N)])
        if s[2] == 0:
            return exec_from_EE1(s, E, [(1, lam), (0, N - 2), (1, N - 1), (0, N - 1), (2, N), (0, N)])
    if not odL and evL and s[N - 2] == 1:
        f = evL[0]
        return exec_from_EE1(s, E, [(1, N - 3), (2, f), (0, N - 1), (2, N), (0, N)])

    if not (evL and odL and evR and odR):
        return None

    f1 = evL[0]
    k1 = odL[0]

    # THEOREM A2 (rL == 6)
    if rL == 6:
        if lam == N - 2:
            return exec_from_EE1(s, E, [(1, N - 3), (2, f1), (0, N - 1), (2, N), (0, N)])
        od_aft_lam = [i for i in odR if i > lam]
        if not od_aft_lam:
            return exec_from_EE1(s, E, [(1, lam - 1), (2, f1), (0, N - 2), (1, N - 1), (0, N - 1), (2, N), (0, N)])
        alpha = od_aft_lam[-1]
        p1 = next(i for i in odL if i > f1)
        b_end = N - 1 if alpha == N - 3 else N - 3
        return exec_from_EE1(s, E, [(1, lam - 1), (2, f1), (0, alpha), (2, p1), (1, b_end), (0, N - 1), (2, N), (0, N)])

    if rR == 6:
        return None

    alpha = odR[-1]

    # THEOREM A3 (rR == 2, rL >= 2)
    if rR == 2:
        ev_bef_lam = [i for i in evR if i < lam]
        e0_prev = ev_bef_lam[-1] if ev_bef_lam else E
        if e0_prev == E:
            ph = ([(0, E + 1), (1, E + 1)] if lam == E + 2 else [(1, lam - 2), (0, lam - 1), (1, lam - 1)]) + [(2, k1), (0, lam)]
        else:
            ph = [(1, e0_prev), (0, e0_prev), (0, lam - 1), (2, k1), (1, lam)]
        fin = [(1, alpha), (2, f1), (0, N - 1), (2, N), (0, N)] if alpha == N - 3 else [(1, alpha), (2, f1), (0, N - 2), (1, N - 1), (0, N - 1), (2, N), (0, N)]
        return exec_from_EE1(s, E, ph + fin)

    if rL == 2:
        return None

    # THEOREM A4 (rR == 3, rL >= 3)
    if rR == 3:
        p1 = next(i for i in odL if i > f1)
        b_end = N - 1 if alpha == N - 3 else N - 3
        return exec_from_EE1(s, E, [(1, lam - 1), (2, f1), (0, lam), (0, alpha), (2, p1), (1, b_end), (0, N - 1), (2, N), (0, N)])

    if rL == 3:
        return None

    # REDUCED WINGS (rL, rR in {4, 5})
    r1 = odR[0]
    mu = next(i for i in evR if i > r1)
    q1 = max(i for i in odR if i < mu)
    ev_bef_r1 = [i for i in evR if i < r1]
    e0 = ev_bef_r1[-1] if ev_bef_r1 else E
    b_end = N - 1 if alpha == N - 3 else N - 3

    def finish_after_lam_even_c0(ph_to_lam, c0):
        u2 = next(i for i in odR if i > lam)
        if s[c0] == 1:
            p_nx = next(i for i in odL if i > c0)
            return exec_from_EE1(s, E, ph_to_lam + [(0, alpha), (2, p_nx), (1, b_end), (0, N - 1), (2, N), (0, N)])
        od_a = [i for i in odL if i > c0]
        ev_a = [i for i in evL if i > c0]
        if od_a and (not ev_a or od_a[0] < ev_a[0]):
            k_nx = od_a[0]
            gL = ev_a[0] if ev_a else e
            tL = max(i for i in od_a if i < gL)
            if u2 == lam + 1:
                if gL < e:
                    fin = [(1, alpha), (2, gL), (0, N - 1), (2, N), (0, N)] if alpha == N - 3 else [(1, alpha), (2, gL), (0, N - 2), (1, N - 1), (0, N - 1), (2, N), (0, N)]
                    return exec_from_EE1(s, E, ph_to_lam + [(1, u2), (2, k_nx)] + fin)
                return exec_from_EE1(s, E, ph_to_lam + [(1, u2), (2, tL), (1, N - 3), (2, e), (0, N - 1), (2, N), (0, N)])
            else:
                if tL == k_nx and gL < e:
                    fin = [(1, alpha), (2, gL), (0, N - 1), (2, N), (0, N)] if alpha == N - 3 else [(1, alpha), (2, gL), (0, N - 2), (1, N - 1), (0, N - 1), (2, N), (0, N)]
                    return exec_from_EE1(s, E, ph_to_lam + [(0, u2 - 2), (2, k_nx), (1, u2 - 1)] + fin)
                if tL == k_nx and gL == e:
                    return exec_from_EE1(s, E, ph_to_lam + [(0, u2 - 2), (2, k_nx), (1, N - 3), (2, e), (0, N - 1), (2, N), (0, N)])
                return exec_from_EE1(s, E, ph_to_lam + [(0, u2 - 2), (2, k_nx), (1, u2), (0, u2), (2, tL), (1, N - 3), (2, gL), (0, N - 1), (2, N), (0, N)])
        else:
            f_nx = ev_a[0]
            p_nx = next(i for i in od_a if i > f_nx)
            gL = next(i for i in range(p_nx + 1, e + 1, 2) if s[i] >= 1)
            tL = max(i for i in range(f_nx + 1, gL, 2) if s[i] == 1)
            if u2 == lam + 1:
                return exec_from_EE1(s, E, ph_to_lam + [(1, u2), (2, f_nx), (2, tL), (1, N - 3), (2, gL), (0, N - 1), (2, N), (0, N)])
            else:
                if f_nx == c0 + 2:
                    return exec_from_EE1(s, E, ph_to_lam + [(0, u2 - 2), (1, u2 - 1), (0, alpha), (2, p_nx), (1, b_end), (0, N - 1), (2, N), (0, N)])
                return exec_from_EE1(s, E, ph_to_lam + [(0, u2 - 2), (1, u2 - 1), (0, u2), (1, u2), (2, f_nx), (2, tL), (1, N - 3), (2, gL), (0, N - 1), (2, N), (0, N)])

    # THEOREM A6 (Light R: mu == lam, works for ANY rL in {4, 5}!)
    if mu == lam:
        p1 = next(i for i in odL if i > f1)
        if q1 == lam - 1:
            ph1 = reach_mu_phase1(s, E, k1, f1, e0, r1, q1, lam, evR)
            return finish_after_lam_even_c0(ph1, f1)
        ev_bef_p1 = [i for i in evL if f1 < i < p1]
        if not ev_bef_p1:
            gL_p1 = next(i for i in range(p1 + 1, e + 1, 2) if s[i] >= 1)
            t_last = max(i for i in odL if i < gL_p1)
            if t_last > p1:
                if r1 == q1:
                    ph_tl = reach_q1_sync_f1_zero_gap(E, e0, k1, f1, q1) + [(2, t_last - 1), (0, lam - 1), (1, lam)]
                else:
                    r_prev = max(i for i in odR if i < q1)
                    ph0 = reach_e0(E, e0, r1, k1, evR) + [(1, r_prev), (2, f1)]
                    if q1 == r_prev + 2:
                        ph_tl = ph0 + [(0, lam - 2), (1, q1), (2, t_last - 1), (1, lam)]
                    else:
                        ph_tl = ph0 + [(0, lam - 3), (2, p1), (1, q1), (2, t_last - 1), (1, lam)]
                w = finish_from_lam_odd_c(s, E, N, e, lam, alpha, ph_tl, t_last)
                if w: return w
            ph1 = reach_mu_phase1(s, E, k1, f1, e0, r1, q1, lam, evR, adv_t_next=p1)
            return finish_after_lam_even_c0(ph1, p1 - 1)
        else:
            ph1 = reach_mu_phase1(s, E, k1, f1, e0, r1, q1, lam, evR)
            u2 = next(i for i in odR if i > lam)
            f2_0 = ev_bef_p1[0]
            gL = next(i for i in range(p1 + 1, e + 1, 2) if s[i] >= 1)
            tL = max(i for i in range(f2_0 + 1, gL, 2) if s[i] == 1)
            pre2 = [(1, u2 - 1), (0, u2 - 1)] if u2 >= lam + 3 else []
            if f2_0 == f1 + 2:
                return exec_from_EE1(s, E, ph1 + pre2 + [(0, alpha), (2, p1), (1, b_end), (0, N - 1), (2, N), (0, N)])
            return exec_from_EE1(s, E, ph1 + pre2 + [(0, u2), (1, u2), (2, f2_0), (2, tL), (1, N - 3), (2, gL), (0, N - 1), (2, N), (0, N)])

    if rL < 5:
        return None

    # THEOREM A5 (rL == 5 and mu < lam)
    od_in_mu_lam = [i for i in odR if mu < i < lam]
    if not od_in_mu_lam:
        ph1 = reach_mu_phase1(s, E, k1, f1, e0, r1, q1, mu, evR)
        return finish_after_lam_even_c0(ph1 + [(1, lam), (0, lam)], f1 + 2)

    p2 = next(i for i in odL if i > evL[1])
    f2 = max(i for i in evL if i < p2)
    od_bef_f2 = [i for i in odL if f1 < i < f2]

    # Case A5.2a: r1 == q1
    if r1 == q1:
        ph_q1 = reach_q1_sync_f1_zero_gap(E, e0, k1, f1, q1)
        ph_mu = ph_q1 + ([(2, f2), (0, mu)] if q1 == mu - 1 else [(2, f2 - 1), (1, mu - 1), (0, mu)])
        return leapfrog_from_mu_f2(s, E, N, e, mu, lam, alpha, odR, evR, f2, p2, ph_mu)

    # Case A5.2b: r1 < q1 and od_bef_f2 non-empty
    r_prev = max(i for i in odR if i < q1)
    if od_bef_f2:
        k2 = od_bef_f2[0]
        ph0 = reach_e0(E, e0, r1, k1, evR) + [(1, r_prev), (2, f1)]
        if q1 == mu - 1:
            ph_q1 = ph0 + ([(0, q1), (1, q1)] if q1 == r_prev + 2 else [(0, q1 - 2), (2, k2), (1, q1 - 1), (1, q1), (0, q1)])
            ph_mu = ph_q1 + [(2, f2), (0, mu)]
        else:
            # `q1 <= mu - 3`: `mu - 2 >= q1 + 1` EVEN `0` and `mu - 1` ODD `0`!
            if q1 == r_prev + 2:
                ph_mu = ph0 + [(0, q1), (1, q1), (2, f2 - 1), (1, mu - 1), (0, mu)]
            elif k2 == f2 - 1:
                ph_mu = ph0 + [(0, mu - 3), (2, k2), (1, q1), (1, mu - 1), (0, mu)]
            elif evL[1] == f2:
                ph_mu = ph0 + [(0, mu - 3), (2, k2), (1, q1), (2, f2 - 1), (1, mu)]
            else:
                ph_mu = ph0 + [(0, q1 - 2), (2, k2), (1, q1 - 1), (1, q1), (0, q1), (2, f2 - 1), (1, mu - 1), (0, mu)]
        return leapfrog_from_mu_f2(s, E, N, e, mu, lam, alpha, odR, evR, f2, p2, ph_mu)

    # Case A5.2c: r1 < q1 <= mu - 3 and not od_bef_f2
    if q1 <= mu - 3:
        ph_mu = reach_e0(E, e0, r1, k1, evR) + [(1, q1), (2, f1), (0, q1), (2, f2 - 1), (1, mu - 1), (0, mu)]
        return leapfrog_from_mu_f2(s, E, N, e, mu, lam, alpha, odR, evR, f2, p2, ph_mu)

    # Case A5.2d: r1 < q1 == mu - 1 and not od_bef_f2
    u_mid = od_in_mu_lam[0]
    mu_p = max(i for i in evR if mu <= i < u_mid)
    v_mid = next(i for i in evR if i > u_mid)
    q_mid = max(i for i in odR if i < v_mid)

    def dispatch_from_vmid_f2(ph_v):
        if v_mid == lam:
            return finish_after_lam_even_c0(ph_v, f2)
        if not [i for i in odR if v_mid < i < lam]:
            if s[f2 + 1] == 0:
                return finish_after_lam_even_c0(ph_v + [(1, lam), (0, lam)], f2 + 2)
            pre_lam = [(0, v_mid + 1), (1, v_mid + 1), (0, lam)] if lam == v_mid + 2 else [(0, lam - 1), (1, lam)]
            w = finish_from_lam_odd_c(s, E, N, e, lam, alpha, ph_v + pre_lam, f2 + 1)
            if w: return w
        return leapfrog_from_mu_f2(s, E, N, e, v_mid, lam, alpha, odR, evR, f2, p2, ph_v)

    tail_f2_vmid = [(2, f2), (0, v_mid)] if q_mid == v_mid - 1 else [(2, f2 - 1), (1, v_mid), (0, v_mid)]

    if r1 == E + 1:
        ph_f1 = [(1, q_mid), (2, f1)]
    elif k1 == 3 or q_mid == mu_p + 1:
        ph_f1 = [(1, mu_p), (0, r1 - 1), (2, k1), (1, q_mid), (2, f1)]
    elif s[r1 - 1] == 1 and u_mid == q_mid:
        ph_f1 = [(1, mu_p), (0, r1 - 1), (1, u_mid - 1), (1, u_mid), (2, f1)]
    elif s[r1 - 1] == 1:
        # `e0 == r1 - 1`, `k1 >= 5`, `u_mid < q_mid`:
        # At `(e0, u_mid - 1, 3, 7)` (from `[(1, mu_p), (0, r1 - 1), (1, u_mid - 1)]`), if `u_mid == mu_p + 1` was already handled above, so `u_mid >= mu_p + 3`!
        # Reach `(mu, mu, f1, 7)` cleanly: `[(1, e0), (0, e0 - 1), (2, k1), (1, q1), (2, f1), (0, mu)]` (`e0 - 1 = r1 - 2` ODD `0`! First `x` of `(1, q1)` pushes `A: e0 - 1 -> e0 (1)` WITNESSED AT `B = e0 + 2`? No, `[(1, q1 - 1)]`? Wait: `e0 = r1 - 1` IS EVEN `1`, so `[(1, q1), (0, r1 - 2), (2, k1)]`? No, at `(E, q1 - 1, 1, 7)`? Use `[(1, e0 - 2)]`? If `e0 == E + 2`, `e0 - 2 == E` (`s[E] = 2`): `[(0, E + 1), (2, k1), (1, q1), (2, f1), (0, mu)]`! If `e0 >= E + 4`: `e_prev = max([i for i in evR if i < e0], default=E)`: `(e_prev, r1 - 1)` has NO even `1`s, so `[(1, e0), (0, r1 - 2), (2, k1)]` pushes `B: e0 -> r1 (1)` WITNESSED BY `k1 (1)` (`(r1 - 2, r1, k1, 7)`!), THEN `(0, r1 - 1)`? `y` pushes `C`! Instead `(1, r_prev)`? `x` pushes `A: r1 - 2 -> r1 - 1 = e0 (1)`! Wait: witness `A = e0 (1)` by stopping `B` at `e0 - 1`? `s[e0 - 1] = 0`! Witness `A = e0` by `[(1, mu), (0, r1 - 2), (2, k1)]` -> `(r1 - 2, mu + 1, k1)` -> only if `mu + 1`! Or from `(r1, u_mid, f1, 7)`, `[(2, p2), (1, v_mid)]`!)
        ph_vp2 = [(1, mu_p), (0, r1 - 1), (1, u_mid - 1), (1, u_mid), (2, f1), (2, p2), (1, v_mid), (0, v_mid)]
        if v_mid == lam:
            return finish_from_lam_odd_c(s, E, N, e, lam, alpha, ph_vp2, p2)
        if not [i for i in odR if v_mid < i < lam]:
            if s[p2 + 1] == 0:
                return finish_after_lam_even_c0(ph_vp2 + [(1, lam), (0, lam)], p2 + 1)
            return finish_after_lam_even_c0(ph_vp2 + [(1, lam), (0, lam)], p2 + 1)
        ev_aft_p2 = [i for i in evL if i > p2]
        if ev_aft_p2:
            g2 = ev_aft_p2[0]
            if g2 == p2 + 1:
                w = finish_after_lam_even_c0(ph_vp2 + [(1, lam), (0, lam)], g2)
                if w: return w
            v_2 = next(i for i in evR if i > v_mid)
            od_v_v2 = [i for i in odR if v_mid < i < v_2]
            if not od_v_v2:
                u_2 = next(i for i in odR if i > v_mid); v_3 = next(i for i in evR if i > u_2); q_2 = max(i for i in odR if i < v_3)
                ph_vn = ph_vp2 + ([(1, q_2), (2, g2 - 1), (1, v_3), (0, v_3)] if q_2 <= v_3 - 3 else [(1, q_2), (2, g2), (0, v_3)])
                vn = v_3
            else:
                q_2 = od_v_v2[-1]
                ph_vn = ph_vp2 + ([(1, q_2), (2, g2 - 1), (1, v_2), (0, v_2)] if q_2 <= v_2 - 3 else [(1, q_2), (2, g2), (0, v_2)])
                vn = v_2
            if vn == lam:
                return finish_after_lam_even_c0(ph_vn, g2)
            if not [i for i in odR if vn < i < lam]:
                if s[g2 + 1] == 0:
                    return finish_after_lam_even_c0(ph_vn + [(1, lam), (0, lam)], g2 + 2)
                pre_lam = [(0, vn + 1), (1, vn + 1), (0, lam)] if lam == vn + 2 else [(0, lam - 1), (1, lam)]
                return finish_from_lam_odd_c(s, E, N, e, lam, alpha, ph_vn + pre_lam, g2 + 1)
            p3_cands = [i for i in odL if i > g2]
            if p3_cands:
                p3 = p3_cands[0]; f3 = max(i for i in evL if i < p3)
                return leapfrog_from_mu_f2(s, E, N, e, vn, lam, alpha, odR, evR, f3 if f3 == g2 else g2, p3, ph_vn)
        ph_f1 = [(1, mu_p), (0, r1 - 2), (2, k1), (1, q_mid), (2, f1)]
    else:
        ph_f1 = [(1, mu_p), (0, r1 - 2), (2, k1), (1, q_mid), (2, f1)]
    return dispatch_from_vmid_f2(ph_f1 + tail_f2_vmid)

if __name__ == '__main__':
    mid = (2, 0, 0, 2, 0, 2, 0, 0, 2)
    for kL, kR in [(2, 2), (4, 4), (4, 6), (6, 6), (6, 8), (8, 8)]:
        tot = cov = 0
        for L in product((0, 1), repeat=kL):
            for R in product((0, 1), repeat=kR):
                if kL == kR and L > R: continue
                if not any(L[i]==1 for i in range(0,kL,2)) and not any(R[i]==1 for i in range(0,kR,2)):
                    continue
                s = (2, 2) + L + mid + R[::-1] + (2, 2)
                tot += 1
                if try_closed_form_dir(s) or try_closed_form_dir(s[::-1]):
                    cov += 1
        print(f"({kL}, {kR}): {cov}/{tot}, rem={tot - cov}")

    rng = random.Random(20261124)
    r_fail = []
    for _ in range(5000):
        kL = 2 * rng.randint(1, 50)
        kR = 2 * rng.randint(1, 50)
        L = tuple(rng.randint(0, 1) for _ in range(kL))
        R = tuple(rng.randint(0, 1) for _ in range(kR))
        if not any(L[i]==1 for i in range(0,kL,2)) and not any(R[i]==1 for i in range(0,kR,2)):
            L = (1,) + L[1:]
        s = (2, 2) + L + mid + R[::-1] + (2, 2)
        if not (try_closed_form_dir(s) or try_closed_form_dir(s[::-1])):
            r_fail.append((L, R))
    print(f"Random 5000 long pairs: {5000 - len(r_fail)}/5000, fails={len(r_fail)}")

    s_fail = []
    for _ in range(2000):
        k = 2 * rng.randint(2, 30)
        W = tuple(rng.randint(0, 1) for _ in range(k))
        if not any(W[i] == 1 for i in range(0, k, 2)):
            W = (1,) + W[1:]
        s = (2, 2) + W + mid + W[::-1] + (2, 2)
        if not try_closed_form_dir(s):
            s_fail.append(W)
    print(f"Symmetric 2000 W vs W pairs: {2000 - len(s_fail)}/2000, fails={len(s_fail)}")
    if s_fail:
        print("  sample sym fail:", ''.join(map(str, s_fail[0])))
