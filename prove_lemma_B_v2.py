import os, sys, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from itertools import product
import op1_lib as lib
import prove_lemma_A_closed_form as cf
from prove_binary_suffix_complete import complete_binary_suffix

_STEP_LETTER = (('x', 'y'), ('x', 'z'), ('y', 'z'))

def run_ph(s, phases, t_init):
    t = t_init; w = []
    for cur, tgt in phases:
        cur_let = _STEP_LETTER[cur]
        while t[cur] < tgt:
            nxt = lib.step(s, t, cur_let[(t[cur] + 1) & 1], directed=True)
            if nxt is None: return None, None
            w.append(cur_let[(t[cur] + 1) & 1]); t = nxt
    return t, ''.join(w)

def exec_phases(s, a0, phases):
    if not (1 <= a0 < len(s) - 1): return None
    sc = lib.Sched(s, a0, directed=True)
    t, w = run_ph(s, phases, sc.t)
    if t != (len(s) - 1, len(s) - 1, len(s) - 1, 7): return None
    full = sc.word + w
    try:
        lib.verify_word(s, full, directed=True)
        return full
    except AssertionError:
        return None

# ==============================================================================
# 1. Theorem B0: Zero-Even Wings
# ==============================================================================
def solve_B0_dir(s):
    N = len(s) - 1
    evp = [i for i in range(2, N - 1, 2) if s[i] == 2]
    e, E = evp[0], evp[-1]
    if lib.M_ev(s, 1, e) > 0 or lib.M_ev(s, E, N - 1) > 0: return None
    if not any(s[i] == 2 for i in range(E + 1, N - 1, 2)): return None
    p = max(i for i in range(1, e, 2) if s[i] == 2)
    alpha = max(i for i in range(E + 1, N - 1, 2) if s[i] >= 1)
    pref = [(2, p - 1)] if p > 1 else []
    # Wait: I(E - 1), C -> p (if p > 1: C -> p - 1 while A = E - 1 odd, then B -> alpha pushes C -> p? No: B -> E first or C -> p!)
    # In Note 6: I(E - 1), B -> E? No, Note 6: from (E, E, 1, 7) if p == 1, else I(E - 1), C -> p - 1, B -> E -> (E, E, p, 7), then B -> alpha, C -> e!
    init = ([(2, p - 1)] if p > 1 else []) + [(1, E), (1, alpha), (2, e)]
    fin = [(0, N - 1), (2, N), (0, N)] if alpha == N - 3 else [(0, N - 2), (1, N - 1), (0, N - 1), (2, N), (0, N)]
    return exec_phases(s, E - 1, init + fin)

# ==============================================================================
# 2. Common-Witness Schedule (Appendix) & Section 5 Mid-Cut
# ==============================================================================
def solve_common_witness_dir(s):
    """Runs Common-Witness on s^r and reverses the word to give a directed OP1 word for s."""
    sr = s[::-1]
    N = len(sr) - 1
    evp = [i for i in range(2, N - 1, 2) if sr[i] == 2]
    e, E = evp[0], evp[-1]
    L_cands = [i for i in range(1, e, 2) if sr[i] == 2]
    O_cands = [i for i in range(E + 1, N, 2) if sr[i] == 2]
    for L in reversed(L_cands):
        T_cands = [1] if L == 1 else L_cands
        for T in T_cands:
            if lib.M_ev(sr, 1, T) > sr[L - 1]: continue
            if lib.M_ev(sr, L, e) > sr[T + 1]: continue
            for O in O_cands:
                if lib.M_od(sr, L, e) > sr[O - 1]: continue
                if lib.M_ev(sr, O, N - 1) > sr[e + 1]: continue
                sc = lib.Sched(sr, L if T == 1 else L - 1, directed=False)
                if T > 1: sc.go(1, T)
                sc.go(2, O - 1); sc.go(0, e); sc.go(1, N - 1); sc.go(2, N); sc.go(0, N)
                w_rev = sc.word[::-1]
                try:
                    lib.verify_word(s, w_rev, directed=True)
                    return w_rev
                except AssertionError:
                    pass
    return None

def solve_sec5_dir(s):
    N = len(s) - 1
    evp = [i for i in range(2, N - 1, 2) if s[i] == 2]
    e, E = evp[0], evp[-1]
    od2_L = [i for i in range(3, e, 2) if s[i] == 2]
    od2_R = [i for i in range(E + 1, N - 1, 2) if s[i] == 2]
    if not od2_L or not od2_R: return None
    O = od2_R[0]
    if lib.M_ev(s, E, O) > s[N - 2]: return None
    for T in od2_L:
        m1 = lib.M_ev(s, 1, T)
        for P in od2_L:
            if lib.M_od(s, E, O) > s[P + 1]: continue
            m2 = max(s[i] for i in range(2, P, 2))
            for J in range(4, E, 2):
                if s[J] == m1 and s[J + 1] == m2 and lib.M_ev(s, J + 1, E) <= s[T + 1] and lib.M_od(s, J + 1, E) <= s[P - 1]:
                    w = exec_phases(s, J - 1, [(1, T), (2, P - 1), (0, E), (1, N - 2), (0, O), (2, N), (0, N)])
                    if w: return w
    return None

# ==============================================================================
# 3. Binary Suffix + Right-Lifting from (Ok, Ok, Ok, 7) and Multi-Peak Finisher
# ==============================================================================
def _finish_zero_odd_after_f(s, t_ev, p_ev, ob, f, O_star, N):
    """Universal closed-form lift when p_ev is even, ob = odd 1s in (p_ev, f) is non-empty,
    at least 2 even 1s exist in (p_ev, O_star), and NO odd 1 exists in (f, O_star)."""
    u = ob[0]; r = ob[-1]
    if len(ob) == 1:
        pre = ([(0, u - 1), (1, u - 1)] if u - 1 > p_ev else []) + [(0, u), (2, u), (2, O_star - 1), (0, f), (1, N - 1), (2, N), (0, N)]
        return run_ph(s, pre, t_ev)
    if f == r + 1:
        pre_u0 = ([(0, u - 1), (1, u - 1)] if u - 1 > p_ev else []) + [(0, u), (2, u), (2, f), (0, r), (2, O_star), (0, f), (1, N - 1), (2, N), (0, N)]
        return run_ph(s, pre_u0, t_ev)
    pre1 = [(1, u)] + ([(2, u)] if u > p_ev + 1 else []) + [(1, r - 1), (2, f), (0, r), (2, O_star - 1), (0, f), (1, N - 1), (2, N), (0, N)]
    return run_ph(s, pre1, t_ev)

def lift_binary_from_Ok(s, t_Ok, O_star):
    """Theorem S-Lift: Universal closed-form completion from any synchronized state
    t_Ok = (p, p, p, 7) (E < p <= O_star, s[p] >= 1, no odd 2 in (p, O_star), M_ev(O_star, N-1) == 0)."""
    N = len(s) - 1
    p = t_Ok[0]; t = t_Ok; w_all = []
    if O_star == N - 1:
        if p == N - 1:
            te, we = run_ph(s, [(2, N), (0, N)], t)
            return we if te == (N, N, N, 7) else None
        ws = complete_binary_suffix(s, p)
        for ch in ws:
            t = lib.step(s, t, ch, directed=True)
            if t is None: return None
        return ws if t == (N, N, N, 7) else None
    if p == O_star:
        te, we = run_ph(s, [(1, N - 1), (2, N), (0, N)], t)
        return we if te == (N, N, N, 7) else None
    while p < O_star:
        ev1 = [i for i in range(p + 1, O_star) if i % 2 == 0 and s[i] == 1]
        od1 = [i for i in range(p + 1, O_star) if i % 2 == 1 and s[i] == 1]
        if p % 2 == 1:
            if not ev1:
                te, we = run_ph(s, [(2, O_star - 1), (0, p + 1), (1, N - 1), (2, N), (0, N)], t)
                return (''.join(w_all) + we) if te == (N, N, N, 7) else None
            f = ev1[0]; obf = [i for i in od1 if i < f]
            if not obf:
                te, we = run_ph(s, [(2, O_star - 1), (0, f), (1, N - 1), (2, N), (0, N)], t)
                return (''.join(w_all) + we) if te == (N, N, N, 7) else None
            r = obf[-1]
            if len(ev1) >= 2 and not [i for i in od1 if i > f]:
                t_ev, w_ev = run_ph(s, [(2, p + 1), (0, p + 1)], t)
                if t_ev != (p + 1, p + 1, p + 1, 7): return None
                te, we = _finish_zero_odd_after_f(s, t_ev, p + 1, obf, f, O_star, N)
                return (''.join(w_all) + w_ev + we) if te == (N, N, N, 7) else None
            t, ws = run_ph(s, [(2, r), (1, f - 1), (2, f), (0, f)], t)
            if t != (f, f, f, 7): return None
            w_all.append(ws); p = f
        else:
            if p == O_star - 1:
                te, we = run_ph(s, [(1, N - 1), (2, N), (0, N)], t)
                return (''.join(w_all) + we) if te == (N, N, N, 7) else None
            if s[p + 1] == 1:
                t, ws = run_ph(s, [(0, p + 1), (1, p + 1)], t)
                if t != (p + 1, p + 1, p + 1, 7): return None
                w_all.append(ws); p = p + 1
            elif not ev1:
                if not od1:
                    te, we = run_ph(s, [(1, O_star - 2), (2, O_star - 1), (0, O_star - 1), (1, N - 1), (2, N), (0, N)], t)
                else:
                    te, we = run_ph(s, [(1, od1[0]), (2, O_star - 1), (1, N - 1), (2, N), (0, N)], t)
                return (''.join(w_all) + we) if te == (N, N, N, 7) else None
            else:
                u = od1[0]; v = ev1[0]
                if u < v:
                    r = max(i for i in od1 if i < v)
                    if len(ev1) >= 2 and not [i for i in od1 if i > v]:
                        obv = [i for i in od1 if i < v]
                        te, we = _finish_zero_odd_after_f(s, t, p, obv, v, O_star, N)
                        return (''.join(w_all) + we) if te == (N, N, N, 7) else None
                    if r == v - 1:
                        t, ws = run_ph(s, [(1, u), (2, r), (1, v - 1), (0, v)], t)
                    else:
                        t, ws = run_ph(s, [(1, u), (2, r), (1, v - 2), (0, u), (2, v), (0, v)], t)
                    if t != (v, v, v, 7): return None
                    w_all.append(ws); p = v
                else:
                    w = max(i for i in ev1 if i < u)
                    t, ws1 = run_ph(s, [(0, w - 1)], t)
                    if t is None: return None
                    t = lib.step(s, t, 'z', directed=True)
                    if t is None: return None
                    t, ws2 = run_ph(s, [(1, max(w, u - 2)), (0, u), (2, u)], t)
                    if t != (u, u, u, 7): return None
                    w_all.append(ws1 + 'z' + ws2); p = u
    return None

def finish_from_O1_plus1(s, t_in, O1):
    """Finishes from (O1 + 1, O1, O1, 7) or (O1, b_odd, O1, 7) when M_ev(O1, N - 1) == 0."""
    N = len(s) - 1
    if any(s[i] == 1 for i in range(O1 + 1, N - 1, 2)):
        return None
    t = t_in; w = ''
    if t[0] == O1 and t[1] < O1:
        t2, w2 = run_ph(s, [(1, O1)], t)
        if t2 != (O1 + 1, O1, O1, 7):
            return None
        t = t2; w = w2
    if t != (O1 + 1, O1, O1, 7):
        return None
    od_rest = [i for i in range(O1 + 2, N - 1, 2) if s[i] >= 1]
    if not od_rest:
        ph = [(1, N - 2), (0, N - 1), (1, N - 1), (2, N), (0, N)]
    else:
        u1 = od_rest[0]
        ph = [(1, N - 2)] + ([(0, u1 - 1)] if u1 - 1 > O1 + 1 else []) + [(1, N - 1), (2, N), (0, N)]
    te, we = run_ph(s, ph, t)
    return (w + we) if te == (N, N, N, 7) else None

def finish_from_even_Ok(s, tv, O_star, lam):
    """Finishes from tv = (v, v, c_pk, m) where v <= lam is an EVEN 1, (tv[3] & 3) == 3,
    and c_pk (or c_pk + 1 if c_pk even) is an ODD PEAK 2 < v (or any c_pk when v == N - 2)!"""
    N = len(s) - 1
    v = tv[0]
    c_pk = tv[2]
    if v == N - 2:
        for ph_n2 in [
            [(0, N - 1), (1, N - 1), (2, N), (0, N)],
            [(1, N - 1), (0, N - 1), (2, N), (0, N)],
        ]:
            te, we = run_ph(s, ph_n2, tv)
            if te == (N, N, N, 7): return we
    Ok = c_pk if c_pk % 2 == 1 else c_pk + 1
    if s[Ok] != 2:
        return None

    # 1. Universal Theorem B5-Complete whenever M_ev(v, Onx) == 0 for ANY odd peak Onx > v (including v == lam, Onx = O_star!):
    od2_after_v = [i for i in range(v + 1, N, 2) if s[i] == 2]
    for Onx in od2_after_v:
        if lib.M_ev(s, v, Onx) == 0:
            od_v_Onx = [i for i in range(v + 1, Onx, 2) if s[i] == 1]
            if not od_v_Onx:
                te, we = run_ph(s, [(1, N - 2), (0, Onx), (2, N), (0, N)], tv)
                if te == (N, N, N, 7): return we
            else:
                u1 = od_v_Onx[0]
                for tl_u1 in [[(1, N - 2), (0, u1), (2, N - 1), (0, N)], [(1, N - 2), (0, u1), (2, N), (0, N)]]:
                    te, we = run_ph(s, tl_u1, tv)
                    if te == (N, N, N, 7): return we
        elif s[N - 2] == 1:
            te, we = run_ph(s, [(1, N - 2), (0, Onx), (2, N), (0, N)], tv)
            if te == (N, N, N, 7): return we
    if v == lam:
        od_lam_O = [i for i in range(lam + 1, O_star, 2) if s[i] == 1]
        if od_lam_O:
            u1 = od_lam_O[0]
            ph_l2 = [(1, O_star - 1), (0, u1), (1, O_star), (2, O_star)] + ([(2, N), (0, N)] if O_star == N - 1 else [(1, N - 1), (2, N), (0, N)])
            te, we = run_ph(s, ph_l2, tv)
            if te == (N, N, N, 7): return we
        return None

    # 2a-bis. Theorem B6: Multi-peak step across (v, Onx0) when M_ev(v, Onx0) > 0 (including Onx0 == O_star!):
    Onx0 = od2_after_v[0]
    if lib.M_ev(s, v, Onx0) > 0:
        w_k = max(i for i in range(v + 2, Onx0, 2) if s[i] == 1)
        od_vw = [i for i in range(v + 1, w_k, 2) if s[i] == 1]
        Om_cands = [Om for Om in od2_after_v if Om >= Onx0 and (Om == Onx0 or lib.M_ev(s, w_k, Om) == 0)]
        od_w_Onx = [i for i in range(w_k + 1, Onx0, 2) if s[i] == 1]
        if not od_vw:
            tw, ww = run_ph(s, [(1, w_k), (0, w_k)], tv)
            if tw and (tw[3] & 3) == 3:
                for Om in Om_cands:
                    te, we = run_ph(s, [(1, N - 2), (0, Om), (2, N), (0, N)], tw)
                    if te == (N, N, N, 7): return ww + we
                if od_w_Onx:
                    te, we = run_ph(s, [(1, N - 2), (0, od_w_Onx[0]), (2, N - 1), (0, N)], tw)
                    if te == (N, N, N, 7): return ww + we
        else:
            tails_b6 = [[(0, Onx0), (2, N), (0, N)]] + ([[(0, od_w_Onx[0]), (2, N - 1), (0, N)]] if od_w_Onx else [])
            for u_vw in ([od_vw[0], od_vw[-1]] if len(od_vw) > 1 else [od_vw[0]]):
                for Om in Om_cands:
                    for tl_b6 in tails_b6:
                        for ph_b6 in [
                            [(1, w_k), (0, u_vw)] + ([(1, Om - 1)] if Om - 1 > w_k else []) + [(2, Om - 1), (1, N - 2)] + tl_b6,
                            [(1, w_k), (0, u_vw)] + ([(1, Om - 1)] if Om - 1 > w_k else []) + [(2, Om), (0, w_k), (1, N - 2)] + tl_b6,
                        ]:
                            te, we = run_ph(s, ph_b6, tv)
                            if te == (N, N, N, 7): return we
            # Synchronize to (u0_vw, u0_vw, u0_vw, 7) across [Ok, Onx0) and invoke multi-peak / binary window sync!
            u0_vw = od_vw[0]
            w0_vw = max(i for i in range(v, u0_vw, 2) if s[i] == 1)
            sync_u_cands = []
            if w0_vw > v:
                pre_w0 = [(1, w0_vw), (0, w0_vw)]
            else:
                pre_w0 = []
            if u0_vw == w0_vw + 1:
                sync_u_cands.append(pre_w0 + [(2, w0_vw), (2, u0_vw)])
                sync_u_cands.append(pre_w0 + [(0, u0_vw), (1, u0_vw), (2, u0_vw)])
            else:
                sync_u_cands.append(pre_w0 + [(0, u0_vw - 1), (1, u0_vw - 1), (0, u0_vw), (2, u0_vw)])
                sync_u_cands.append(pre_w0 + [(1, u0_vw), (0, u0_vw - 1), (2, w0_vw), (0, u0_vw), (2, u0_vw)])
            for su_ph in sync_u_cands:
                tu, wu = run_ph(s, su_ph, tv)
                if tu == (u0_vw, u0_vw, u0_vw, 7):
                    if Onx0 == O_star:
                        res_u = lift_binary_from_Ok(s, tu, O_star)
                    else:
                        res_u = sync_binary_windows_from_p(s, tu, Ok)
                    if res_u: return wu + res_u

    # 2b. If NO odd peak in (v, lam) (i.e. Onx0 == O_star):
    if not [i for i in range(v + 1, lam, 2) if s[i] == 2]:
        od_v_lam = [i for i in range(v + 1, lam, 2) if s[i] == 1]
        if not od_v_lam:
            for fin_vl in [
                [(1, N - 2), (0, O_star), (2, N), (0, N)],
                [(1, lam), (0, O_star)] + ([(2, N), (0, N)] if O_star == N - 1 else [(1, N - 1), (2, N), (0, N)]),
                [(1, lam), (0, lam), (1, N - 2), (0, N - 1), (2, N), (0, N)],
                [(1, lam), (0, lam - 1), (1, O_star - 1), (0, lam), (1, O_star), (2, O_star)] + ([(2, N), (0, N)] if O_star == N - 1 else [(1, N - 1), (2, N), (0, N)]),
            ]:
                te, we = run_ph(s, fin_vl, tv)
                if te == (N, N, N, 7): return we
        else:
            for u_cand in ([od_v_lam[0], od_v_lam[-1]] + [i for i in range(lam + 1, O_star, 2) if s[i] == 1]):
                ph_u = [(1, lam), (0, u_cand - 1 if u_cand > v + 1 else v), (1, O_star - 1), (0, u_cand), (1, O_star), (2, O_star)] + ([(1, N - 1)] if O_star < N - 1 else []) + [(0, N - 1), (2, N), (0, N)]
                te, we = run_ph(s, ph_u, tv)
                if te == (N, N, N, 7): return we
    return None

def finish_from_O1_anchor(s, tE, O1, E):
    """Finishes from tE = (O1, O1, E, 7) OR tE = (O1, O1 - 1, E, 7) across arbitrary >=1 odd peaks in [O1, N - 1)!"""
    N = len(s) - 1
    od2 = [i for i in range(O1, N - 1, 2) if s[i] == 2]
    ev_af = [i for i in range(O1 + 1, N - 1, 2) if s[i] == 1]

    if not ev_af:
        t1, w1 = run_ph(s, [(2, O1)], tE)
        if t1 == (O1, O1, O1, 7):
            res = lift_binary_from_Ok(s, t1, O1)
            if res: return w1 + res
        return None

    lam = ev_af[-1]
    O_star = min(i for i in range(lam + 1, N, 2) if s[i] == 2)
    fR = ev_af[0]

    # 1. Try reaching (O1, O1, O1, 7) -> Theorem B4 or pure-binary (O1, O_star):
    t1, w1 = run_ph(s, [(2, O1)], tE)
    if t1 == (O1, O1, O1, 7):
        for tgt_pk in ([N - 1] if O_star == N - 1 else [N - 1, O_star]):
            if lib.M_od(s, O1, fR) <= s[tgt_pk - 1]:
                ph = [(2, tgt_pk - 1), (0, fR), (1, tgt_pk)] + ([(2, N), (0, N)] if tgt_pk == N - 1 else [(1, N - 1), (2, N), (0, N)])
                te, we = run_ph(s, ph, t1)
                if te == (N, N, N, 7): return w1 + we
        if len(od2) == 1 or od2[1] > lam:
            res = lift_binary_from_Ok(s, t1, O_star)
            if res: return w1 + res

    # 2. THEOREM B5 via (v, v, Ok) -> finish_from_even_Ok!
    Ok_bef_fR = max(i for i in od2 if i < fR)
    Or = max(i for i in od2 if i < lam)
    targets = [(Ok_bef_fR, fR)]
    # Also target w_k = max even 1 before the next odd peak Onx (so M_ev(w_k, Onx) == 0 for Golden Bridge!):
    od2_after_fR = [i for i in od2 if i > fR]
    if od2_after_fR:
        Onx0 = od2_after_fR[0]
        w_k = max(i for i in ev_af if i < Onx0)
        if w_k != fR:
            targets.append((Ok_bef_fR, w_k))
    if lib.M_ev(s, O1, Or) == 0:
        v_Or = min(i for i in ev_af if i > Or)
        if (Or, v_Or) not in targets:
            targets.append((Or, v_Or))

    if len(od2) >= 2 and od2[1] == O1 + 2 and s[O1 + 1] == 0 and tE[1] == O1:
        t2, w2 = run_ph(s, [(0, od2[1]), (2, od2[1])], tE)
        if t2 == (od2[1], od2[1], od2[1], 7):
            if len(od2) == 2 or od2[2] > lam:
                res = lift_binary_from_Ok(s, t2, O_star)
                if res: return w2 + res
            else:
                res2 = finish_from_O1_O1_c(s, t2, od2[1], E)
                if res2: return w2 + res2

    for O_piv, v_tgt in targets:
        b5_pres = [
            [(2, O1), (0, v_tgt)],
            [(2, O1 - 1), (0, v_tgt)],
            [(2, O1 - 1), (1, v_tgt)],
            [(0, v_tgt - 1), (2, O1 - 1), (1, v_tgt)],
            [(0, v_tgt - 1), (2, O1), (1, v_tgt)],
            [(0, O_piv), (2, O1 - 1), (0, v_tgt - 1), (1, v_tgt)],
            [(0, O_piv), (2, O1), (0, v_tgt - 1), (1, v_tgt)],
            [(0, O_piv), (2, O_piv - 1), (0, v_tgt - 1), (1, v_tgt)],
            [(0, O_piv), (2, O_piv), (0, v_tgt)],
            [(0, O_piv), (1, O_piv), (2, O_piv), (1, v_tgt)],
            [(0, O_piv), (1, O_piv), (2, O1), (1, v_tgt)],
        ]
        for pre in b5_pres:
            tf, wf = run_ph(s, pre, tE)
            if tf and tf[0] == v_tgt and tf[1] == v_tgt and (tf[3] & 3) == 3:
                we = finish_from_even_Ok(s, tf, O_star, lam)
                if we: return wf + we

    # 3. Inductive binary step from (O1, O1, O1, 7) when fR < O2:
    if t1 == (O1, O1, O1, 7):
        res = finish_from_O1_O1_c(s, t1, O1, E)
        if res: return w1 + res
    return None

def finish_from_O1_e_anchor(s, t_e, O1, b_ev, c_ep, E):
    """Finishes from t_e = (O1, b_ev, c_ep, 7) where b_ev < O1 is EVEN (s[b_ev] in {0,1}, e.g. O1-1 or E)
    and c_ep in [e, E] is an internal even peak (all internal even peaks < c_ep already right-witnessed)!"""
    N = len(s) - 1
    od2 = [i for i in range(O1, N - 1, 2) if s[i] == 2]
    ev_af = [i for i in range(O1 + 1, N - 1, 2) if s[i] == 1]
    if not ev_af:
        if b_ev <= O1 - 1:
            return finish_from_O1_O1_c(s, t_e, O1, E)
        return None
    lam = ev_af[-1]
    O_star = min(i for i in range(lam + 1, N, 2) if s[i] == 2)
    lift_tail = [(1, O_star), (2, O_star)] + ([(2, N), (0, N)] if O_star == N - 1 else [(1, N - 1), (2, N), (0, N)])
    fR = ev_af[0]
    # Also try Theorem B5 directly from (O1, O1 - 1, E, 7) when c_ep == E and b_ev == O1 - 1:
    if c_ep == E and b_ev == O1 - 1:
        res = finish_from_O1_anchor(s, t_e, O1, E)
        if res: return res
    if len(od2) >= 2 and od2[1] < lam:
        Or = max(i for i in od2 if i < lam)
        Ok = max(i for i in od2 if i < fR)
        targets_e = [(Ok, fR)]
        od2_af_fR = [i for i in od2 if i > fR]
        if od2_af_fR:
            w_ke = max(i for i in ev_af if i < od2_af_fR[0])
            if w_ke != fR:
                targets_e.append((Ok, w_ke))
        if lib.M_ev(s, O1, Or) == 0:
            v_Or_e = min(i for i in ev_af if i > Or)
            if (Or, v_Or_e) not in targets_e:
                targets_e.append((Or, v_Or_e))
            od2_af_Or = [i for i in od2 if i > v_Or_e]
            if od2_af_Or:
                w_Or_e = max(i for i in ev_af if i < od2_af_Or[0])
                if (Or, w_Or_e) not in targets_e:
                    targets_e.append((Or, w_Or_e))
        for O_piv, v_tgt in targets_e:
            if lib.M_ev(s, O1, O_piv) > s[b_ev]: continue
            pre_O = [(0, O_piv)] if c_ep == E else [(0, O_piv - 1)]
            # Note: if b_ev < O1 - 1 (e.g. b_ev == E), first walk B -> O1 - 1? No, (2, O_piv - 1) needs B at O1(2) on first z, so b_ev == O1 - 1 (or walk B -> O1 during C)!
            if b_ev == O1 - 1:
                mid_v_list = [[(1, v_tgt)]] if v_tgt == O_piv + 1 else [[(1, v_tgt)], [(1, O_piv), (0, v_tgt - 1), (1, v_tgt)]]
                for mid_v in mid_v_list:
                    tv, wv = run_ph(s, pre_O + [(2, O_piv - 1)] + mid_v, t_e)
                    if tv and tv[0] == v_tgt and tv[1] == v_tgt and (tv[3] & 3) == 3:
                        we = finish_from_even_Ok(s, tv, O_star, lam)
                        if we: return wv + we
                if O_piv >= O1 + 2:
                    for pre_b in [
                        [(0, O1 + 1), (2, O1)] + ([(2, O_piv - 1)] if O_piv - 1 > O1 else []) + [(0, v_tgt - 1), (1, v_tgt)],
                        [(0, O_piv - 1), (2, O1)] + ([(2, O_piv - 1)] if O_piv - 1 > O1 else []) + ([(0, v_tgt - 1)] if v_tgt - 1 > O_piv else []) + [(1, v_tgt)],
                    ]:
                        tv, wv = run_ph(s, pre_b, t_e)
                        if tv and tv[0] == v_tgt and tv[1] == v_tgt and (tv[3] & 3) == 3:
                            we = finish_from_even_Ok(s, tv, O_star, lam)
                            if we: return wv + we
                    od_Op_v = [i for i in range(O_piv + 2, v_tgt, 2) if s[i] == 1]
                    if O_piv == Or and od_Op_v:
                        u1_op = od_Op_v[0]
                        tu_op, wu_op = run_ph(s, [(0, O1 + 1), (2, O1)] + ([(2, O_piv - 1)] if O_piv - 1 > O1 else []) + [(1, u1_op - 1), (0, u1_op), (1, u1_op), (2, u1_op)], t_e)
                        if tu_op and tu_op[:3] == (u1_op, u1_op, u1_op) and (tu_op[3] & 6) == 6:
                            res_op = lift_binary_from_Ok(s, tu_op, O_star)
                            if res_op: return wu_op + res_op
            else:
                for ph_E in [
                    [(0, O_piv - 1), (2, O1 - 1), (1, v_tgt)],
                    [(0, O_piv - 1), (2, O1 - 1), (1, O_piv), (0, v_tgt - 1), (1, v_tgt)],
                    [(0, O_piv - 1), (1, O1), (2, O_piv - 1), (1, v_tgt)],
                    [(0, O_piv - 1), (1, O1), (2, O_piv - 1), (1, O_piv), (0, v_tgt - 1), (1, v_tgt)],
                    [(0, v_tgt - 1), (2, O1 - 1), (1, v_tgt)],
                    [(0, v_tgt - 1), (1, O1), (2, O_piv - 1), (1, v_tgt)],
                ]:
                    tv, wv = run_ph(s, ph_E, t_e)
                    if tv and tv[0] == v_tgt and tv[1] == v_tgt and (tv[3] & 3) == 3:
                        we = finish_from_even_Ok(s, tv, O_star, lam)
                        if we: return wv + we
    if b_ev <= O1 - 1:
        res_c = finish_from_O1_O1_c(s, t_e, O1, E)
        if res_c: return res_c
    return None

def finish_from_O1_O1_c(s, t_in, O1, E):
    """Given t_in = (O1, b_le_O1, c0, m) with c0 <= O1, completes OP1."""
    N = len(s) - 1
    od2 = [i for i in range(O1, N - 1, 2) if s[i] == 2]
    ev_af = [i for i in range(O1 + 1, N - 1, 2) if s[i] == 1]

    # Try advancing to (O1, O1 or O1-1, E, 7 or 5) first if c0 <= E!
    if t_in[2] <= E:
        t = t_in; w = ''
        if t[2] < E and t[2] % 2 == 0 and not (t[3] & 4):
            u = lib.step(s, t, 'y', directed=True)
            if u is not None: t = u; w += 'y'
        if t[2] < E:
            t2, w2 = run_ph(s, [(2, E)], t)
            if t2 is not None: t = t2; w += w2
        if t[2] == E and (not (t[3] & 4) or not (t[3] & 1)):
            u = lib.step(s, t, 'y', directed=True)
            if u is not None: t = u; w += 'y'
        if t and t[0] == O1 and t[1] <= O1 and t[2] == E and (t[3] & 5) == 5:
            res = finish_from_O1_anchor(s, t, O1, E)
            if res: return w + res
        if t and t[0] == O1 and t[2] == E and (t[3] & 5) == 5 and not ev_af:
            if O1 == N - 1:
                te, we = run_ph(s, [(2, N), (1, N)], t)
                if te == (N, N, N, 7): return w + we
            else:
                to, wo = run_ph(s, [(2, O1)], t)
                if to:
                    res_p1 = finish_from_O1_plus1(s, to, O1)
                    if res_p1: return w + wo + res_p1

    # Advance to (O1, O1, O1, 7) (or if already at (O1, O1, O1, 7)):
    if t_in == (O1, O1, O1, 7):
        t1, w = t_in, ''
    else:
        t = t_in; w = ''
        if t[2] % 2 == 0 and not (t[3] & 4):
            u = lib.step(s, t, 'y', directed=True)
            if u is None: return None
            t = u; w += 'y'
        t1, w1 = run_ph(s, [(2, O1)], t)
        if t1 != (O1, O1, O1, 7): return None
        w += w1

    if not ev_af:
        res = lift_binary_from_Ok(s, t1, O1)
        return (w + res) if res else None
    lam = ev_af[-1]; fR = ev_af[0]
    O_star = min(i for i in range(lam + 1, N, 2) if s[i] == 2)
    lift_tail = [(1, O_star), (2, O_star)] + ([(2, N), (0, N)] if O_star == N - 1 else [(1, N - 1), (2, N), (0, N)])

    for tgt_pk in ([N - 1] if O_star == N - 1 else [N - 1, O_star]):
        if lib.M_od(s, O1, fR) <= s[tgt_pk - 1]:
            ph = [(2, tgt_pk - 1), (0, fR), (1, tgt_pk)] + ([(2, N), (0, N)] if tgt_pk == N - 1 else [(1, N - 1), (2, N), (0, N)])
            te, we = run_ph(s, ph, t1)
            if te == (N, N, N, 7): return w + we
    if len(od2) == 1 or od2[1] > lam:
        res = lift_binary_from_Ok(s, t1, O_star)
        if res: return w + res
    if fR == O1 + 1:
        tf, wf = run_ph(s, [(0, fR)], t1)
        if tf and (tf[3] & 3) == 3:
            we = finish_from_even_Ok(s, tf, O_star, lam)
            if we: return w + wf + we
    res_mp = sync_binary_windows_from_p(s, t1, O1)
    if res_mp: return w + res_mp
    return None

def try_post_Onx_bc_relay(s, tc, Onx, od2, ev_af, lam, N):
    """Post-Onx (B, C) Relay Theorem: from tc = (a_cur < Onx, Onx, Onx, 7), steps (B, C) across
    remaining odd peaks in (Onx, lam) while keeping A < Onx, then finishes via Golden Bridge."""
    def _try_gb_from_bc(t_bc, O_cur):
        O_nxt = min(i for i in range(O_cur + 2, N, 2) if s[i] == 2)
        gb_cands = [
            [(2, O_nxt - 1), (0, Onx - 1), (1, N - 2), (2, N), (0, N)],
            [(2, O_nxt - 1), (1, N - 2), (0, Onx), (2, N), (0, N)],
            [(2, O_nxt - 1), (0, Onx), (1, N - 1), (2, N), (0, N)],
            [(1, lam), (2, O_nxt - 1), (0, Onx - 1), (1, N - 2), (2, N), (0, N)],
        ]
        for ph_gb in gb_cands:
            te, we = run_ph(s, ph_gb, t_bc)
            if te == (N, N, N, 7):
                return we
        return None

    t_bc = tc
    w_bc_acc = ''
    O_prev = Onx
    we0 = _try_gb_from_bc(t_bc, O_prev)
    if we0:
        return we0
    for O_j in [o for o in od2 if Onx < o < lam]:
        ev_bw = [i for i in ev_af if O_prev < i < O_j]
        stepped_j = False
        if ev_bw:
            w_bw = ev_bw[-1]
            for ph_j in [[(1, w_bw), (2, O_j)], [(1, w_bw), (0, t_bc[0] + 1), (2, O_j)]]:
                tj, wj = run_ph(s, ph_j, t_bc)
                if tj and tj[0] < Onx and tj[1] == O_j and tj[2] == O_j and tj[3] == 7:
                    t_bc = tj; w_bc_acc += wj; O_prev = O_j; stepped_j = True; break
        else:
            raw_cands = ['xyzx', 'xyz', 'yzzx', 'zxyx'] if O_j == O_prev + 2 else []
            for raw_w in raw_cands:
                tj = t_bc; ok_r = True
                for ch_r in raw_w:
                    tj = lib.step(s, tj, ch_r, directed=True)
                    if tj is None or tj[0] >= Onx:
                        ok_r = False; break
                if ok_r and tj[1] == O_j and tj[2] == O_j and tj[3] == 7:
                    t_bc = tj; w_bc_acc += raw_w; O_prev = O_j; stepped_j = True; break
            if not stepped_j:
                for ph_j in [[(1, O_j - 2), (2, O_j)], [(1, O_j - 1), (2, O_j)]]:
                    tj, wj = run_ph(s, ph_j, t_bc)
                    if tj and tj[0] < Onx and tj[1] == O_j and tj[2] == O_j and tj[3] == 7:
                        t_bc = tj; w_bc_acc += wj; O_prev = O_j; stepped_j = True; break
        if not stepped_j:
            break
        we_j = _try_gb_from_bc(t_bc, O_prev)
        if we_j:
            return w_bc_acc + we_j
    return None

def sync_binary_windows_from_p(s, t_start, Ok_start):
    """Multi-Peak Binary Window Synchronizer: steps from t_start = (p0, p0, p0, 7)
    (where Ok_start <= p0 < Onx) across [Ok_k, Ok_{k+1}) windows and lifts via Theorem S-Lift / B5-Complete."""
    N = len(s) - 1
    od2 = [i for i in range(Ok_start, N - 1, 2) if s[i] == 2]
    ev_af = [i for i in range(Ok_start + 1, N - 1, 2) if s[i] == 1]
    if not ev_af:
        return lift_binary_from_Ok(s, t_start, Ok_start)
    lam = ev_af[-1]
    O_star = min(i for i in range(lam + 1, N, 2) if s[i] == 2)
    if len(od2) == 1 or od2[1] > lam:
        return lift_binary_from_Ok(s, t_start, O_star)

    idx_pk = 0; t_pk = t_start; w_pk = ''
    while idx_pk + 1 < len(od2) and od2[idx_pk + 1] < lam:
        Ok = od2[idx_pk]; Onx = od2[idx_pk + 1]
        p_init = t_pk[0]
        ev_nx = [i for i in ev_af if i > p_init]
        if p_init == Ok:
            if not ev_nx: break
            if ev_nx[0] < Onx:
                f_nx = ev_nx[0]
                for tgt_pk in ([N - 1] if O_star == N - 1 else [N - 1, O_star]):
                    if lib.M_od(s, Ok, f_nx) <= s[tgt_pk - 1]:
                        ph = [(2, tgt_pk - 1), (0, f_nx), (1, tgt_pk)] + ([(2, N), (0, N)] if tgt_pk == N - 1 else [(1, N - 1), (2, N), (0, N)])
                        te, we = run_ph(s, ph, t_pk)
                        if te == (N, N, N, 7): return w_pk + we
                if f_nx == Ok + 1:
                    tf, wf = run_ph(s, [(0, f_nx)], t_pk)
                    if tf and (tf[3] & 3) == 3:
                        we = finish_from_even_Ok(s, tf, O_star, lam)
                        if we: return w_pk + wf + we
        def _try_tf_before_Onx(tf, f_ev, w_ev):
            od_f_Onx = [i for i in range(f_ev + 1, Onx, 2) if s[i] == 1]
            cands_tf = [
                [(1, N - 2), (0, Onx if not od_f_Onx else od_f_Onx[0]), (2, N), (0, N)],
                [(1, N - 2), (0, Onx if not od_f_Onx else od_f_Onx[0]), (2, N - 1), (0, N)],
            ]
            if not od_f_Onx and w_ev > f_ev:
                cands_tf.append([(0, w_ev - 1), (1, N - 2), (0, Onx), (2, N), (0, N)])
                cands_tf.append([(1, lam), (0, w_ev), (1, N - 2), (0, Onx), (2, N), (0, N)])
                for b_ev_r in [i for i in ev_af if i > Onx]:
                    if b_ev_r - 2 > Onx:
                        cands_tf.append([(1, b_ev_r - 2), (0, w_ev - 1), (1, N - 2), (0, Onx), (2, N), (0, N)])
                    if b_ev_r - 3 >= Onx:
                        cands_tf.append([(1, b_ev_r - 3), (0, w_ev - 1), (1, N - 2), (0, Onx), (2, N), (0, N)])
            for ph_tf in cands_tf:
                te_tf, we_tf = run_ph(s, ph_tf, tf)
                if te_tf == (N, N, N, 7): return we_tf
            return None

        s_Onx = tuple(s[:Onx + 1]) + (2,)
        tc = t_pk; pr = []; advanced = False
        while tc is not None and tc[0] < Onx:
            if tc == (Onx - 1, Onx - 1, Onx - 1, 7) and s[Onx - 1] == 1:
                we_nx = finish_from_even_Ok(s, tc, O_star, lam)
                if we_nx: return w_pk + ''.join(pr) + we_nx
            if tc[0] == tc[1] == tc[2] and tc[3] == 7:
                p_cur = tc[0]
                ev1_w = [i for i in range(p_cur + 1, Onx) if i % 2 == 0 and s[i] == 1]
                od1_w = [i for i in range(p_cur + 1, Onx) if i % 2 == 1 and s[i] == 1]
                if p_cur % 2 == 1 and ev1_w:
                    f_w = ev1_w[0]; obf_w = [i for i in od1_w if i < f_w]; w_ev = ev1_w[-1]
                    if not obf_w:
                        tf_w, wf_w = run_ph(s, [(2, Onx - 1), (0, f_w)], tc)
                        if tf_w:
                            we_tf = _try_tf_before_Onx(tf_w, f_w, w_ev)
                            if we_tf: return w_pk + ''.join(pr) + wf_w + we_tf
                    elif obf_w and (len(ev1_w) == 1 or not [i for i in od1_w if i > f_w]):
                        u0_w = obf_w[0]; r_w = obf_w[-1]
                        t_ev_w, w_ev_w = run_ph(s, [(2, p_cur + 1), (0, p_cur + 1)], tc)
                        if t_ev_w == (p_cur + 1, p_cur + 1, p_cur + 1, 7):
                            p_ev_w = p_cur + 1
                            if len(obf_w) == 1:
                                pre_fw = ([(0, u0_w - 1), (1, u0_w - 1)] if u0_w - 1 > p_ev_w else []) + [(0, u0_w), (2, u0_w), (2, Onx - 1), (0, f_w)]
                            elif f_w == r_w + 1:
                                pre_fw = ([(0, u0_w - 1), (1, u0_w - 1)] if u0_w - 1 > p_ev_w else []) + [(0, u0_w), (2, u0_w), (2, f_w), (0, r_w), (2, Onx), (0, f_w)]
                            else:
                                pre_fw = [(1, u0_w)] + ([(2, u0_w)] if u0_w > p_ev_w + 1 else []) + [(1, r_w - 1), (2, f_w), (0, r_w), (2, Onx - 1), (0, f_w)]
                            tf_w, wf_w = run_ph(s, pre_fw, t_ev_w)
                            if tf_w:
                                we_tf = _try_tf_before_Onx(tf_w, f_w, w_ev)
                                if we_tf: return w_pk + ''.join(pr) + w_ev_w + wf_w + we_tf
                elif p_cur % 2 == 0 and s[p_cur + 1] == 0 and ev1_w and od1_w and od1_w[0] < ev1_w[0]:
                    f_w = ev1_w[0]; obf_w = [i for i in od1_w if i < f_w]; w_ev = ev1_w[-1]
                    if len(ev1_w) == 1 or not [i for i in od1_w if i > f_w]:
                        u0_w = obf_w[0]; r_w = obf_w[-1]
                        if len(obf_w) == 1:
                            pre_fw = ([(0, u0_w - 1), (1, u0_w - 1)] if u0_w - 1 > p_cur else []) + [(0, u0_w), (2, u0_w), (2, Onx - 1), (0, f_w)]
                        elif f_w == r_w + 1:
                            pre_fw = ([(0, u0_w - 1), (1, u0_w - 1)] if u0_w - 1 > p_cur else []) + [(0, u0_w), (2, u0_w), (2, f_w), (0, r_w), (2, Onx), (0, f_w)]
                        else:
                            pre_fw = [(1, u0_w)] + ([(2, u0_w)] if u0_w > p_cur + 1 else []) + [(1, r_w - 1), (2, f_w), (0, r_w), (2, Onx - 1), (0, f_w)]
                        tf_w, wf_w = run_ph(s, pre_fw, tc)
                        if tf_w:
                            we_tf = _try_tf_before_Onx(tf_w, f_w, w_ev)
                            if we_tf: return w_pk + ''.join(pr) + wf_w + we_tf
                elif p_cur % 2 == 0 and not ev1_w and not od1_w and p_cur < Onx - 1:
                    t_m1, w_m1 = run_ph(s, [(1, Onx - 2), (2, Onx - 1), (0, Onx - 1)], tc)
                    if t_m1 == (Onx - 1, Onx - 1, Onx - 1, 7):
                        te_m1, we_m1 = run_ph(s, [(1, N - 2), (0, Onx), (2, N), (0, N)], t_m1)
                        if te_m1 == (N, N, N, 7): return w_pk + ''.join(pr) + w_m1 + we_m1
                if p_cur % 2 == 0 and p_cur < Onx - 1 and s[p_cur + 1] == 1:
                    ok_st2 = True
                    for ch2 in 'yz':
                        tc = lib.step(s, tc, ch2, directed=True)
                        if tc is None: ok_st2 = False; break
                        pr.append(ch2)
                    if not ok_st2: break
                    continue
            ws_nx = complete_binary_suffix(s_Onx, tc[0])
            stepped_sync = False
            for ch in ws_nx:
                if tc == (Onx - 1, Onx - 1, Onx - 1, 7) and s[Onx - 1] == 1:
                    we_nx = finish_from_even_Ok(s, tc, O_star, lam)
                    if we_nx: return w_pk + ''.join(pr) + we_nx
                if tc[0] < Onx and tc[0] % 2 == 0 and s[tc[0]] == 1 and lib.M_ev(s, tc[0], Onx) == 0 and tc[2] == Onx - 1 and tc[3] == 7 and tc[1] <= N - 2:
                    od_w_nx = [i for i in range(tc[0] + 1, Onx, 2) if s[i] == 1]
                    tail_b5 = [(0, Onx), (2, N), (0, N)] if not od_w_nx else [(0, od_w_nx[0]), (2, N - 1), (0, N)]
                    te_nx, we_nx = run_ph(s, ([(1, N - 2)] if tc[1] < N - 2 else []) + tail_b5, tc)
                    if te_nx == (N, N, N, 7):
                        return w_pk + ''.join(pr) + we_nx
                if tc[1] == Onx and tc[2] == Onx and tc[3] == 7 and tc[0] < Onx:
                    we_rel = try_post_Onx_bc_relay(s, tc, Onx, od2, ev_af, lam, N)
                    if we_rel:
                        return w_pk + ''.join(pr) + we_rel
                p_prev = tc[0]
                tc = lib.step(s, tc, ch, directed=True)
                if tc is None: break
                pr.append(ch)
                if tc[1] == Onx and tc[2] == Onx and tc[3] == 7 and tc[0] < Onx:
                    we_rel = try_post_Onx_bc_relay(s, tc, Onx, od2, ev_af, lam, N)
                    if we_rel:
                        return w_pk + ''.join(pr) + we_rel
                if tc[0] == tc[1] == tc[2] and tc[3] == 7 and p_prev < tc[0] < Onx:
                    stepped_sync = True; break
            if advanced or not stepped_sync:
                break
        if not advanced:
            break
    return None

# ==============================================================================
# 3b. Closed-Form Binary Right-Wing C-Stepper, Parity Walk & 4-Peak Relay
# ==============================================================================
def step_c_to_goal_general(s, t_init, c_goal, evR_c, O_star, E):
    """Steps C from t_init[2] to odd target c_goal using deterministic closed-form cursor phases on [E .. lam_c]."""
    t = t_init; w_acc = []
    while t[2] < c_goal:
        if t[2] % 2 == 1:
            if not (t[3] & 4):
                b_od1 = next((j for j in range(max(E + 1, t[1] + (0 if t[1] % 2 == 1 else 1)), O_star, 2) if s[j] >= s[t[2]]), None)
                if b_od1 is None: return None, None
                tb, wb = run_ph(s, [(1, b_od1 if b_od1 > t[1] else b_od1 + 1)], t)
                if tb is None or not (tb[3] & 4): return None, None
                t = tb; w_acc.append(wb)
            nxt_ev = t[2] + 1
            wt_ev = s[nxt_ev]
            a_af = t[0] if t[0] % 2 == 1 else t[0] + 1
            if wt_ev == 1 and s[a_af] == 0:
                if t[0] % 2 == 1 and t[0] + 2 < O_star and s[t[0] + 2] >= 1:
                    ux = lib.step(s, t, 'x', directed=True)
                    if ux: t = ux; w_acc.append('x')
                elif t[1] % 2 == 0 and s[t[1]] >= 1:
                    a_od1 = next((j for j in range(max(E + 1, t[0] + (2 if t[0] % 2 == 1 else 1)), O_star, 2) if s[j] == 1), None)
                    if a_od1 and a_od1 - 1 > t[0] and lib.M_od(s, t[0], a_od1 - 1) == 0:
                        ta, wa = run_ph(s, [(0, a_od1 - 1)], t)
                        if ta: t = ta; w_acc.append(wa)
                    else:
                        return None, None
                else:
                    return None, None
            next_ev1 = next((i for i in range(nxt_ev + 2, c_goal + 2, 2) if s[i] == 1), None)
            a_post = t[0] if t[0] % 2 == 1 else t[0] + 1
            if next_ev1 is not None and s[a_post] == 0 and wt_ev == 0:
                if t[0] % 2 == 0 and s[t[0]] >= 1:
                    b_ev_ok = [b for b in evR_c if b >= t[1] and (nxt_ev + 1 > c_goal or s[nxt_ev + 1] == 0 or s[b + 1] >= 1)]
                    if not b_ev_ok: b_ev_ok = [b for b in evR_c if b >= t[1]]
                    if b_ev_ok:
                        b_pick = b_ev_ok[-1] if (nxt_ev + 1 <= c_goal and s[nxt_ev + 1] == 0 and s[b_ev_ok[-1] + 1] == 0) else b_ev_ok[0]
                        if b_pick > t[1]:
                            tb, wb = run_ph(s, [(1, b_pick)], t)
                            if tb: t = tb; w_acc.append(wb)
            elif nxt_ev + 1 <= c_goal and s[nxt_ev + 1] == 1:
                b_after_z = t[1] if t[1] % 2 == 1 else t[1] + 1
                if s[b_after_z] == 0:
                    b_od1 = next((j for j in range(max(E + 1, t[1] + 1), O_star, 2) if s[j] == 1), None)
                    if b_od1 and b_od1 - 1 > t[1]:
                        if lib.M_ev(s, t[1], b_od1) > 0 and (t[0] % 2 == 1 or s[t[0]] == 0):
                            if t[0] % 2 == 1 and t[0] + 1 in evR_c:
                                ux = lib.step(s, t, 'x', directed=True)
                                if ux: t = ux; w_acc.append('x')
                        tb, wb = run_ph(s, [(1, b_od1 - 1)], t)
                        if tb: t = tb; w_acc.append(wb)
            elif wt_ev == 1 and (t[1] % 2 == 1 or s[t[1]] == 0):
                b_ev1 = next((b for b in evR_c if b >= t[1]), None)
                if b_ev1 and b_ev1 > t[1]:
                    if lib.M_ev(s, t[1], b_ev1 + 1) <= (s[t[0]] if t[0] % 2 == 0 else s[t[0] + 1]):
                        tb, wb = run_ph(s, [(1, b_ev1)], t)
                        if tb: t = tb; w_acc.append(wb)
            uy = lib.step(s, t, 'y', directed=True)
            if uy is None: return None, None
            t = uy; w_acc.append('y')
        else:
            if not (t[3] & 4):
                a_od1 = next((j for j in range(max(E + 1, t[0] + (0 if t[0] % 2 == 1 else 1)), O_star, 2) if s[j] >= s[t[2]]), None)
                if a_od1 is None: return None, None
                ta, wa = run_ph(s, [(0, a_od1 if a_od1 > t[0] else a_od1 + 1)], t)
                if ta is None or not (ta[3] & 4): return None, None
                t = ta; w_acc.append(wa)
            nxt_od = t[2] + 1
            next_ev1 = next((i for i in range(t[2] + 2, c_goal + 2, 2) if s[i] == 1), None)
            if next_ev1 is not None:
                a_af = t[0] if t[0] % 2 == 1 else t[0] + 1
                if s[a_af] == 0:
                    if t[1] % 2 == 1 and t[1] + 1 in evR_c and s[nxt_od] == 0:
                        ux = lib.step(s, t, 'x', directed=True)
                        if ux: t = ux; w_acc.append('x')
                    if t[1] % 2 == 0 and s[t[1]] >= 1:
                        a_od1 = next((j for j in range(max(E + 1, t[0] + (2 if t[0] % 2 == 1 else 1)), O_star, 2) if s[j] == 1), None)
                        if a_od1 and a_od1 - 1 > t[0]:
                            ta, wa = run_ph(s, [(0, a_od1 - 1)], t)
                            if ta: t = ta; w_acc.append(wa)
            uz = lib.step(s, t, 'z', directed=True)
            if uz is None: return None, None
            t = uz; w_acc.append('z')
            if not (t[3] & 4):
                b_od1 = next((j for j in range(max(E + 1, t[1] + 2), O_star, 2) if s[j] >= s[t[2]]), None)
                if b_od1:
                    if lib.M_ev(s, t[1], b_od1) > 0 and (t[0] % 2 == 1 or s[t[0]] == 0):
                        if t[0] % 2 == 1 and t[0] + 1 in evR_c:
                            ux = lib.step(s, t, 'x', directed=True)
                            if ux: t = ux; w_acc.append('x')
                    tb, wb = run_ph(s, [(1, b_od1)], t)
                    if tb and (tb[3] & 4): t = tb; w_acc.append(wb)
    if not (t[3] & 4): return None, None
    return t, ''.join(w_acc)

def try_binary_parity_walk_to_Ostar(s, t_start, O_star, e, tail_O_m1, N):
    """Universal Binary Parity Walk across [p_start .. O_star] keeping C <= e (minimal +1 C-advance per step)."""
    t = t_start; w_acc = []
    p_ev = t[0]
    while p_ev < O_star - 1:
        pos_odd = p_ev + 1
        # Stay-Continuation Witness Recovery when C is odd, unwitnessed (m_C == 0), and s[pos_odd] < s[C]:
        if t[2] % 2 == 1 and not (t[3] & 4) and s[pos_odd] < s[t[2]]:
            if s[t[2]] != 1:
                return None
            u_nx = next((j for j in range(pos_odd + 2, O_star, 2) if s[j] == 1), None)
            if u_nx is None or lib.M_ev(s, p_ev, u_nx) > s[p_ev]:
                return None
            tu, wu = run_ph(s, [(1, u_nx)], t)
            if tu is None or not (tu[3] & 4):
                return None
            ty = lib.step(s, tu, 'y', directed=True)
            if ty is None or ty[2] > e:
                return None
            ev_c = next((i for i in range(ty[2], e + 1, 2) if s[i] >= 1), None)
            if ev_c is None or ev_c == e:
                return None
            tc2, wc2 = run_ph(s, [(2, ev_c)] if ev_c > ty[2] else [], ty)
            if tc2 is None:
                return None
            tsync, wsync = run_ph(s, [(0, u_nx + 1)], tc2)
            if tsync is None or tsync[:2] != (u_nx + 1, u_nx + 1) or tsync[3] != 7:
                return None
            w_acc.extend([wu, 'y', wc2, wsync])
            t = tsync; p_ev = t[0]
            continue
        # Symmetric Stay-Continuation Witness Recovery when C is even, unwitnessed (m_C == 0), and s[pos_odd] < s[C]:
        if t[2] % 2 == 0 and not (t[3] & 4) and s[pos_odd] < s[t[2]]:
            if s[t[2]] != 1:
                return None
            u_nx = next((j for j in range(pos_odd + 2, O_star, 2) if s[j] == 1), None)
            if u_nx is None or lib.M_ev(s, p_ev, u_nx) > s[p_ev]:
                return None
            ta, wa = run_ph(s, [(0, u_nx)], t)
            if ta is None or not (ta[3] & 4):
                return None
            tz = lib.step(s, ta, 'z', directed=True)
            if tz is None or tz[2] >= e:
                return None
            od_c = next((i for i in range(tz[2], e, 2) if s[i] >= 1), None)
            if od_c is None:
                return None
            tc2, wc2 = run_ph(s, [(2, od_c)] if od_c > tz[2] else [], tz)
            if tc2 is None:
                return None
            tsync, wsync = run_ph(s, [(1, u_nx + 1)], tc2)
            if tsync is None or tsync[:2] != (u_nx + 1, u_nx + 1) or tsync[3] != 7:
                return None
            w_acc.extend([wa, 'z', wc2, wsync])
            t = tsync; p_ev = t[0]
            continue

        pair = ('z', 'y') if t[2] % 2 == 1 else ('y', 'z')
        ok_p = True
        for ch in pair:
            t = lib.step(s, t, ch, directed=True)
            if t is None or t[2] > e:
                ok_p = False; break
            w_acc.append(ch)
        if not ok_p:
            return None
        wt_need = s[pos_odd]
        if not (t[3] & 1):
            ev_c = next((i for i in range(t[2] + (1 if t[2] % 2 == 1 else 2), e + 1, 2) if s[i] >= wt_need), None)
            if ev_c is None: return None
            t, wc1 = run_ph(s, [(2, ev_c)], t)
            if t is None or not (t[3] & 1): return None
            w_acc.append(wc1)
        if not (t[3] & 2):
            od_c = next((i for i in range(t[2] + (2 if t[2] % 2 == 1 else 1), e, 2) if s[i] >= wt_need), None)
            if od_c is None: return None
            t, wc2 = run_ph(s, [(2, od_c)], t)
            if t is None or not (t[3] & 2): return None
            w_acc.append(wc2)
        tx = lib.step(s, t, 'x', directed=True)
        if tx is None:
            return None
        w_acc.append('x')
        t = tx; p_ev = t[0]
    if t[0] == O_star - 1 and t[1] == O_star - 1 and (t[3] & 3) == 3:
        for fin_w in [
            [(0, O_star), (1, O_star), (2, O_star)] + tail_O_m1,
            [(1, O_star), (0, O_star), (2, O_star)] + tail_O_m1,
        ]:
            te, we = run_ph(s, fin_w, t)
            if te == (N, N, N, 7):
                return ''.join(w_acc) + we
    return None

def try_four_peak_relay(s, t, Ob, od2_R, evR, O_star, N):
    """4-Peak Right-Wing Relay Golden Bridge from t = (Ob, Ob, c >= E, m)."""
    Oa = max(o for o in od2_R if o < Ob)
    od2_rem = [o for o in od2_R if o > Ob]
    if len(od2_rem) < 2:
        return None
    Oc, Od = od2_rem[0], od2_rem[1]
    ev_bc = [i for i in evR if Ob < i < Oc]
    ev_cd = [i for i in evR if Oc < i < Od]
    if not (ev_bc and ev_cd and Od == O_star):
        return None
    w_bc, w_cd = ev_bc[-1], ev_cd[-1]
    ev_e_oa = [i for i in evR if t[2] < i < Oa]
    pre_c_opts = [[]] + ([[(2, ev_e_oa[0])]] if ev_e_oa else [])
    od_oa_ob = [i for i in range(Oa + 2, Ob, 2) if s[i] == 1]
    for pre_c in pre_c_opts:
        t_rel, w_rel = run_ph(s, pre_c + [(1, w_bc), (2, Oa - 1), (1, w_cd)], t)
        if t_rel and t_rel[1] == w_cd and t_rel[2] == Oa:
            mid_rels = [
                [(0, Oc - 2), (1, Od - 1), (2, Ob), (1, N - 2), (2, N), (0, N)],
                [(1, Od - 1), (0, Oc - 2), (2, Ob), (1, N - 2), (2, N), (0, N)],
            ]
            if od_oa_ob:
                mid_rels.insert(0, [(2, od_oa_ob[0]), (0, Oc - 2), (2, Ob), (1, N - 2), (2, N), (0, N)])
            for mid_rel in mid_rels:
                te_r, we_r = run_ph(s, mid_rel, t_rel)
                if te_r == (N, N, N, 7):
                    return w_rel + we_r
    return None


# ==============================================================================
# 4. Solving Left-Stripped s_p = (2, 2, s_{P0+1}, ..., s_N) (NO right-lifting issues!)
# ==============================================================================
def jump_all_zero_to_O1(b, O1, c_cur):
    if O1 == b + 1:
        return [(0, O1), (1, O1)] if c_cur % 2 == 0 else [(1, O1), (0, O1)]
    if c_cur % 2 == 1:
        return [(1, O1 - 2), (0, O1), (1, O1)]
    return [(0, O1 - 1), (1, O1), (0, O1)]

def solve_on_sp_dir(s_p, c1_wt=2):
    """Solves left-stripped pattern s_p (where P0 == 1) directly to (N, N, N, 7)."""
    N = len(s_p) - 1
    evp = [i for i in range(2, N - 1, 2) if s_p[i] == 2]
    e, E = evp[0], evp[-1]
    evL = [i for i in range(2, e, 2) if s_p[i] == 1]
    odL = [i for i in range(3, e, 2) if s_p[i] >= 1]
    od2_L = [i for i in range(3, e, 2) if s_p[i] == 2]
    evR = [i for i in range(E + 2, N - 1, 2) if s_p[i] == 1]
    odR = [i for i in range(E + 1, N - 1, 2) if s_p[i] >= 1]
    od2_R = [i for i in range(E + 1, N - 1, 2) if s_p[i] == 2]
    f1 = evL[0] if evL else e
    lam = evR[-1] if evR else E
    O_star = min(i for i in range(lam + 1, N, 2) if s_p[i] == 2)

    # --- Branch A: Pure binary core (neither (1, e) nor (E, O_star) has odd peaks) -> Lemma A + B1! ---
    if not od2_L and not [i for i in od2_R if i < O_star]:
        s_core = tuple(s_p[:O_star + 1]) + (2,)
        s_core_bin = tuple(1 if (e < i < E and i % 2 == 1 and s_p[i] == 2) else s_p[i] for i in range(O_star + 1)) + (2,)
        w_c = cf.try_closed_form_dir(s_core_bin)
        if w_c and w_c.endswith('yx'):
            if O_star == N - 1:
                try:
                    lib.verify_word(s_p, w_c, directed=True)
                    return w_c
                except AssertionError:
                    pass
            sc = lib.Sched(s_p, E - 1, directed=True)
            sc.go(1, E)
            sc_init = lib.Sched(s_core, E - 1, directed=True); sc_init.go(1, E)
            t = sc.t; w_mid = w_c[len(sc_init.word):-2]
            ok = True
            for ch in w_mid:
                t = lib.step(s_p, t, ch, directed=True)
                if t is None: ok = False; break
            if ok and t == (O_star, O_star, O_star, 7):
                ph_end_a = [(2, N), (0, N)] if O_star == N - 1 else [(1, N - 1), (2, N), (0, N)]
                te, we = run_ph(s_p, ph_end_a, t)
                if te == (N, N, N, 7):
                    full = sc.word + w_mid + we
                    try:
                        lib.verify_word(s_p, full, directed=True)
                        return full
                    except AssertionError:
                        pass
        # Also if not evL (rL == 0 on s_core) and evR_c non-empty and odL non-empty (e.g. after inner-stripping P_last!):
        evR_c0 = [i for i in range(E + 2, O_star, 2) if s_p[i] == 1]
        odR_c0 = [i for i in range(E + 1, O_star, 2) if s_p[i] == 1]
        if not evL and evR_c0 and s_p[e - 1] == 1:
            for pre_r0 in [
                [(1, E), (2, e - 1), (1, O_star - 2), (0, O_star), (2, O_star + 1), (0, O_star + 1)],
                [(1, E), (1, evR_c0[-1]), (0, O_star - 1), (1, O_star), (0, O_star), (2, O_star + 1), (0, O_star + 1)],
            ]:
                w_c0 = exec_phases(s_core, E - 1, pre_r0)
                if w_c0 and w_c0.endswith('yx'):
                    if O_star == N - 1: return w_c0
                    sc = lib.Sched(s_p, E - 1, directed=True); wm = w_c0[len(sc.word):-2]; tc = sc.t
                    for ch in wm: tc = lib.step(s_p, tc, ch, directed=True)
                    if tc == (O_star, O_star, O_star, 7):
                        te, we = run_ph(s_p, [(1, N - 1), (2, N), (0, N)], tc)
                        if te == (N, N, N, 7): return sc.word + wm + we

    # --- Branch B: Peak-L (no odd peak in (E, O_star), od2_L non-empty) ---
    if od2_L and not [i for i in od2_R if i < O_star]:
        s_core = tuple(s_p[:O_star + 1]) + (2,)
        N_c = len(s_core) - 1
        # B.1: Try Lemma A on binary-flattened left wing and middle (succeeds whenever C <= P1 - 1 before B = O_star!)
        s_bin = tuple(1 if (2 < i < E and i % 2 == 1 and s_core[i] == 2) else s_core[i] for i in range(N_c + 1))
        w_b = cf.try_closed_form_dir(s_bin)
        if w_b and w_b.endswith('yx'):
            sc_init = lib.Sched(s_core, E - 1, directed=True); sc_init.go(1, E)
            sc = lib.Sched(s_p, E - 1, directed=True); sc.go(1, E)
            t = sc.t; w_mid = w_b[len(sc_init.word):-2]
            ok = True
            for ch in w_mid:
                t = lib.step(s_p, t, ch, directed=True)
                if t is None: ok = False; break
            if ok and t == (O_star, O_star, O_star, 7):
                ph_end = [(2, N), (0, N)] if O_star == N - 1 else [(1, N - 1), (2, N), (0, N)]
                te, we = run_ph(s_p, ph_end, t)
                if te == (N, N, N, 7):
                    full = sc.word + w_mid + we
                    try:
                        lib.verify_word(s_p, full, directed=True)
                        return full
                    except AssertionError:
                        pass

        # B.2: Super-Odd-Peak P1 on s_core (lifted to s_p via (O_star, O_star, O_star, 7) or direct on s_p!)
        if evL and evR and [i for i in odR if i < O_star]:
            P1 = od2_L[0]
            odR_c = [i for i in range(E + 1, O_star, 2) if s_p[i] == 1]
            evR_c = [i for i in range(E + 2, O_star, 2) if s_p[i] == 1]
            lam_c = evR_c[-1]; alpha_c = odR_c[-1]

            def try_core_phases(ph_c):
                w_c = exec_phases(s_core, E - 1, [(1, E)] + ph_c)
                if not w_c or not w_c.endswith('yx'): return None
                if O_star == N - 1: return w_c
                sc_i = lib.Sched(s_core, E - 1, directed=True); sc_i.go(1, E)
                sc = lib.Sched(s_p, E - 1, directed=True); sc.go(1, E)
                t = sc.t; wm = w_c[len(sc_i.word):-2]
                for ch in wm:
                    t = lib.step(s_p, t, ch, directed=True)
                    if t is None: return None
                if t == (O_star, O_star, O_star, 7):
                    te, we = run_ph(s_p, [(1, N - 1), (2, N), (0, N)], t)
                    if te == (N, N, N, 7):
                        full = sc.word + wm + we
                        lib.verify_word(s_p, full, directed=True)
                        return full
                return None

            # Universal mu == O_star - 1 theorem (NO condition on (f1, P1) needed!!):
            if lam_c == O_star - 1 and odL[0] < f1:
                k1 = odL[0]; r1 = odR_c[0]
                mu = next(i for i in evR_c if i > r1)
                q1 = max(i for i in odR_c if i < mu)
                e0 = max([i for i in evR_c if i < r1], default=E)
                ph_mu = cf.reach_mu_phase1(s_core, E, k1, f1, e0, r1, q1, mu, evR_c)
                if mu == O_star - 1:
                    for tl in [
                        [(1, O_star), (0, O_star), (2, O_star + 1), (0, O_star + 1)],
                        [(0, O_star), (1, O_star), (2, O_star + 1), (0, O_star + 1)],
                    ]:
                        res = try_core_phases(ph_mu + tl)
                        if res: return res

                # Non-(E, E, 1) Exception Family for general P1 > f1 (not just P1 == f1 + 1!):
                P_last = od2_L[-1]
                ev_after_Plast = [i for i in evL if i > P_last]
                if ev_after_Plast:
                    f_last = ev_after_Plast[-1]
                    if lib.M_od(s_p, f_last, e) == 0:
                        a_star = max([f_last] + [i for i in range(e, E) if s_p[i] >= 1])
                        if s_p[E - 1] >= 1 or a_star % 2 == 1:
                            a_st = (E - 1) if s_p[E - 1] >= 1 else a_star
                            for P_piv in [P1, P_last]:
                                ev_aft_piv = [i for i in evL if i > P_piv]
                                if not ev_aft_piv: continue
                                for f_piv in ([ev_aft_piv[0], ev_aft_piv[-1]] if len(ev_aft_piv) > 1 else [ev_aft_piv[0]]):
                                    for mid_ep in [
                                        [(1, mu), (2, f_piv), (0, O_star - 1), (1, O_star), (0, O_star), (2, O_star + 1), (0, O_star + 1)],
                                        [(1, O_star - 1), (2, f_piv), (0, O_star), (1, O_star), (2, O_star + 1), (0, O_star + 1)],
                                        [(1, O_star - 2), (2, f_piv), (0, O_star), (1, O_star), (2, O_star + 1), (0, O_star + 1)],
                                    ]:
                                        ph_EP1 = [(2, P_piv - 1)] + ([(0, E - 1)] if a_st < E - 1 else []) + [(1, E)] + mid_ep
                                        w_c = exec_phases(s_core, a_st, ph_EP1)
                                        if w_c and w_c.endswith('yx'):
                                            if O_star == N - 1: return w_c
                                            sc_tmp = lib.Sched(s_p, a_st, directed=True)
                                            wm = w_c[len(sc_tmp.word):-2]; t_chk = sc_tmp.t; ok = True
                                            for ch in wm:
                                                t_chk = lib.step(s_p, t_chk, ch, directed=True)
                                                if t_chk is None: ok = False; break
                                            if ok and t_chk == (O_star, O_star, O_star, 7):
                                                te, we = run_ph(s_p, [(1, N - 1), (2, N), (0, N)], t_chk)
                                                if te == (N, N, N, 7): return sc_tmp.word + wm + we

            # Universal rR == 6 (alpha_c < lam_c, i.e., (lam_c, O_star) all zeros) Super-Peak completion:
            if alpha_c < lam_c and odL and odL[0] < f1 and not [i for i in odL if f1 < i < P1]:
                k1_r6 = odL[0]; r1_r6 = odR_c[0]
                mu_r6 = next(i for i in evR_c if i > r1_r6)
                q1_r6 = max(i for i in odR_c if i < mu_r6)
                e0_r6 = max([i for i in evR_c if i < r1_r6], default=E)
                ph_e0_r6 = cf.reach_e0(E, e0_r6, r1_r6, k1_r6, evR_c)
                c_r6_cands = [P1 - 1] if P1 - 1 == f1 else [P1 - 1, f1]
                for c_r6 in c_r6_cands:
                    ph_mu_r6 = ph_e0_r6 + [(1, q1_r6), (2, c_r6)] + ([(0, mu_r6)] if q1_r6 == mu_r6 - 1 else [(0, mu_r6 - 1), (1, mu_r6), (0, mu_r6)])
                    if mu_r6 < lam_c and not [i for i in odR_c if mu_r6 < i < lam_c]:
                        ph_lam_list = [ph_mu_r6 + [(1, lam_c), (0, lam_c)]]
                    elif mu_r6 == lam_c:
                        ph_lam_list = [ph_mu_r6]
                    else:
                        q_lam_r6 = max(i for i in odR_c if mu_r6 < i < lam_c)
                        p2_r6 = next((i for i in odL if c_r6 < i < P1), P1)
                        ph_lam_list = [
                            ph_mu_r6 + [(0, lam_c - 1), (2, P1 - 1), (1, lam_c)],
                            ph_mu_r6 + [(1, q_lam_r6), (2, P1 - 1), (0, lam_c - 1), (1, lam_c)],
                        ]
                    tail_sp_r6 = [(2, N), (0, N)] if O_star == N - 1 else [(1, N - 1), (2, N), (0, N)]
                    for ph_lam_r6 in ph_lam_list:
                        for mid_r6 in (
                            [[(1, O_star), (0, O_star)] + tail_sp_r6, [(2, P1 - 1), (1, O_star), (0, O_star)] + tail_sp_r6]
                            if lam_c == O_star - 1 else
                            [
                                [(0, O_star - 2), (1, O_star - 1), (1, O_star)] + tail_sp_r6,
                                [(2, P1 - 1), (0, O_star - 2), (1, O_star - 1), (1, O_star)] + tail_sp_r6,
                            ]
                        ):
                            w_r6 = exec_phases(s_p, E - 1, [(1, E)] + ph_lam_r6 + mid_r6)
                            if w_r6: return w_r6

            if not [i for i in odL if f1 < i < P1]:

                mid_P = ([(2, P1 - 1)] if P1 - 1 > f1 else []) + [(0, O_star - 1), (1, O_star), (0, O_star), (2, O_star + 1), (0, O_star + 1)]
                if not [i for i in odL if i < f1]:
                    res = try_core_phases([(1, lam_c - 1), (2, f1), (0, alpha_c)] + mid_P)
                    if res: return res
                    res = try_core_phases([(1, lam_c - 1), (2, f1), (0, alpha_c), (0, O_star - 1), (1, O_star), (0, O_star), (2, O_star + 1), (0, O_star + 1)])
                    if res: return res
                    if alpha_c <= O_star - 2:
                        res = try_core_phases([(1, lam_c - 1), (2, f1), (0, alpha_c + 1), (2, P1)] + ([(1, O_star - 1), (0, O_star - 1)] if alpha_c + 2 < O_star else []) + [(1, O_star), (2, O_star + 1), (0, O_star + 1)])
                        if res: return res
                if s_p[lam_c - 1] == 1:
                    res = try_core_phases([(1, lam_c - 1), (2, f1), (0, lam_c), (0, alpha_c)] + mid_P)
                    if res: return res

                # Super-Odd-Peak when lam_c == O_star - 1 (s_core[N_c - 2] == 1)!
                if lam_c == O_star - 1 and odL[0] < f1:
                    k1 = odL[0]; r1 = odR_c[0]
                    mu = next(i for i in evR_c if i > r1)
                    q1 = max(i for i in odR_c if i < mu)
                    e0 = max([i for i in evR_c if i < r1], default=E)
                    ph_mu = cf.reach_mu_phase1(s_core, E, k1, f1, e0, r1, q1, mu, evR_c)
                    tails = []
                    if mu == O_star - 1:
                        tails.append([(1, O_star), (0, O_star), (2, O_star + 1), (0, O_star + 1)])
                        if P1 - 1 > f1:
                            tails.append([(2, P1 - 1), (1, O_star), (0, O_star), (2, O_star + 1), (0, O_star + 1)])
                    else:
                        tails.append([(0, O_star - 2), (1, O_star - 1), (1, O_star), (0, O_star), (2, O_star + 1), (0, O_star + 1)])
                        if P1 - 1 > f1:
                            tails.append([(2, P1 - 1), (0, O_star - 2), (1, O_star - 1), (1, O_star), (0, O_star), (2, O_star + 1), (0, O_star + 1)])
                        if not [i for i in odR_c if mu < i < O_star - 1]:
                            tails.append([(1, O_star - 1), (0, O_star - 1)] + ([(2, P1 - 1)] if P1 - 1 > f1 + 1 else []) + [(1, O_star), (0, O_star), (2, O_star + 1), (0, O_star + 1)])
                    for tl in tails:
                        res = try_core_phases(ph_mu + tl)
                        if res: return res

                    # Non-(E, E, 1) Exception Family (when P1 == f1 + 1 and exists even 1 f_last in (P1, e) with M_od(f_last, e) == 0)!
                    ev_after_P1 = [i for i in evL if i > P1]
                    if ev_after_P1 and P1 == f1 + 1:
                        f_last = ev_after_P1[-1]
                        if lib.M_od(s_p, f_last, e) == 0:
                            a_star = max([f_last] + [i for i in range(e, E) if s_p[i] >= 1])
                            if s_p[E - 1] >= 1 or a_star % 2 == 1:
                                # Odd a_star (including E - 1 when s_p[E - 1] >= 1!): reaches (E, E, P1, 7) on s_core!
                                a_st = (E - 1) if s_p[E - 1] >= 1 else a_star
                                ph_EP1 = [(2, f1)] + ([(0, E - 1)] if a_st < E - 1 else []) + [(1, E), (1, mu), (2, f_last), (0, O_star - 1), (1, O_star), (0, O_star), (2, O_star + 1), (0, O_star + 1)]
                                w_c = exec_phases(s_core, a_st, ph_EP1)
                                if w_c and w_c.endswith('yx'):
                                    if O_star == N - 1: return w_c
                                    t_chk, _ = run_ph(s_p, [], (a_st, 1, 1, 7))
                                    sc_tmp = lib.Sched(s_p, a_st, directed=True)
                                    wm = w_c[len(sc_tmp.word):-2]
                                    ok = True
                                    for ch in wm:
                                        t_chk = lib.step(s_p, t_chk, ch, directed=True)
                                        if t_chk is None: ok = False; break
                                    if ok and t_chk == (O_star, O_star, O_star, 7):
                                        te, we = run_ph(s_p, [(1, N - 1), (2, N), (0, N)], t_chk)
                                        if te == (N, N, N, 7): return sc_tmp.word + wm + we
                            else:
                                # Even a_star (e.g. f_last when e == E, or an even peak/1 in [e, E) with (a_star, E) all 0!):
                                # Start at I(a_star - 1): B -> a_star -> (a_star, a_star, 1, 7), then B -> E, A -> E -> (E, E, 2, 7)!
                                qL = max(i for i in range(3, f1, 2) if s_p[i] == 1)
                                ph_even = [(1, a_star)] + ([(1, E), (0, E)] if a_star < E else [])
                                # From (E, E, 2 or 1, 7):
                                sc_e = lib.Sched(s_core, a_star - 1, directed=True)
                                t_e, w_e = run_ph(s_core, ph_even, sc_e.t)
                                if t_e is not None:
                                    # Try reaching (E + 1, mu, f1, 7) -> (0, O_star - 1), (1, O_star), ...
                                    for m_try in [
                                        [(1, mu), (2, f1), (0, O_star - 1), (1, O_star), (0, O_star), (2, O_star + 1), (0, O_star + 1)],
                                        [(1, r1), (2, k1), (1, mu), (2, f1), (0, O_star - 1), (1, O_star), (0, O_star), (2, O_star + 1), (0, O_star + 1)],
                                        [(1, E + 1), (0, E + 1), (1, E + 2), (0, E + 2), (1, r1), (2, qL), (1, mu), (2, f1), (0, O_star - 1), (1, O_star), (0, O_star), (2, O_star + 1), (0, O_star + 1)],
                                    ]:
                                        t_f, w_f = run_ph(s_core, m_try, t_e)
                                        if t_f == (O_star + 1, O_star + 1, O_star + 1, 7):
                                            w_c = sc_e.word + w_e + w_f
                                            if O_star == N - 1:
                                                lib.verify_word(s_p, w_c, directed=True)
                                                return w_c
                                            sc_sp = lib.Sched(s_p, a_star - 1, directed=True)
                                            wm = (w_e + w_f)[:-2]
                                            t_sp = sc_sp.t; ok = True
                                            for ch in wm:
                                                t_sp = lib.step(s_p, t_sp, ch, directed=True)
                                                if t_sp is None: ok = False; break
                                            if ok and t_sp == (O_star, O_star, O_star, 7):
                                                te, we = run_ph(s_p, [(1, N - 1), (2, N), (0, N)], t_sp)
                                                if te == (N, N, N, 7):
                                                    full = sc_sp.word + wm + we
                                                    lib.verify_word(s_p, full, directed=True)
                                                    return full

    # --- Branch C: Peak-R (od2_R has at least one inner odd peak O1 < O_star, or general od2_R non-empty!) ---
    if od2_R:
        O1 = od2_R[0]
        ev0 = [i for i in range(E + 2, O1, 2) if s_p[i] == 1]
        od0 = [i for i in range(E + 1, O1, 2) if s_p[i] == 1]

        # C.1: Terminal-B / Golden Bridge when s_p[N - 2] == 1 (requires C = 1 to have weight 2):
        if s_p[N - 2] == 1 and c1_wt == 2:
            if s_p[2] == 1:
                w = exec_phases(s_p, E - 1, [(1, E), (1, N - 2), (0, O1), (2, N), (0, N)])
                if w: return w
            if s_p[2] == 0 and not od0:
                w = exec_phases(s_p, E - 1, [(1, E), (1, N - 2), (0, O1 - 1), (1, N - 1), (2, N), (0, N)])
                if w: return w
            if evL and ev0 and (s_p[N - 3] >= 1 or not [i for i in range(3, f1, 2) if s_p[i] >= 1]):
                w = exec_phases(s_p, E - 1, [(1, E), (1, N - 3), (2, f1), (0, O1), (2, N), (0, N)])
                if w: return w

        # C.1a: Direct s_p[2] == 1 right-crossing across [E, O1] when s_p[3] == 0 (e.g. e == E == 4 with odL == []):
        if s_p[2] == 1 and ev0 and c1_wt == 2:
            b_l0 = ev0[-1]
            sc_c1a = lib.Sched(s_p, E - 1, directed=True)
            tc_1a, wc_1a = run_ph(s_p, [(1, E), (1, b_l0 - 1), (0, O1 - 1)], sc_c1a.t)
            if tc_1a is not None:
                tc_1az = lib.step(s_p, tc_1a, 'z', directed=True)
                if tc_1az is not None:
                    tc_1ae, wc_1ae = run_ph(s_p, [(2, E)], tc_1az)
                    if tc_1ae and tc_1ae[0] == O1 and tc_1ae[2] == E:
                        ev_af_1a = [i for i in range(O1 + 1, N - 1, 2) if s_p[i] == 1]
                        if od0 and ev_af_1a:
                            fR_1a = ev_af_1a[0]; lam_1a = ev_af_1a[-1]
                            O_st_1a = min(i for i in range(lam_1a + 1, N, 2) if s_p[i] == 2)
                            Op_1a = max(i for i in od2_R if i < fR_1a)
                            pre_1a = [(2, od0[-1]), (2, Op_1a - 1)] + ([(1, fR_1a)] if fR_1a == Op_1a + 1 else [(0, fR_1a - 1), (1, fR_1a)])
                            tv_1a, wv_1a = run_ph(s_p, pre_1a, tc_1ae)
                            if tv_1a and tv_1a[:2] == (fR_1a, fR_1a) and (tv_1a[3] & 3) == 3:
                                we_1a = finish_from_even_Ok(s_p, tv_1a, O_st_1a, lam_1a)
                                if we_1a:
                                    full_1a = sc_c1a.word + wc_1a + 'z' + wc_1ae + wv_1a + we_1a
                                    lib.verify_word(s_p, full_1a, directed=True)
                                    return full_1a
                        w_fin_1a = finish_from_O1_anchor(s_p, tc_1ae, O1, E) or finish_from_O1_O1_c(s_p, tc_1ae, O1, E)
                        if w_fin_1a:
                            full_1a = sc_c1a.word + wc_1a + 'z' + wc_1ae + w_fin_1a
                            lib.verify_word(s_p, full_1a, directed=True)
                            return full_1a

        # C.1b: General Lemma A prefix reduction on s_O1 = s_p[:O1 + 1] + (2,)!
        s_O1_bin = tuple(1 if (2 < i < E and i % 2 == 1 and s_p[i] == 2) else s_p[i] for i in range(O1 + 1)) + (2,)
        if any(s_O1_bin[i] == 1 for i in range(2, e, 2)) or any(s_O1_bin[i] == 1 for i in range(E + 2, O1, 2)):
            w_o1_cf = cf.try_closed_form_dir(s_O1_bin)
            if w_o1_cf and w_o1_cf.endswith('yx'):
                # Replay w_o1_cf[:-2] on s_p: check if it reaches (O1, O1, O1, 7) (or hits (O1, O1, E, 7) along the way!)
                z0 = w_o1_cf.index('z')
                sc_o1 = lib.Sched(s_p, z0 - 1, directed=True)
                t_cur = sc_o1.t; pref_w = []; ok_o1 = True; hit_anchors = []
                for ch in w_o1_cf[len(sc_o1.word):-2]:
                    # Branch before (0, O1) if at (a_lt_O1, O1 - 2, c_cur < e, 7) to hit (O1, O1 - 1, e, 7) or relay across O_piv > O1!
                    if t_cur[1] == O1 - 2 and t_cur[0] < O1 and t_cur[2] < e and t_cur[3] == 7 and not od2_L:
                        if t_cur[0] % 2 == 1:
                            tb, wb = run_ph(s_p, [(2, e - 1), (0, O1)], t_cur)
                            if tb == (O1, O1 - 1, e, 7):
                                hit_anchors.append((tb, ''.join(pref_w) + wb))
                        elif t_cur[0] == O1 - 1 and len(od2_R) >= 2:
                            ev_af2 = [i for i in range(O1 + 1, N - 1, 2) if s_p[i] == 1]
                            if ev_af2 and ev_af2[0] > od2_R[1]:
                                lam2 = ev_af2[-1]; O_st2 = min(i for i in range(lam2 + 1, N, 2) if s_p[i] == 2)
                                Op2 = max(i for i in od2_R if i < ev_af2[0])
                                for pre_op2 in [
                                    ([(2, e - 1)] if t_cur[2] < e - 1 else []) + [(0, O1), (0, Op2), (2, Op2 - 1)] + ([(1, ev_af2[0])] if ev_af2[0] == Op2 + 1 else [(0, ev_af2[0] - 1), (1, ev_af2[0])]),
                                    [(2, e), (0, O1 + 1), (2, O1)] + ([(2, Op2 - 1)] if Op2 - 1 > O1 else []) + [(0, ev_af2[0] - 1), (1, ev_af2[0])],
                                ]:
                                    tv2, wv2 = run_ph(s_p, pre_op2, t_cur)
                                    if tv2 and tv2[:2] == (ev_af2[0], ev_af2[0]) and (tv2[3] & 3) == 3:
                                        we2 = finish_from_even_Ok(s_p, tv2, O_st2, lam2)
                                        if we2:
                                            full2 = sc_o1.word + ''.join(pref_w) + wv2 + we2
                                            lib.verify_word(s_p, full2, directed=True)
                                            return full2
                    # Also branch at (b_last, b_last, c_cur < e, 7) when u0 > b_last and O2 == O1 + 2 (rf1!):
                    if ev0 and t_cur[0] == t_cur[1] == ev0[-1] and t_cur[2] < e and t_cur[3] == 7 and not od2_L and od0 and od0[-1] > ev0[-1] and odL and len(od2_R) >= 2 and od2_R[1] == O1 + 2 and s_p[O1 + 1] == 0:
                        q_last_L = odL[-1]
                        if q_last_L > t_cur[2]:
                            tb_q, wb_q = run_ph(s_p, [(1, od0[-1]), (2, q_last_L), (0, O1 - 1), (1, O1 - 2), (2, e), (0, O1 + 1), (2, O1)], t_cur)
                            if tb_q == (O1 + 2, O1, O1, 7):
                                ev_af2 = [i for i in range(O1 + 1, N - 1, 2) if s_p[i] == 1]
                                if ev_af2:
                                    lam2 = ev_af2[-1]; O_st2 = min(i for i in range(lam2 + 1, N, 2) if s_p[i] == 2)
                                    Op2 = max(i for i in od2_R if i < ev_af2[0])
                                    tv2, wv2 = run_ph(s_p, ([(2, Op2 - 1)] if Op2 - 1 > O1 else []) + [(0, ev_af2[0] - 1), (1, ev_af2[0])], tb_q)
                                    if tv2 and tv2[:2] == (ev_af2[0], ev_af2[0]) and (tv2[3] & 3) == 3:
                                        we2 = finish_from_even_Ok(s_p, tv2, O_st2, lam2)
                                        if we2:
                                            full_q = sc_o1.word + ''.join(pref_w) + wb_q + wv2 + we2
                                            lib.verify_word(s_p, full_q, directed=True)
                                            return full_q
                    if t_cur[0] == O1 - 1 and t_cur[1] < O1 and t_cur[1] % 2 == 1 and s_p[t_cur[1]] >= 1 and t_cur[2] < E and t_cur[3] == 7:
                        for pre_anc in ([[(0, O1), (2, E)], [(2, E), (0, O1)]] if O1 - 1 > E else [[(0, O1), (2, E)]]):
                            tb_a, wb_a = run_ph(s_p, pre_anc, t_cur)
                            if tb_a and tb_a[0] == O1 and tb_a[2] == E and (tb_a[3] & 5) == 5:
                                hit_anchors.append((tb_a, ''.join(pref_w) + wb_a))
                    t_cur = lib.step(s_p, t_cur, ch, directed=True)
                    if t_cur is None: ok_o1 = False; break
                    pref_w.append(ch)
                    if (t_cur[0] == O1 and t_cur[1] <= O1 and t_cur[2] == E and (t_cur[3] & 5) == 5) or t_cur == (O1, O1 - 1, e, 7):
                        hit_anchors.append((t_cur, ''.join(pref_w)))
                for t_anc, w_anc in hit_anchors:
                    if t_anc[2] == E:
                        w_fin = finish_from_O1_anchor(s_p, t_anc, O1, E) or finish_from_O1_O1_c(s_p, t_anc, O1, E)
                    else:
                        w_fin = finish_from_O1_e_anchor(s_p, t_anc, O1, O1 - 1, e, E)
                    if w_fin:
                        full = sc_o1.word + w_anc + w_fin
                        lib.verify_word(s_p, full, directed=True)
                        return full
                if ok_o1 and t_cur == (O1, O1, O1, 7):
                    w_fin = finish_from_O1_O1_c(s_p, t_cur, O1, E)
                    if w_fin:
                        full = sc_o1.word + ''.join(pref_w) + w_fin
                        lib.verify_word(s_p, full, directed=True)
                        return full

        # C.1c: Direct (E, E, 1, 7) Golden Bridge across Or when s_p[2] == 0, not od0, ev0[-1] == O1 - 1, and s_p[Or + 1] == 1!
        if not od0 and ev0 and ev0[-1] == O1 - 1 and s_p[2] == 0 and len(od2_R) >= 2:
            ev_af_O1 = [i for i in range(O1 + 1, N - 1, 2) if s_p[i] == 1]
            if ev_af_O1:
                lam_r = ev_af_O1[-1]
                Or_cands = [i for i in od2_R if O1 < i < lam_r and s_p[i + 1] == 1]
                for Or_p in reversed(Or_cands):
                    od_af_Or = [i for i in range(Or_p + 2, N - 1, 2) if s_p[i] >= 1]
                    gb_cands = [
                        [(1, E), (1, Or_p), (0, O1 - 1), (1, N - 1), (0, O1), (2, N), (0, N)],
                    ]
                    if od_af_Or and odL:
                        u_af = od_af_Or[0]; q_odL = odL[-1]
                        gb_cands.append([(1, E), (1, Or_p), (0, O1 - 1), (1, u_af), (2, q_odL)] + ([(2, e)] if q_odL == e - 1 else []) + [(1, N - 1), (0, Or_p), (2, N), (0, N)])
                    for ph_gb in gb_cands:
                        w_gb = exec_phases(s_p, E - 1, ph_gb)
                        if w_gb: return w_gb

        if not od2_L:
            if not ev0 and od0:
                r1_0 = od0[0]
                if s_p[O1 - 2] == 1:
                    for a0_e0, pre_e0 in [
                        (E - 1, ([(2, f1 - 1)] if f1 > 2 else []) + [(1, E), (0, O1 - 1), (1, O1 - 2), (0, O1)]) if (evL and f1 == e - 2 and lib.M_od(s_p, 1, E) == 0 and len(od2_R) >= 2 and od2_R[1] == O1 + 2 and s_p[O1 + 1] == 0) else (0, []),
                        (E - 1, [(1, E), (1, O1 - 2), (2, e - 1), (0, O1)]),
                        (E - 1, [(1, E), (0, r1_0 - 1), (1, O1 - 2), (2, e - 1), (0, O1)]) if r1_0 > E + 1 else (0, []),
                    ]:
                        if not pre_e0: continue
                        sc_e0 = lib.Sched(s_p, a0_e0, directed=True)
                        te0, we0 = run_ph(s_p, pre_e0, sc_e0.t)
                        if te0 == (O1, O1 - 1, e, 7):
                            w_fin = finish_from_O1_e_anchor(s_p, te0, O1, O1 - 1, e, E)
                            if w_fin:
                                full = sc_e0.word + we0 + w_fin
                                lib.verify_word(s_p, full, directed=True)
                                return full
                        elif te0 == (O1, O1 - 2, e, 7):
                            tb2, wb2 = run_ph(s_p, [(0, O1 + 1), (2, O1)], te0)
                            ev_af2 = [i for i in range(O1 + 1, N - 1, 2) if s_p[i] == 1]
                            if tb2 == (O1 + 2, O1, O1, 7) and ev_af2:
                                lam2 = ev_af2[-1]; O_st2 = min(i for i in range(lam2 + 1, N, 2) if s_p[i] == 2)
                                Op2 = max(i for i in od2_R if i < ev_af2[0])
                                tv2, wv2 = run_ph(s_p, ([(2, Op2 - 1)] if Op2 - 1 > O1 else []) + ([(0, ev_af2[0] - 1)] if ev_af2[0] - 1 > O1 + 2 else []) + [(1, ev_af2[0])], tb2)
                                if tv2 and tv2[:2] == (ev_af2[0], ev_af2[0]) and (tv2[3] & 3) == 3:
                                    we2 = finish_from_even_Ok(s_p, tv2, O_st2, lam2)
                                    if we2:
                                        full2 = sc_e0.word + we0 + wb2 + wv2 + we2
                                        lib.verify_word(s_p, full2, directed=True)
                                        return full2
                # General zero-odd-L multi-peak relay across [e, E] when r1_0 >= E + 3 and O2 == O1 + 2:
                if evL and not odL and r1_0 >= E + 3 and e < E and len(od2_R) >= 2 and od2_R[1] == O1 + 2 and s_p[O1 + 1] == 0 and lib.M_od(s_p, 1, E) == 0:
                    O2_0 = od2_R[1]
                    ev_af2 = [i for i in range(O2_0 + 1, N - 1, 2) if s_p[i] == 1]
                    if ev_af2:
                        v0_af = ev_af2[0]; lam2 = ev_af2[-1]
                        O_st2 = min(i for i in range(lam2 + 1, N, 2) if s_p[i] == 2)
                        Op2 = max(i for i in od2_R if i < v0_af)
                        sc_mp0 = lib.Sched(s_p, E - 1, directed=True)
                        pre_mp0 = ([(2, f1 - 1)] if f1 > 2 else []) + [(1, E), (0, O1 - 1), (1, r1_0 - 2), (2, e), (0, O1 + 1), (1, r1_0), (2, O1 - 1)]
                        for mid_mp0 in [
                            [(1, v0_af)],
                            [(1, O2_0)] + ([(2, Op2 - 1)] if Op2 - 1 > O1 else []) + ([(0, v0_af - 1)] if v0_af - 1 > O2_0 + 1 else []) + [(1, v0_af)],
                            [(1, O2_0), (2, Op2)] + ([(0, v0_af - 1)] if v0_af - 1 > O2_0 + 1 else []) + [(1, v0_af)],
                        ]:
                            tv2, wv2 = run_ph(s_p, pre_mp0 + mid_mp0, sc_mp0.t)
                            if tv2 and tv2[:2] == (v0_af, v0_af) and (tv2[3] & 3) == 3:
                                we2 = finish_from_even_Ok(s_p, tv2, O_st2, lam2)
                                if we2:
                                    full_mp0 = sc_mp0.word + wv2 + we2
                                    lib.verify_word(s_p, full_mp0, directed=True)
                                    return full_mp0
            # C.1d-bis: When s_p[e - 1] == 1 and s_p[E + 1] == 1 and f1 == 2, reach (O1, O1 - 1, e, 7) via (E + 1, E + 1, e - 1, 7)!
            if f1 == 2 and s_p[e - 1] == 1 and s_p[E + 1] == 1 and O1 >= E + 3:
                sc_e1 = lib.Sched(s_p, E - 1, directed=True)
                for ph_e1 in [
                    [(1, E), (2, 2), (2, e - 1), (0, O1)],
                    [(1, E), (2, 2), (2, e - 1), (0, E + 2), (1, O1 - 2), (0, O1)],
                    [(1, E), (2, 2), (2, e - 1), (1, O1 - 2), (0, O1)],
                ]:
                    te1_s, we1_s = run_ph(s_p, ph_e1, sc_e1.t)
                    if te1_s == (O1, O1 - 1, e, 7):
                        wf_e1 = finish_from_O1_e_anchor(s_p, te1_s, O1, O1 - 1, e, E)
                        if wf_e1:
                            full_e1 = sc_e1.word + we1_s + wf_e1
                            lib.verify_word(s_p, full_e1, directed=True)
                            return full_e1
            # C.1d: (E, E, f1, 7) middle-odd-1 entry when e < E, s_p[E - 1] >= 1, and f1 < e!
            if e < E and s_p[E - 1] >= 1 and f1 < e:
                e_prev = max(i for i in range(e, E, 2) if s_p[i] == 2)
                for pre_Ef in [
                    [(1, E - 1), (2, f1), (0, E)],
                    [(1, e_prev), (0, E - 2), (1, E - 1), (2, f1), (0, E)],
                ]:
                    sc_ef = lib.Sched(s_p, e_prev - 1, directed=True)
                    tef, wef = run_ph(s_p, pre_Ef, sc_ef.t)
                    if tef == (E, E, f1, 7):
                        # Jump across arbitrary binary (E, O1)!
                        b_l = ev0[-1] if ev0 else E
                        for jmp in [
                            [(0, O1 - 1), (1, O1), (0, O1)],
                            [(0, b_l), (1, O1 - 1), (0, O1), (1, O1)],
                            [(0, b_l), (1, O1 - 2), (2, e - 1), (0, O1)],
                        ]:
                            to1, wo1 = run_ph(s_p, jmp, tef)
                            if to1 and to1[0] == O1 and to1[1] in (O1, O1 - 1) and to1[2] <= E + 1:
                                wf = finish_from_O1_e_anchor(s_p, to1, O1, O1 - 1, e, E) if to1 == (O1, O1 - 1, e, 7) else finish_from_O1_O1_c(s_p, to1, O1, E)
                                if wf:
                                    full = sc_ef.word + wef + wo1 + wf
                                    try:
                                        lib.verify_word(s_p, full, directed=True)
                                        return full
                                    except AssertionError:
                                        pass
            # Binary prefix [1 .. e - 1] sync when s_p[e - 1] == 1 and not od2_L: reaches (e, e, e - 1, 7)!
            if s_p[e - 1] == 1 and not any(s_p[i] == 2 for i in range(e + 1, E, 2)):
                tl2 = None; pref_l2 = None
                if evL and not [i for i in range(evL[0] + 1, e - 1, 2) if s_p[i] == 1]:
                    hL = evL[-1]
                    sc_h = lib.Sched(s_p, evL[0] - 1, directed=True)
                    t_h, w_h = run_ph(s_p, [(1, hL), (0, e - 2), (1, e - 1), (0, e - 1), (2, e - 1), (0, e)], sc_h.t)
                    if t_h == (e, e, e - 1, 7):
                        tl2 = t_h; pref_l2 = sc_h.word + w_h
                if tl2 is None:
                    s_left = tuple(s_p[:e]) + (2,)
                    w_left = complete_binary_suffix(s_left, 1)
                    sc_l = lib.Sched(s_p, 1, directed=True)
                    tl = sc_l.t; pl = []
                    for ch in w_left:
                        if tl == (e - 1, e - 1, e - 1, 7):
                            t_e2, w_e2 = run_ph(s_p, [(0, e)], tl)
                            if t_e2 == (e, e, e - 1, 7):
                                tl2 = t_e2; pref_l2 = sc_l.word + ''.join(pl) + w_e2
                            break
                        if tl[0] == e - 2 and tl[1] == e - 1 and (tl[3] & 3) == 3:
                            t_e1, w_e1 = run_ph(s_p, [(2, e - 1), (0, e - 1), (0, e)], tl)
                            if t_e1 == (e, e, e - 1, 7):
                                tl2 = t_e1; pref_l2 = sc_l.word + ''.join(pl) + w_e1
                            break
                        tl = lib.step(s_p, tl, ch, directed=True)
                        if tl is None: break
                        pl.append(ch)
                if tl2 == (e, e, e - 1, 7):
                    if e == E:
                        te1, we1 = run_ph(s_p, [(1, O1 - 1), (0, O1)], tl2)
                        if te1 == (O1, O1 - 1, E, 7):
                            w_fin = finish_from_O1_anchor(s_p, te1, O1, E)
                            if w_fin:
                                full = pref_l2 + we1 + w_fin
                                lib.verify_word(s_p, full, directed=True)
                                return full
                    if e < E and s_p[e + 1] <= 1:
                        t_z = lib.step(s_p, tl2, 'z', directed=True)
                        t_zy = lib.step(s_p, t_z, 'y', directed=True) if t_z else None
                        if t_zy is not None:
                            te2, we2 = run_ph(s_p, [(1, E), (0, O1)], t_zy)
                            if te2 == (O1, E, e, 7):
                                w_fin = finish_from_O1_e_anchor(s_p, te2, O1, E, e, E)
                                if w_fin:
                                    full = pref_l2 + 'zy' + we2 + w_fin
                                    lib.verify_word(s_p, full, directed=True)
                                    return full

        # C.2: Sync across binary prefix (E, O1) to (O1, O1, c0, m), then finish_from_O1_O1_c!
        cand_starts = [(E - 1, [(1, E)])]
        if not any(s_p[i] == 2 for i in range(3, E, 2)):
            od_bef_E = [i for i in range(3, E, 2) if s_p[i] == 1]
            for q_cand in ([i for i in od_bef_E if i < f1][-1:] + (od_bef_E[-1:] if od_bef_E else [])):
                if s_p[E - 1] >= 1 or q_cand < f1:
                    cand_starts.append((E - 1, ([(2, q_cand - 1)] if q_cand > 3 else []) + [(1, E)]))
                if q_cand < E - 1 and not any(s_p[i] >= 1 for i in range(q_cand + 1, e)):
                    cand_starts.append((q_cand, ([(2, q_cand - 1)] if q_cand > 3 else []) + [(0, e if s_p[2] == 1 else e - 1), (1, E)]))

        for a0, init_ph in cand_starts:
            sc0 = lib.Sched(s_p, a0, directed=True)
            t_st, w_st = run_ph(s_p, init_ph, sc0.t)
            if t_st is None or t_st[:2] != (E, E): continue
            c_init = t_st[2]
            no_odd_in_c_f1 = not [i for i in range(c_init + 2, f1, 2) if s_p[i] >= 1]

            mid_cands = []
            if not od0:
                if not ev0:
                    mid_cands.append(jump_all_zero_to_O1(E, O1, c_init))
                    if O1 >= E + 3:
                        mid_cands.append([(1, O1 - 1), (0, O1 - 1), (1, O1), (0, O1)])
                else:
                    b = ev0[-1]
                    if b == O1 - 1:
                        mid_cands.append([(1, O1 - 1), (0, O1), (1, O1)])
                    elif s_p[c_init + 1] == 0:
                        mid_cands.append([(1, b), (0, O1 - 1), (1, O1), (0, O1)])
                    elif not [i for i in range(c_init + 1, E, 2) if s_p[i] >= 1]:
                        # Zero-odd-after-c_init bridge when s_p[c_init + 1] == 1!
                        t_b6, w_b6 = run_ph(s_p, [(1, b), (0, O1), (2, E)], t_st)
                        if t_b6 and t_b6[0] == O1 and t_b6[2] == E and (t_b6[3] & 5) == 5:
                            w_fin6 = finish_from_O1_O1_c(s_p, t_b6, O1, E)
                            if w_fin6:
                                full = sc0.word + w_st + w_b6 + w_fin6
                                lib.verify_word(s_p, full, directed=True)
                                return full
            else:
                u0 = od0[-1]; r1 = od0[0]
                if not ev0:
                    if f1 < e and no_odd_in_c_f1:
                        mid_cands.append([(1, u0), (2, f1), (0, O1 - 1), (1, O1), (0, O1)])
                    if r1 == E + 1:
                        mid_cands.append([(1, O1 - 2), (2, e - 1), (0, O1)])
                    elif s_p[c_init + 1] == 0:
                        mid_cands.append([(1, O1 - 3), (0, r1 - 1), (1, O1 - 2), (2, e - 1), (0, O1)])
                else:
                    ev_after_r1 = [i for i in ev0 if i > r1]
                    if not ev_after_r1 and f1 < e and no_odd_in_c_f1:
                        b0 = ev0[-1]
                        mid_cands.append([(1, b0), (0, b0), (1, u0), (2, f1), (0, O1 - 1), (1, O1), (0, O1)])
                    elif ev_after_r1 and f1 < e:
                        b_last = ev0[-1]
                        mu0 = ev_after_r1[0]
                        q0 = max(i for i in od0 if i < mu0)
                        e0 = max([i for i in ev0 if i < r1], default=E)
                        if no_odd_in_c_f1:
                            base = [] if e0 == E else [(1, e0), (0, e0)]
                            ph_mu_list = []
                            if c_init == 1:
                                if e0 == E and f1 == 2 and r1 == E + 1 and q0 == mu0 - 1:
                                    ph_mu_list.append([(2, 2), (0, mu0), (1, mu0)])
                                ph_mu_list.append(base + [(1, q0), (2, f1)] + ([(0, mu0)] if q0 == mu0 - 1 else [(0, mu0 - 1), (1, mu0), (0, mu0)]))
                            else:
                                ph_mu_list.append(base + ([(1, q0), (2, f1)] if r1 == e0 + 1 else [(0, r1 - 1), (1, q0), (2, f1)]) + ([(0, mu0)] if q0 == mu0 - 1 else [(0, mu0 - 1), (1, mu0), (0, mu0)]))
                        elif c_init == 1 and odL and odL[0] < f1:
                            ph_mu_list = [cf.reach_mu_phase1(s_p, E, odL[0], f1, e0, r1, q0, mu0, ev0)]
                        else:
                            ph_mu_list = []
                        for ph_mu in ph_mu_list:
                            t_m, _ = run_ph(s_p, ph_mu, t_st)
                            if t_m is not None:
                                if mu0 == b_last:
                                    if u0 < mu0:
                                        mid_cands.append(ph_mu + jump_all_zero_to_O1(mu0, O1, t_m[2]))
                                        if O1 >= mu0 + 3:
                                            mid_cands.append(ph_mu + [(1, O1 - 1), (0, O1 - 1), (1, O1), (0, O1)])
                                    else:
                                        if t_m[2] % 2 == 0 and s_p[t_m[2]] == 1:
                                            mid_cands.append(ph_mu + [(0, O1 - 1), (1, O1), (0, O1)])
                                        c_nx = next((i for i in range(t_m[2] + (1 if t_m[2]%2 else 2), e, 2) if s_p[i] == 1), None)
                                        if c_nx:
                                            mid_cands.append(ph_mu + [(1, u0), (2, c_nx), (0, O1 - 1), (1, O1), (0, O1)])
                                elif not [i for i in od0 if mu0 < i < b_last]:
                                    ph_bl = ph_mu + [(1, b_last), (0, b_last)]
                                    t_bl, _ = run_ph(s_p, ph_bl, t_st)
                                    if t_bl:
                                        if u0 < b_last:
                                            mid_cands.append(ph_bl + jump_all_zero_to_O1(b_last, O1, t_bl[2]))
                                        else:
                                            if t_bl[2] % 2 == 0 and s_p[t_bl[2]] == 1:
                                                mid_cands.append(ph_bl + [(0, O1 - 1), (1, O1), (0, O1)])
                                            c_nx = next((i for i in range(t_bl[2] + (1 if t_bl[2]%2 else 2), e, 2) if s_p[i] == 1), None)
                                            if c_nx:
                                                mid_cands.append(ph_bl + [(1, u0), (2, c_nx), (0, O1 - 1), (1, O1), (0, O1)])

            for m_ph in mid_cands:
                t_o1, w_o1 = run_ph(s_p, m_ph, t_st)
                if t_o1 and t_o1[0] == O1 and t_o1[1] == O1 and t_o1[2] <= E + 1:
                    w_fin = finish_from_O1_O1_c(s_p, t_o1, O1, E)
                    if w_fin:
                        full = sc0.word + w_st + w_o1 + w_fin
                        try:
                            lib.verify_word(s_p, full, directed=True)
                            return full
                        except AssertionError:
                            pass

        # C.3: P_vs_P Early B-Advance / Super-P1 + Golden Bridge when BOTH wings have inner odd peaks!
        if od2_L:
            P1 = od2_L[0]
            # GPT 6.2 sol Section 4 early B-advance: B -> O1 - 1, C -> P1, B -> N - 1, C -> N, A -> N!
            for b_pre in ([O1 - 1] + ([i for i in ev0] if ev0 else [])):
                w = exec_phases(s_p, E - 1, [(1, E), (1, b_pre), (2, P1), (1, N - 1), (2, N), (0, N)])
                if w: return w
            # Zero-even-gap bypass (ri = '10200021...'): use C = P1(2) to walk B across O1..Or to N - 2, then Golden Bridge!
            if evL and not [i for i in odL if f1 < i < P1]:
                if od0:
                    u0 = od0[-1]
                    for b_tgt in ([N - 2] + ([lam] if lam < N - 2 else [])):
                        ph_gb = [(1, E), (1, u0), (2, P1 - 1 if P1 - 1 > f1 else f1), (1, b_tgt), (0, O1)] + ([(2, N), (0, N)] if b_tgt == N - 2 else [(1, N - 2), (2, N), (0, N)])
                        w = exec_phases(s_p, E - 1, ph_gb)
                        if w: return w
            # Multi-peak B-advance across O1 when b_last == O1 - 1 and e < E (syncs at (O3, O3, O3, 7)!):
            if e < E and ev0 and ev0[-1] == O1 - 1 and len(od2_R) >= 3 and od0:
                O2_r, O3_r = od2_R[1], od2_R[2]
                if s_p[O2_r + 1] == 1 and O3_r == O2_r + 2:
                    e_pen = evp[-2]
                    r1_0 = od0[0]; u0_0 = od0[-1]
                    mu0_0 = next((i for i in ev0 if i > r1_0), None)
                    if mu0_0 is not None and f1 < P1:
                        q0_0 = max(i for i in od0 if i < mu0_0)
                        e0_0 = max([i for i in ev0 if i < r1_0], default=E)
                        sc_mp = lib.Sched(s_p, E - 1, directed=True)
                        ph_pre_r1 = [(1, E)] + ([] if e0_0 == E else [(1, e0_0), (0, e0_0)]) + ([(1, q0_0)] if r1_0 == e0_0 + 1 else [(1, e0_0 + 1), (2, f1), (0, r1_0), (1, q0_0)])
                        for ph_mp_try in [
                            ph_pre_r1 + [(2, P1 - 2 if P1 - 2 >= f1 else f1)] + ([(0, mu0_0)] if q0_0 == mu0_0 - 1 else [(0, mu0_0 - 1), (1, mu0_0), (0, mu0_0)]) + [(1, mu0_0 + 1), (0, O1 - 2), (1, O1 - 1), (1, O2_r - 1), (0, O1), (2, e_pen - 1), (0, O2_r + 1), (2, O3_r)],
                            [(1, E)] + ([] if e0_0 == E else [(1, e0_0), (0, e0_0)]) + [(1, q0_0), (2, f1)] + ([(0, mu0_0)] if q0_0 == mu0_0 - 1 else [(0, mu0_0 - 1), (1, mu0_0), (0, mu0_0)]) + [(1, u0_0), (2, P1 - 1), (0, O1 - 1), (1, O2_r - 1), (0, O1), (2, e_pen - 1), (0, O2_r + 1), (2, O3_r)],
                        ]:
                            tm0, wm0 = run_ph(s_p, ph_mp_try, sc_mp.t)
                            if tm0 == (O3_r, O3_r, O3_r, 7):
                                O_st_r = min(i for i in range(lam + 1, N, 2) if s_p[i] == 2)
                                if len(od2_R) == 3 or od2_R[3] > lam:
                                    w_lft = lift_binary_from_Ok(s_p, tm0, O_st_r if O3_r < lam else O3_r)
                                    if w_lft:
                                        full_mp = sc_mp.word + wm0 + w_lft
                                        lib.verify_word(s_p, full_mp, directed=True)
                                        return full_mp
            # Symmetric / P_vs_P bridge when not ev0, s_p[E + 1] == 1, s_p[e - 1] == 1, and len(od2_R) >= 2:
            if not ev0 and s_p[E + 1] == 1 and s_p[e - 1] == 1 and len(od2_R) >= 2:
                O2_s = od2_R[1]
                ev_af_s = [i for i in range(O2_s + 1, N - 1, 2) if s_p[i] == 1]
                if ev_af_s and lib.M_ev(s_p, O1, O2_s) == 0:
                    fR_s = ev_af_s[0]; lam_s = ev_af_s[-1]
                    O_st_s = min(i for i in range(lam_s + 1, N, 2) if s_p[i] == 2)
                    sc_sy = lib.Sched(s_p, E - 1, directed=True)
                    for tail_sy in ([[(0, fR_s)]] if fR_s == O2_s + 1 else [[(0, fR_s - 1), (1, fR_s)], [(2, O2_s - 1), (0, fR_s - 1), (1, fR_s)]]):
                        tsy, wsy = run_ph(s_p, [(1, E), (1, O1 - 1), (2, e - 1), (1, O2_s - 2), (0, O2_s), (2, O1)] + tail_sy, sc_sy.t)
                        if tsy and tsy[:2] == (fR_s, fR_s) and (tsy[3] & 3) == 3:
                            w_fsy = finish_from_even_Ok(s_p, tsy, O_st_s, lam_s)
                            if w_fsy:
                                full_sy = sc_sy.word + wsy + w_fsy
                                lib.verify_word(s_p, full_sy, directed=True)
                                return full_sy
    return None

def solve_lemma_B_dir(s):
    N = len(s) - 1
    evp = [i for i in range(2, N - 1, 2) if s[i] == 2]
    e, E = evp[0], evp[-1]
    if not any(s[i] == 2 for i in range(3, e, 2)) and not any(s[i] == 2 for i in range(E + 1, N - 1, 2)):
        return None
    if lib.M_ev(s, 1, e) == 0 and lib.M_ev(s, E, N - 1) == 0:
        return solve_B0_dir(s)

    w = solve_common_witness_dir(s)
    if w: return w
    w = solve_sec5_dir(s)
    if w: return w
    w = solve_on_sp_dir(s)
    if w: return w

    # Theorem B1+ (General Left Odd-Peak Pivot Isomorphism (E, E, P_piv, 7) ~= (E_in, E_in, 1, 7) on s_in!):
    evL = [i for i in range(2, e, 2) if s[i] == 1]
    f1 = evL[0] if evL else e
    P0 = max(i for i in range(1, f1, 2) if s[i] == 2)
    od2_all_L = [i for i in range(1, e, 2) if s[i] == 2]
    P_last = od2_all_L[-1]
    P1_in = next((i for i in od2_all_L if i > P0), None)

    # ==========================================================================
    # Universal Two-Stage Left-Wing & Multi-Peak Middle Pivot Reduction
    # ==========================================================================
    # Stage 1: Exact closed-form prefixes reaching (e, e, c_e, m_e) with (m_e & 3) == 3
    ee_map = {}  # (c_e, m_e) -> word
    def add_ee_ph(a0, ph):
        if a0 < 1: return
        sc = lib.Sched(s, a0, directed=True)
        te, we = run_ph(s, ph, sc.t)
        if te and te[0] == e and te[1] == e and 1 <= te[2] < e and (te[3] & 3) == 3:
            key = (te[2], te[3])
            if key not in ee_map:
                ee_map[key] = sc.word + we

    # 1a. Outer pivot P0 (unconditional on [1..e]):
    add_ee_ph(e - 1, ([(2, P0 - 1)] if P0 > 1 else []) + [(1, e)])

    # 1b. Universal u_max / m_L dichotomy across ALL odd peaks P_k and inner odd 1s in (1, e):
    m_L = max([P_last] + [i for i in range(P_last + 1, e) if s[i] >= 1])
    u_max = max(i for i in range(P_last, e, 2) if s[i] >= 1)
    od_pivs_L = list(od2_all_L) + [q for q in range(P_last + 2, u_max + 1, 2) if s[q] == 1]
    for Pk in od_pivs_L:
        c_ph = [(2, Pk - 1)] if Pk > 1 else []
        if s[e - 1] >= 1:
            add_ee_ph(e - 1, c_ph + [(1, e)])
        if m_L % 2 == 1 or s[2] == 1:
            a_tgt = e if s[2] == 1 else e - 1
            add_ee_ph(u_max, c_ph + ([(0, a_tgt)] if u_max < a_tgt else []) + [(1, e)])
        # Even-1 anchors v > Pk in (1, e):
        ev_after_u = [i for i in range(u_max + 1, e, 2) if s[i] == 1]
        if ev_after_u:
            v0 = ev_after_u[0]; hL = ev_after_u[-1]
            pre_v0 = c_ph + ([(1, v0)] if v0 == u_max + 1 else [(0, v0 - 1), (1, v0)])
            add_ee_ph(u_max, pre_v0 + [(0, e - 1), (1, e)])
            if hL > v0:
                add_ee_ph(u_max, pre_v0 + [(0, hL), (1, e - 1), (0, e)])
            if Pk in od2_all_L:
                for Pb in od2_all_L:
                    if Pb <= Pk: continue
                    if v0 == u_max + 1 and Pk > 1:
                        add_ee_ph(u_max, [(1, Pk - 1), (2, Pb - 1), (1, v0), (0, e - 1), (1, e)])
                        if Pb - 3 >= 2:
                            add_ee_ph(u_max, [(1, Pk - 1), (2, Pb - 3), (1, v0), (0, e - 1), (1, e)])
                            add_ee_ph(u_max, c_ph + [(1, v0), (0, hL), (2, Pb - 1), (0, e - 1), (1, e)])

    # 1c. General (v, v, Pa, 7) for last even 1 h_all < e when s[h_all - 1] >= 1 (including odd 1s and t_L > h_all!):
    if evL:
        h_all = evL[-1]
        for v_cand in ([h_all] + (evL[-2:-1] if len(evL) >= 2 else [])):
            if s[v_cand - 1] >= 1:
                od_cands_v = [1] + [p for p in range(3, v_cand, 2) if s[p] >= 1]
                for Pa in od_cands_v:
                    pre_v = ([(2, Pa - 1)] if Pa > 1 else []) + [(1, v_cand)]
                    add_ee_ph(v_cand - 1, pre_v + [(0, e - 1), (1, e)])
                    od_after_v = [i for i in range(v_cand + 1, e, 2) if s[i] == 1]
                    if od_after_v and v_cand == h_all:
                        tL = od_after_v[-1]
                        add_ee_ph(v_cand - 1, pre_v + [(1, e - 1), (0, e)])
                        add_ee_ph(v_cand - 1, pre_v + [(0, od_after_v[0]), (1, tL), (2, tL), (1, e - 1), (0, e)])
        # Also unconditional I(h_all - 1), [(1, h_all)] -> (h_all, h_all, 1, 7):
        add_ee_ph(h_all - 1, [(1, h_all), (0, e - 1), (1, e)])
        if s[e - 1] == 1:
            add_ee_ph(h_all - 1, [(1, h_all), (1, e - 1), (0, e)])

    # 1d. Post-P_last binary suffix sync on (P_last, e) (works for BOTH P_last == 1 and P_last >= 3!):
    sync_starts_1d = []
    if len(od2_all_L) == 1 and e >= 6:
        sc_Lb0 = lib.Sched(s, 1, directed=True)
        sync_starts_1d.append((sc_Lb0.t, sc_Lb0.word))
    elif P_last >= 3:
        ev_af_Pl = [i for i in evL if i > P_last]
        if ev_af_Pl:
            v_af = ev_af_Pl[0]
            od_af_v = [i for i in range(v_af + 1, e, 2) if s[i] == 1]
            if od_af_v:
                r_af = max(i for i in range(P_last, v_af, 2) if s[i] >= 1)
                u1_af = od_af_v[0]
                w0_af = max(i for i in range(v_af, u1_af, 2) if s[i] == 1)
                sc_pl = lib.Sched(s, r_af, directed=True)
                pre_v_af = [(2, P_last - 1)] + ([(1, v_af)] if v_af == r_af + 1 else ([(0, v_af), (1, v_af)] if s[2] == 1 else [(0, v_af - 1), (1, v_af)]))
                tv_af, wv_af = run_ph(s, pre_v_af, sc_pl.t)
                if tv_af == (v_af, v_af, P_last, 7):
                    if u1_af == v_af + 1:
                        ph_u1 = [(0, u1_af), (1, u1_af)] if v_af == P_last + 1 else [(1, u1_af), (2, v_af), (0, u1_af), (2, u1_af)]
                    elif w0_af == v_af:
                        ph_u1 = [(1, u1_af - 2), (0, u1_af), (2, v_af), (1, u1_af), (2, u1_af)]
                    elif u1_af == w0_af + 1:
                        ph_u1 = [(1, w0_af), (0, u1_af), (2, v_af), (1, u1_af), (2, u1_af)]
                    else:
                        ph_u1 = [(1, w0_af), (0, u1_af - 2), (1, u1_af - 1), (0, u1_af), (2, v_af), (1, u1_af), (2, u1_af)]
                    tu1_af, wu1_af = run_ph(s, ph_u1, tv_af)
                    if tu1_af == (u1_af, u1_af, u1_af, 7):
                        sync_starts_1d.append((tu1_af, sc_pl.word + wv_af + wu1_af))

    for t_sync0, w_sync0 in sync_starts_1d:
        s_Lbin = tuple(s[:e - 1]) + (2, 2)
        t_cur = t_sync0; w_acc = w_sync0
        while t_cur[0] < e - 1:
            p_sync = t_cur[0]
            if p_sync > 1:
                step_e_list = [
                    [(1, e - 1), (0, e)],
                    [(0, e - 1), (1, e)],
                    [(0, e - 1), (1, e - 1), (0, e)] if p_sync == e - 2 else [(0, e - 2), (1, e - 1), (0, e - 1), (2, e - 1), (0, e)],
                ] + ([[(0, evL[-1]), (1, e - 1), (0, e)]] if evL and evL[-1] > p_sync else [])
                for step_e in step_e_list:
                    te, we = run_ph(s, step_e, t_cur)
                    if te and te[:2] == (e, e) and 1 <= te[2] < e and (te[3] & 3) == 3:
                        key = (te[2], te[3])
                        if key not in ee_map:
                            ee_map[key] = w_acc + we
            if s[p_sync + 1] == 1:
                step2 = 'yx' if p_sync % 2 == 1 else 'yz'
                ok2 = True
                for ch2 in step2:
                    t_cur = lib.step(s, t_cur, ch2, directed=True)
                    if t_cur is None: ok2 = False; break
                    w_acc += ch2
                if not ok2: break
                continue
            w_Lb = complete_binary_suffix(s_Lbin, p_sync)
            moved = False
            for ch in w_Lb:
                t_nx = lib.step(s, t_cur, ch, directed=True)
                if t_nx is None or max(t_nx[:3]) >= e: break
                t_cur = t_nx; w_acc += ch
                if t_cur[0] == t_cur[1] == t_cur[2] and t_cur[3] == 7 and p_sync < t_cur[0] < e - 1:
                    moved = True; break
            if not moved: break
        if t_cur and t_cur[0] == t_cur[1] == t_cur[2] and t_cur[3] == 7 and 1 < t_cur[0] <= e - 1:
            p_sync = t_cur[0]
            for step_e in ([[(0, e)]] if p_sync == e - 1 else [
                [(1, e - 1), (0, e)],
                [(0, e - 1), (1, e)],
                [(0, e - 1), (1, e - 1), (0, e)] if p_sync == e - 2 else [(0, e - 2), (1, e - 1), (0, e - 1), (2, e - 1), (0, e)],
            ]):
                te, we = run_ph(s, step_e, t_cur)
                if te and te[:2] == (e, e) and 1 <= te[2] < e and (te[3] & 3) == 3:
                    key = (te[2], te[3])
                    if key not in ee_map:
                        ee_map[key] = w_acc + we

    if evL and lib.M_od(s, 1, e) == 0:
        add_ee_ph(e - 1, ([(2, f1 - 1)] if f1 > 2 else []) + [(1, e)])

    # 1e. Synchronous Left-Prefix Walk from I(a0_st) to (a_cur < e, Pk, Pk, 7) -> (e, e, c_e, m_e):
    if len(od2_all_L) > 1:
        cand_a0s = sorted(set([P_last] + [i for i in range(P_last + 1, e) if s[i] >= 1]))
        for a0_st in cand_a0s:
            for Pk in od2_all_L[1:]:
                sc_s = lib.Sched(s, a0_st, directed=True)
                t_sw = sc_s.t; w_sw = []
                while t_sw is not None and t_sw[1] < Pk and t_sw[0] < e:
                    if t_sw[1] == t_sw[2] and t_sw[1] % 2 == 1:
                        ux = lib.step(s, t_sw, 'x', directed=True)
                        if ux is None: break
                        w_sw.append('x'); t_sw = ux
                        uy = lib.step(s, t_sw, 'y', directed=True)
                        if uy is None: break
                        w_sw.append('y'); t_sw = uy
                    elif t_sw[1] == t_sw[2] and t_sw[1] % 2 == 0:
                        if t_sw[1] + 2 < Pk and s[t_sw[1] + 2] == 1 and s[t_sw[2]] == 1:
                            while t_sw[0] < e - 2:
                                a_fin = t_sw[0] + 2 if t_sw[0] % 2 == 1 else t_sw[0] + 1
                                if a_fin < e and s[a_fin] >= 1: break
                                ch_a = 'x' if t_sw[0] % 2 == 1 else 'y'
                                ua = lib.step(s, t_sw, ch_a, directed=True)
                                if ua is None: break
                                w_sw.append(ch_a); t_sw = ua
                        elif t_sw[1] + 2 < Pk and s[t_sw[1] + 2] == 0 and s[t_sw[2]] == 1:
                            while t_sw[0] < e - 2 and t_sw[0] % 2 == 1 and s[t_sw[0] + 1] == 1:
                                for ch_a in ('x', 'y'):
                                    ua = lib.step(s, t_sw, ch_a, directed=True)
                                    if ua is None: break
                                    w_sw.append(ch_a); t_sw = ua
                        uz = lib.step(s, t_sw, 'z', directed=True)
                        if uz is None: break
                        w_sw.append('z'); t_sw = uz
                    else:
                        break
                if t_sw and t_sw[1] == Pk and t_sw[2] == Pk and t_sw[0] < e:
                    for tail_ee in [[(1, e)], [(0, e - 1), (1, e)]]:
                        te, we = run_ph(s, tail_ee, t_sw)
                        if te and te[:2] == (e, e) and 1 <= te[2] < e and (te[3] & 3) == 3:
                            if (te[2], te[3]) not in ee_map:
                                ee_map[(te[2], te[3])] = sc_s.word + ''.join(w_sw) + we

    # Stage 2: Step (e_j, e_j, c, m) across internal even peaks e = evp[0] < ... < evp[-1] = E
    dp_maps = [dict(ee_map)] + [{} for _ in range(len(evp) - 1)]
    for idx_k in range(1, len(evp)):
        ek_p = evp[idx_k]
        u_ek = max(i for i in range(P_last, ek_p, 2) if s[i] >= 1)
        for Pk in od_pivs_L:
            c_ph_k = [(2, Pk - 1)] if Pk > 1 else []
            cands_ek = []
            if s[ek_p - 1] >= 1:
                cands_ek.append((ek_p - 1, c_ph_k + [(1, ek_p)]))
            if s[2] == 1 or (lib.M_ev(s, u_ek, ek_p) == 0 and lib.M_od(s, u_ek, ek_p) == 0):
                a_tgt_k = ek_p if s[2] == 1 else ek_p - 1
                cands_ek.append((u_ek, c_ph_k + ([(0, a_tgt_k)] if u_ek < a_tgt_k else []) + [(1, ek_p)]))
            for a0_k, ph_k in cands_ek:
                sc_k = lib.Sched(s, a0_k, directed=True)
                tk, wk = run_ph(s, ph_k, sc_k.t)
                if tk and tk[:2] == (ek_p, ek_p) and 1 <= tk[2] < ek_p and (tk[3] & 3) == 3:
                    key_k = (tk[2], tk[3])
                    if key_k not in dp_maps[idx_k]:
                        dp_maps[idx_k][key_k] = sc_k.word + wk
        ek_prev = evp[idx_k - 1]
        if s[ek_prev + 1] == 1:
            for Pb in od2_all_L[1:]:
                for pre_b in [[], [(1, 2)]] + [[(1, Pa)] for Pa in od2_all_L if 1 < Pa < Pb]:
                    tails_ekp = [[(1, ek_p)]] if ek_p == ek_prev + 2 else [[(0, ek_p - 1), (1, ek_p)], [(0, ek_p), (1, ek_p)], [(1, ek_p)]]
                    for tl_ekp in tails_ekp:
                        sc_ekp = lib.Sched(s, ek_prev, directed=True)
                        tekp, wekp = run_ph(s, pre_b + [(2, Pb - 1)] + tl_ekp, sc_ekp.t)
                        if tekp and tekp[:2] == (ek_p, ek_p) and 1 <= tekp[2] < ek_p and (tekp[3] & 3) == 3:
                            k_ekp = (tekp[2], tekp[3])
                            if k_ekp not in dp_maps[idx_k]:
                                dp_maps[idx_k][k_ekp] = sc_ekp.word + wekp
    for idx_ev in range(len(evp) - 1):
        ej, enx = evp[idx_ev], evp[idx_ev + 1]
        # Internal Odd-Peak Teleport Starts I(qm) for all qm in (ej, enx):
        for qm in [i for i in range(ej + 1, enx, 2) if s[i] == 2]:
            sc_q = lib.Sched(s, qm, directed=True)
            for idx_pa, Pa in enumerate(od2_all_L):
                pre_c = [(2, Pa - 1)] if Pa > 1 else []
                tq_pa, wq_pa = run_ph(s, pre_c, sc_q.t)
                if not tq_pa: continue
                for tgt_ev, tgt_map in ([(enx, dp_maps[idx_ev + 1]), (E, dp_maps[-1])] if enx < E else [(E, dp_maps[-1])]):
                    for r_basic in [[(1, tgt_ev)], [(0, tgt_ev - 1), (1, tgt_ev)], [(0, tgt_ev), (1, tgt_ev)]]:
                        tn, wn = run_ph(s, r_basic, tq_pa)
                        if tn and tn[:2] == (tgt_ev, tgt_ev) and 1 <= tn[2] < tgt_ev and (tn[3] & 3) == 3:
                            if (tn[2], tn[3]) not in tgt_map:
                                tgt_map[(tn[2], tn[3])] = sc_q.word + wq_pa + wn
                for b_m in [i for i in evL if i > Pa]:
                    for Pb in od2_all_L[idx_pa + 1:]:
                        rel_qm_list = [
                            [(1, b_m), (2, Pb), (1, E)],
                            [(1, b_m), (2, Pb - 1), (0, E - 1), (1, E)],
                        ]
                        if Pb - 2 > Pa:
                            rel_qm_list.extend([
                                [(1, b_m), (2, Pb - 2), (1, e), (2, Pb), (1, E)],
                                [(1, b_m), (2, Pb - 2), (1, ej), (2, Pb), (1, E)],
                                [(1, b_m), (2, Pb - 2), (0, E - 1), (1, E)],
                                [(1, b_m), (2, Pb - 2), (0, E), (1, E)],
                            ])
                        for r_qm in rel_qm_list:
                            tn, wn = run_ph(s, r_qm, tq_pa)
                            if tn and tn[:2] == (E, E) and 1 <= tn[2] < E and (tn[3] & 3) == 3:
                                if (tn[2], tn[3]) not in dp_maps[-1]:
                                    dp_maps[-1][(tn[2], tn[3])] = sc_q.word + wq_pa + wn

        ev_mid = [i for i in range(ej + 2, enx, 2) if s[i] == 1]
        for (c_cur, m_cur), w_pref in list(dp_maps[idx_ev].items()):
            t_ej = (ej, ej, c_cur, m_cur)
            # Theorem M-Teleport: Direct two-phase jump from ej to E across arbitrary multi-peak [ej, E]:
            if enx < E:
                for ph_m in [[(1, E), (0, E)], [(0, E - 1), (1, E)], [(0, E), (1, E)], [(1, E - 1), (0, E)]]:
                    tM, wM = run_ph(s, ph_m, t_ej)
                    if tM and tM[:2] == (E, E) and 1 <= tM[2] < E and (tM[3] & 3) == 3:
                        if (tM[2], tM[3]) not in dp_maps[-1]:
                            dp_maps[-1][(tM[2], tM[3])] = w_pref + wM
            step_cands = [
                [(0, enx - 1), (1, enx)],
                [(0, enx), (1, enx)],
                [(1, ej + 1), (0, enx)],
                [(1, enx), (0, enx)],
            ]
            if enx >= ej + 4:
                step_cands.append([(1, ej + 1), (0, ej + 2), (1, enx - 1), (0, enx)])
                step_cands.append([(1, ej + 2), (0, enx - 1), (1, enx)])
            if ev_mid:
                hm = ev_mid[-1]
                step_cands.append([(1, hm - 1), (0, hm), (0, enx - 1), (1, enx - 1), (0, enx)])
                step_cands.append([(1, hm - 1), (0, hm), (0, enx - 1), (1, enx)])
                if hm + 2 < enx:
                    step_cands.append([(1, hm - 1), (0, hm), (0, hm + 1), (1, hm + 1), (0, enx - 1), (1, enx)])
            if enx >= ej + 4 and c_cur % 2 == 0 and c_cur + 1 < enx and s[c_cur + 1] >= 1:
                step_cands.append([(0, ej + 1), (1, ej + 1), (0, ej + 2), (0, enx - 1), (1, enx)])
            if s[ej + 1] == 1:
                od_c = [i for i in range(c_cur + (2 if c_cur % 2 == 1 else 1), e, 2) if s[i] >= 1]
                for c_tgt in od_c:
                    if enx == ej + 2:
                        step_cands.append([(1, ej + 1), (2, c_tgt), (0, enx)])
                    else:
                        step_cands.append([(1, ej + 1), (2, c_tgt), (0, ej + 2), (1, enx)])
                        if c_tgt - 2 >= c_cur:
                            step_cands.append([(1, ej + 1), (2, c_tgt - 2), (0, enx - 1), (1, enx)])
            if s[ej + 1] == 0 and c_cur % 2 == 1 and s[c_cur] == 2:
                ev_nx_c = next((i for i in range(c_cur + 1, e, 2) if s[i] == 1), e)
                od_c0 = [i for i in range(c_cur + 2, ev_nx_c, 2) if s[i] >= 1]
                for k1_p in ([od_c0[0], od_c0[-1]] if len(od_c0) > 1 else od_c0):
                    step_cands.append([(0, ej + 1)] + ([(2, k1_p - 1)] if k1_p - 1 > c_cur + 1 else []) + ([(0, enx - 1)] if ej + 1 < enx - 1 else []) + [(1, enx)])
            for st_ph in step_cands:
                tn, wn = run_ph(s, st_ph, t_ej)
                if tn and tn[0] == enx and tn[1] == enx and 1 <= tn[2] < enx and (tn[3] & 3) == 3:
                    k_nx = (tn[2], tn[3])
                    if k_nx not in dp_maps[idx_ev + 1]:
                        dp_maps[idx_ev + 1][k_nx] = w_pref + wn
            # Internal odd-peak synchronization inside (ej, enx): (ej, ej, c_cur, 7) -> (q_m, q_m, q_m, 7) -> enx!
            q_mids = [i for i in range(ej + 1, enx, 2) if s[i] == 2]
            if q_mids and m_cur == 7:
                def _sync_to_q(t_in_q, w_in_q, ej_lim, q_tgt):
                    tc_q = t_in_q; w_q = w_in_q
                    if tc_q[0] % 2 == 1:
                        t2_q, w2_q = run_ph(s, [(2, tc_q[0] + 1), (0, tc_q[0] + 1)], tc_q)
                        if t2_q != (tc_q[0] + 1, tc_q[0] + 1, tc_q[0] + 1, 7): return None, None
                        tc_q = t2_q; w_q += w2_q
                    p_ev_q = tc_q[0]
                    # Method A: synchronous parity walk with C-witness recovery before ej_lim
                    t_a = tc_q; w_a = []; ok_a = True
                    for pos_q in range(p_ev_q + 1, q_tgt + 1):
                        if pos_q % 2 == 1:
                            for ch_q in ('y', 'z'):
                                t_a = lib.step(s, t_a, ch_q, directed=True)
                                if t_a is None: ok_a = False; break
                                w_a.append(ch_q)
                            if not ok_a: break
                            if pos_q < q_tgt:
                                if not (t_a[3] & 1):
                                    ev_c = next((i for i in range(t_a[2] + (1 if t_a[2] % 2 == 1 else 2), ej_lim, 2) if s[i] >= 1), None)
                                    if ev_c is None: ok_a = False; break
                                    t_a, wc1 = run_ph(s, [(2, ev_c)], t_a)
                                    if t_a is None or not (t_a[3] & 1): ok_a = False; break
                                    w_a.append(wc1)
                                if not (t_a[3] & 2):
                                    od_c = next((i for i in range(t_a[2] + (2 if t_a[2] % 2 == 1 else 1), ej_lim, 2) if s[i] >= 1), None)
                                    if od_c is None: ok_a = False; break
                                    t_a, wc2 = run_ph(s, [(2, od_c)], t_a)
                                    if t_a is None or not (t_a[3] & 2): ok_a = False; break
                                    w_a.append(wc2)
                            else:
                                t_a, wc_end = run_ph(s, [(2, q_tgt)], t_a)
                                if t_a == (q_tgt, q_tgt, q_tgt, 7):
                                    return t_a, w_q + ''.join(w_a) + wc_end
                                ok_a = False
                        else:
                            t_a = lib.step(s, t_a, 'x', directed=True)
                            if t_a is None: ok_a = False; break
                            w_a.append('x')
                    # Method B: zero-odd phase escort when M_od(p_ev_q, q_tgt) == 0
                    if lib.M_od(s, p_ev_q, q_tgt) == 0:
                        h_q = max([p_ev_q] + [i for i in range(p_ev_q + 2, q_tgt, 2) if s[i] == 1])
                        ph_b_q = ([(1, h_q)] if h_q > p_ev_q else []) + ([(0, q_tgt - 1), (1, q_tgt - 1)] if q_tgt - 1 > p_ev_q else []) + [(0, q_tgt), (2, q_tgt)]
                        tb_q, wb_q = run_ph(s, ph_b_q, tc_q)
                        if tb_q == (q_tgt, q_tgt, q_tgt, 7):
                            return tb_q, w_q + wb_q
                    return None, None

                q_reached = []
                tq_cur, wq_cur = _sync_to_q(t_ej, w_pref, ej, q_mids[0])
                if tq_cur is not None:
                    q_reached.append((tq_cur, wq_cur))
                    for idx_qm in range(1, len(q_mids)):
                        tq_nx, wq_nx = _sync_to_q(q_reached[-1][0], q_reached[-1][1], q_mids[idx_qm - 1], q_mids[idx_qm])
                        if tq_nx is None: break
                        q_reached.append((tq_nx, wq_nx))
                for t_qm, w_qm in q_reached:
                    qm = t_qm[0]
                    s_qm = (2, 2) + tuple(s[qm + 1:])
                    w_qm_sol = solve_on_sp_dir(s_qm, c1_wt=2) or cf.try_closed_form_dir(s_qm)
                    if w_qm_sol and w_qm_sol.startswith('xyz'):
                        t_chk_q = t_qm; ok_q = True
                        for ch_q in w_qm_sol[3:]:
                            t_chk_q = lib.step(s, t_chk_q, ch_q, directed=True)
                            if t_chk_q is None: ok_q = False; break
                        if ok_q and t_chk_q == (N, N, N, 7):
                            full_q = w_qm + w_qm_sol[3:]
                            lib.verify_word(s, full_q, directed=True)
                            return full_q
                    # Also propagate (qm, qm, qm, 7) across binary (qm, enx] into dp_maps[idx_ev + 1]:
                    if qm == q_mids[-1]:
                        s_q_enx = tuple(s[:enx - 1]) + (2, 2)
                        t_qs = t_qm; w_qs = w_qm
                        while t_qs is not None and t_qs[0] < enx:
                            pq = t_qs[0]
                            q_enx_steps = ([[(0, enx)]] if pq == enx - 1 else [
                                [(0, enx - 1), (1, enx)],
                                [(0, enx), (1, enx)],
                                [(1, enx - 1), (0, enx)],
                                [(1, enx), (0, enx)],
                                [(0, enx - 1), (1, enx - 1), (0, enx)] if pq == enx - 2 else [(0, enx - 2), (1, enx - 1), (0, enx - 1), (2, enx - 1), (0, enx)],
                            ])
                            for st_qe in q_enx_steps:
                                t_qe, w_qe = run_ph(s, st_qe, t_qs)
                                if t_qe and t_qe[:2] == (enx, enx) and 1 <= t_qe[2] < enx and (t_qe[3] & 3) == 3:
                                    k_qe = (t_qe[2], t_qe[3])
                                    if k_qe not in dp_maps[idx_ev + 1]:
                                        dp_maps[idx_ev + 1][k_qe] = w_qs + w_qe
                            if pq >= enx - 1: break
                            if s[pq + 1] == 1:
                                st2_q = 'yx' if pq % 2 == 1 else 'yz'
                                ok2_q = True
                                for ch2_q in st2_q:
                                    t_qs = lib.step(s, t_qs, ch2_q, directed=True)
                                    if t_qs is None: ok2_q = False; break
                                    w_qs += ch2_q
                                if not ok2_q: break
                                continue
                            w_qb = complete_binary_suffix(s_q_enx, pq)
                            mv_q = False
                            for ch_qb in w_qb:
                                t_nx_q = lib.step(s, t_qs, ch_qb, directed=True)
                                if t_nx_q is None or max(t_nx_q[:3]) >= enx: break
                                t_qs = t_nx_q; w_qs += ch_qb
                                if t_qs[0] == t_qs[1] == t_qs[2] and t_qs[3] == 7 and pq < t_qs[0] <= enx - 1:
                                    mv_q = True; break
                            if not mv_q: break

            # Two-even-peak leapfrog ej -> evp[idx_ev + 2]:
            if idx_ev + 2 < len(evp):
                enx2 = evp[idx_ev + 2]
                for st2 in [[(0, enx2 - 1), (1, enx2)], [(0, enx2), (1, enx2)], [(1, enx2 - 1), (0, enx2)]]:
                    tn2, wn2 = run_ph(s, st2, t_ej)
                    if tn2 and tn2[:2] == (enx2, enx2) and 1 <= tn2[2] < enx2 and (tn2[3] & 3) == 3:
                        k_nx2 = (tn2[2], tn2[3])
                        if k_nx2 not in dp_maps[idx_ev + 2]:
                            dp_maps[idx_ev + 2][k_nx2] = w_pref + wn2
    cur_map = dp_maps[-1]
    if e < E and (e - 1, 7) in ee_map:
        t_em1 = (e, e, e - 1, 7)
        t_Ee, w_Ee = run_ph(s, [(1, E - 1), (0, E)], t_em1)
        if t_Ee and t_Ee[:2] == (E, E) and t_Ee[2] == e and (t_Ee[3] & 3) == 3:
            if (e, t_Ee[3]) not in cur_map:
                cur_map[(e, t_Ee[3])] = ee_map[(e - 1, 7)] + w_Ee

    # Stage 2b: Direct middle starts (I(E - 1), I(a_max in [e, E)), Even-Peak Start I(e_k), and Middle Even-1 Start I(a_ev - 1))
    def add_EE_ph(a0, ph):
        if a0 < 1: return
        sc = lib.Sched(s, a0, directed=True)
        tE, wE = run_ph(s, ph, sc.t)
        if tE and tE[0] == E and tE[1] == E and 1 <= tE[2] < E and (tE[3] & 3) == 3:
            key = (tE[2], tE[3])
            if key not in cur_map:
                cur_map[key] = sc.word + wE

    if e < E:
        add_EE_ph(E - 1, ([(2, P0 - 1)] if P0 > 1 else []) + [(1, E)])
        for Pk in od2_all_L:
            if Pk > P0:
                if s[E - 1] >= 1:
                    add_EE_ph(E - 1, [(2, Pk - 1), (1, E)])
                a_mp = max([Pk] + [i for i in range(Pk + 1, E) if s[i] >= 1])
                if a_mp < E - 1 and a_mp % 2 == 1:
                    add_EE_ph(a_mp, [(2, Pk - 1), (0, E if s[2] == 1 else E - 1), (1, E)])
        # Even-Peak Start I(e_k) for e_k in evp[:-1] (both step-to-enx in dp_maps and direct-to-E in cur_map!):
        for idx_ek, ek in enumerate(evp[:-1]):
            enx_ek = evp[idx_ek + 1]
            if s[ek + 1] == 1:
                for Pb in od2_all_L[1:]:
                    for pre_b in [[], [(1, 2)]] + [[(1, Pa)] for Pa in od2_all_L if 1 < Pa < Pb]:
                        for tgt_ev, tgt_map in ([(enx_ek, dp_maps[idx_ek + 1]), (E, cur_map)] if enx_ek < E else [(E, cur_map)]):
                            tails_ek = [[(1, tgt_ev)]] if tgt_ev == ek + 2 else [[(0, tgt_ev - 1), (1, tgt_ev)], [(0, tgt_ev), (1, tgt_ev)], [(1, tgt_ev)]]
                            for tl_ek in tails_ek:
                                sc_ek = lib.Sched(s, ek, directed=True)
                                tek, wek = run_ph(s, pre_b + [(2, Pb - 1)] + tl_ek, sc_ek.t)
                                if tek and tek[:2] == (tgt_ev, tgt_ev) and 1 <= tek[2] < tgt_ev and (tek[3] & 3) == 3:
                                    k_ek = (tek[2], tek[3])
                                    if k_ek not in tgt_map:
                                        tgt_map[k_ek] = sc_ek.word + wek
                for idx_a in range(len(od2_all_L)):
                    Pa = od2_all_L[idx_a]
                    ev_after_Pa = [i for i in range(Pa + 1, e, 2) if s[i] == 1]
                    if not ev_after_Pa: continue
                    b_ev = ev_after_Pa[0]
                    pre_pa = [(1, Pa - 1)] if Pa > 1 else []
                    for Pb in od2_all_L[idx_a + 1:]:
                        for c_stop in ([Pb - 3, Pb - 1] if Pb - 3 >= 2 else [Pb - 1]):
                            add_EE_ph(ek, pre_pa + [(2, c_stop), (1, b_ev), (0, E - 1), (2, Pb), (1, E)])
                            add_EE_ph(ek, pre_pa + [(2, c_stop), (1, b_ev), (0, E), (1, E)])
                            if ek + 3 < E and s[ek + 2] == 1:
                                add_EE_ph(ek, pre_pa + [(2, c_stop), (1, b_ev), (0, ek + 3), (2, Pb), (1, E)])
            elif ek + 2 < E and any(s[i] == 1 for i in range(ek + 2, E, 2)):
                # s[ek + 1] == 0 and even 1s in (ek, E) (#6 FWD & u#2 REV!):
                ev_mid_k = [i for i in range(ek + 2, E, 2) if s[i] == 1]
                od_mid_k = [i for i in range(ek + 1, E, 2) if s[i] == 1]
                for Pk in od2_all_L[1:]:
                    if s[ek + 2] == 1 and evL and evL[0] < Pk:
                        b0 = evL[0]
                        od_b0_Pk = [i for i in range(b0 + 1, Pk, 2) if s[i] >= 1]
                        ph_k = [(1, 2), (0, ek + 1)] + ([(2, b0 - 2)] if b0 > 2 else []) + [(1, b0)]
                        if od_b0_Pk:
                            q_b0 = od_b0_Pk[0]
                            ph_k += [(0, ev_mid_k[-1]), (1, q_b0 - 1), (0, ev_mid_k[-1] + 1), (2, Pk - 1), (1, E)]
                        else:
                            ph_k += [(0, ev_mid_k[-1] + 1), (2, Pk - 1), (1, E)]
                        add_EE_ph(ek, ph_k)
                    if od_mid_k and s[Pk - 1] == 1:
                        u_mk = od_mid_k[0]
                        add_EE_ph(ek, [(1, Pk - 1), (0, u_mk), (2, Pk - 1), (0, E if s[Pk + 1] == 1 else E - 1), (1, E)])
                if od_mid_k and len(od2_all_L) >= 3 and [i for i in evL if i > P_last]:
                    u_mk = od_mid_k[0]; b_post = [i for i in evL if i > P_last][0]
                    P1_l = od2_all_L[1]
                    for Pb_l in od2_all_L[2:]:
                        if Pb_l > P1_l:
                            add_EE_ph(ek, [(1, P1_l - 1), (0, u_mk), (2, Pb_l - 1), (1, b_post), (0, E - 1), (1, E)])
        # Middle Even-1 Start I(a_ev - 1) and Internal Odd-Peak Start I(qm)/I(qm - 1) for (e, E):
        ev_post_Plast = [i for i in evL if i > P_last]
        for a_ev in [i for i in range(e + 2, E, 2) if s[i] == 1]:
            for Pk in od2_all_L:
                add_EE_ph(a_ev - 1, [(1, Pk + 1), (0, E - 1), (1, E)])
                add_EE_ph(a_ev - 1, ([(2, Pk - 1)] if Pk > 1 and s[a_ev - 1] >= 1 else []) + [(1, Pk + 1), (0, E - 1), (1, E)])
            if ev_post_Plast and s[a_ev - 1] >= 1:
                add_EE_ph(a_ev - 1, ([(2, P_last - 1)] if P_last > 1 else []) + [(1, ev_post_Plast[0]), (0, E - 1), (1, E)])
                for Pa in od2_all_L[:-1]:
                    b_pa_list = [i for i in evL if i > Pa]
                    if b_pa_list:
                        add_EE_ph(a_ev - 1, ([(2, Pa - 1)] if Pa > 1 else []) + [(1, b_pa_list[0]), (0, E - 1), (2, P_last - 1), (1, E)])
        for qm in [i for i in range(e + 1, E, 2) if s[i] == 2]:
            if qm + 1 < E and s[qm + 1] == 1:
                if evL:
                    add_EE_ph(qm, [(2, qm - 1), (1, evL[0]), (0, E - 1), (1, E)])
                    for b_ev_q in [b for b in evL if b >= 4]:
                        if qm - 3 >= 2:
                            add_EE_ph(qm - 1, [(1, 2), (2, qm - 3), (1, b_ev_q), (0, E - 1), (1, E)])
                add_EE_ph(qm - 1, [(1, 2), (0, qm), (2, qm - 1), (0, qm + 1), (2, qm), (0, E - 1), (1, E)])

    # Stage 3: Solve from each reachable (E, E, c_piv, m_piv)!
    # Sort pivots to try P0, P_last, odd peaks, odd 1s, then even pivots:
    def piv_priority(item):
        (c_p, m_p), _ = item
        if c_p == P0: return (0, -c_p)
        if c_p == P_last: return (1, -c_p)
        if c_p % 2 == 1 and s[c_p] == 2: return (2, -c_p)
        if c_p % 2 == 1 and s[c_p] == 1: return (3, -c_p)
        return (4, -c_p)

    od2_R_orig = [i for i in range(E + 1, N - 1, 2) if s[i] == 2]
    evR_orig = [i for i in range(E + 2, N - 1, 2) if s[i] == 1]
    odR_orig = [i for i in range(E + 1, N - 1, 2) if s[i] == 1]

    sorted_pivs = sorted(cur_map.items(), key=piv_priority)
    for (c_piv, m_piv), w_piv in sorted_pivs:
        t_piv = (E, E, c_piv, m_piv)
        # 3a. Odd pivot 1 < c_piv <= E - 3 -> Theorem B1+ Isomorphism!
        if c_piv % 2 == 1 and 1 < c_piv <= E - 3 and (s[c_piv] >= 1 or m_piv == 7):
            if True:
                s_in = (2, 2) + tuple(s[c_piv + 1:])
                w_in = solve_on_sp_dir(s_in, c1_wt=s[c_piv])
                if w_in:
                    E_in = E - (c_piv - 1)
                    sc_in_init = lib.Sched(s_in, E_in - 1, directed=True)
                    sc_in_init.go(1, E_in)
                    if w_in.startswith(sc_in_init.word):
                        suf = w_in[len(sc_in_init.word):]
                        t_s = t_piv; ok = True
                        for ch in suf:
                            t_s = lib.step(s, t_s, ch, directed=True)
                            if t_s is None: ok = False; break
                        if ok and t_s == (N, N, N, 7):
                            full = w_piv + suf
                            lib.verify_word(s, full, directed=True)
                            return full
                    elif (c_piv, 7) in ee_map:
                        e_in = e - (c_piv - 1)
                        sc_ein_init = lib.Sched(s_in, e_in - 1, directed=True)
                        sc_ein_init.go(1, e_in)
                        if w_in.startswith(sc_ein_init.word):
                            suf_e = w_in[len(sc_ein_init.word):]
                            t_s = (e, e, c_piv, 7); ok = True
                            for ch in suf_e:
                                t_s = lib.step(s, t_s, ch, directed=True)
                                if t_s is None: ok = False; break
                            if ok and t_s == (N, N, N, 7):
                                full = ee_map[(c_piv, 7)] + suf_e
                                lib.verify_word(s, full, directed=True)
                                return full
                    if c_piv == P0 and P0 > 1:
                        # Lift non-(E,E,1) start I(a0_in) on s_in to I(a0_s), [(2, P0 - 1)] on s!
                        z_idx = w_in.index('z')
                        a0_in = z_idx - 1
                        a0_s = a0_in + (P0 - 1)
                        if a0_in >= 2 and s[a0_s] >= 1 and a0_s % 2 == 1:
                            sc_s2 = lib.Sched(s, a0_s, directed=True)
                            t2, wp2 = run_ph(s, [(2, P0 - 1)], sc_s2.t)
                            if t2 is not None:
                                sc_in2 = lib.Sched(s_in, a0_in, directed=True)
                                suf2 = w_in[len(sc_in2.word):]
                                t_s = t2; ok = True
                                for ch in suf2:
                                    t_s = lib.step(s, t_s, ch, directed=True)
                                    if t_s is None: ok = False; break
                                if ok and t_s == (N, N, N, 7):
                                    full = sc_s2.word + wp2 + suf2
                                    lib.verify_word(s, full, directed=True)
                                    return full

        # 3b. Even pivot c_piv < e OR zero-weight odd pivot s[c_piv] == 0 (m_piv == 7):
        if (c_piv % 2 == 0 and c_piv < E) or (c_piv % 2 == 1 and c_piv < E and s[c_piv] == 0 and m_piv == 7):
            lam_o = evR_orig[-1] if evR_orig else E
            O_star_o = min(i for i in range(lam_o + 1, N, 2) if s[i] == 2)
            if c_piv % 2 == 0 and not [i for i in od2_R_orig if i < O_star_o]:
                odR_c = [i for i in odR_orig if i < O_star_o]
                evR_c = [i for i in evR_orig if i < O_star_o]
                tail_O = [(2, N), (0, N)] if O_star_o == N - 1 else [(1, N - 1), (2, N), (0, N)]
                ev_c_e = [i for i in range(c_piv + 2, e, 2) if s[i] == 1]
                f_nx = ev_c_e[0] if ev_c_e else (c_piv if s[c_piv] == 1 else None)
                cands_ev = []
                if not odR_c:
                    b_l = evR_c[-1] if evR_c else E
                    cands_ev.append(([(0, b_l)] if b_l > E else []) + [(1, O_star_o), (0, O_star_o), (2, O_star_o)] + tail_O)
                    cands_ev.append(([(0, b_l)] if b_l > E else []) + [(1, O_star_o - 1), (0, O_star_o), (1, O_star_o), (2, O_star_o)] + tail_O)
                elif s[c_piv + 1] >= 1 and f_nx is not None:
                    u0_c = odR_c[-1]; r1_c = odR_c[0]
                    ev_af_r1 = [i for i in evR_c if i > r1_c]
                    if not ev_af_r1:
                        b0_c = evR_c[-1] if evR_c else E
                        cands_ev.append(([(0, b0_c)] if b0_c > E else []) + [(1, u0_c), (2, f_nx), (0, O_star_o - 1), (1, O_star_o), (0, O_star_o), (2, O_star_o)] + tail_O)
                    elif lam_o == O_star_o - 1:
                        mu_c = ev_af_r1[0]; q_c = max(i for i in odR_c if i < mu_c); e0_c = max([i for i in evR_c if i < r1_c], default=E)
                        cands_ev.append(([(0, e0_c)] if e0_c > E else []) + [(1, q_c), (2, f_nx)] + ([(0, mu_c)] if q_c == mu_c - 1 else [(0, mu_c - 1), (1, mu_c), (0, mu_c)]) + [(1, O_star_o), (0, O_star_o)] + tail_O)
                    elif c_piv == e - 2 and s[e - 2] == 1 and s[e - 1] == 1 and ev_af_r1[-1] <= O_star_o - 3 and s[ev_af_r1[-1] - 1] == 1:
                        cands_ev.append([(0, ev_af_r1[-1] - 1), (1, O_star_o - 2), (0, O_star_o), (1, O_star_o)] + tail_O)
                for ph_ev in cands_ev:
                    te, we = run_ph(s, ph_ev, t_piv)
                    if te == (N, N, N, 7):
                        full = w_piv + we
                        lib.verify_word(s, full, directed=True)
                        return full
                # Post-even-pivot step (E, E, c_piv, m_piv) -> 'yzx' -> (E + 2, E + 2, c_piv + 1, 7) Lemma A reduction!
                if c_piv + 1 < e and E + 2 < O_star_o and s[c_piv + 1] == 1 and not [i for i in range(c_piv + 2, e, 2) if s[i] == 2]:
                    t_sub, w_sub0 = run_ph(s, [(0, E + 1), (1, E + 1), (0, E + 2)], t_piv)
                    if t_sub == (E + 2, E + 2, c_piv + 1, 7):
                        p_r, c_r = E + 2, c_piv + 1
                        s_sub = (2, 2) + tuple(s[c_r + 1:e]) + (2,) + tuple(s[p_r + 1:O_star_o + 1]) + (2,)
                        E_sub = 2 + (e - (c_r + 1))
                        w_sub_cf = cf.try_closed_form_dir(s_sub)
                        if w_sub_cf and w_sub_cf.endswith('yx'):
                            sc_sub = lib.Sched(s_sub, E_sub - 1, directed=True); sc_sub.go(1, E_sub)
                            if w_sub_cf.startswith(sc_sub.word):
                                tc_s = t_sub; pr_s = []; ok_s = True
                                for ch_s in w_sub_cf[len(sc_sub.word):-2]:
                                    if tc_s[:2] == (O_star_o, O_star_o): break
                                    tc_s = lib.step(s, tc_s, ch_s, directed=True)
                                    if tc_s is None: ok_s = False; break
                                    pr_s.append(ch_s)
                                if ok_s and tc_s[:2] == (O_star_o, O_star_o):
                                    te_s, we_s = run_ph(s, [(2, O_star_o)] + tail_O, tc_s)
                                    if te_s == (N, N, N, 7):
                                        full_s = w_piv + w_sub0 + ''.join(pr_s) + we_s
                                        lib.verify_word(s, full_s, directed=True)
                                        return full_s
            if od2_R_orig:
                O1_o = od2_R_orig[0]
                ev0_o = [i for i in evR_orig if i < O1_o]
                od0_o = [i for i in odR_orig if i < O1_o]
                b_l = ev0_o[-1] if ev0_o else E
                jmp_list = []
                if c_piv == e - 1:
                    if not od0_o:
                        jmp_list.append(([(1, b_l)] if b_l > E else []) + [(0, O1_o)])
                    elif b_l == E:
                        jmp_list.append([(0, O1_o)])
                elif c_piv % 2 == 1 and c_piv < e - 1 and s[c_piv + 1] == 1 and lib.M_od(s, c_piv + 1, e) == 0 and b_l == E and od0_o and len(od2_R_orig) >= 2 and od2_R_orig[1] == O1_o + 2 and s[O1_o + 1] == 0:
                    O2_o = od2_R_orig[1]
                    r1_o = od0_o[0]
                    ev_af_s2 = [i for i in evR_orig if i > O1_o]
                    if ev_af_s2:
                        v0_s2 = ev_af_s2[0]
                        Op2_o = max(i for i in od2_R_orig if i < v0_s2)
                        cands_s2 = [[(0, O1_o - 1), (1, E + 1), (0, O1_o + 1), (2, O1_o - 1), (1, v0_s2)]]
                        if r1_o >= E + 3 and e < E:
                            pre_s2 = [(0, O1_o - 1), (1, r1_o - 2), (2, e), (0, O1_o + 1), (1, r1_o), (2, O1_o - 1)]
                            cands_s2.append(pre_s2 + [(1, v0_s2)])
                            cands_s2.append(pre_s2 + [(1, O2_o)] + ([(2, Op2_o - 1)] if Op2_o - 1 > O1_o else []) + ([(0, v0_s2 - 1)] if v0_s2 - 1 > O2_o + 1 else []) + [(1, v0_s2)])
                            cands_s2.append(pre_s2 + [(1, O2_o), (2, Op2_o)] + ([(0, v0_s2 - 1)] if v0_s2 - 1 > O2_o + 1 else []) + [(1, v0_s2)])
                        for ph_s2 in cands_s2:
                            tv_s2, wv_s2 = run_ph(s, ph_s2, t_piv)
                            if tv_s2 and tv_s2[:2] == (v0_s2, v0_s2) and (tv_s2[3] & 3) == 3:
                                we_s2 = finish_from_even_Ok(s, tv_s2, O_star_o, lam_o)
                                if we_s2:
                                    full_s2 = w_piv + wv_s2 + we_s2
                                    lib.verify_word(s, full_s2, directed=True)
                                    return full_s2
                elif c_piv % 2 == 0:
                    jmp_list = [
                        [(0, O1_o - 1), (1, O1_o), (0, O1_o)],
                        [(0, b_l), (1, O1_o - 1), (0, O1_o), (1, O1_o)],
                        [(0, O1_o), (2, e)],
                    ]
                    if c_piv == e - 2 and not od0_o and b_l > E:
                        jmp_list.append([(0, E + 1), (1, b_l), (0, O1_o)])
                    if s[c_piv] == 1 and c_piv > P_last and s[e - 1] == 1 and s[E + 1] == 1:
                        jmp_list.append([(0, E + 1), (2, e - 1), (0, E + 2), (1, O1_o - 2), (0, O1_o)])
                        jmp_list.append([(0, E + 1), (2, e - 1), (0, O1_o)])
                for jmp_ev in jmp_list:
                    to1, wo1 = run_ph(s, jmp_ev, t_piv)
                    if to1 and to1[0] == O1_o and to1[2] <= E + 1:
                        wf = finish_from_O1_e_anchor(s, to1, O1_o, to1[1], to1[2], E) if (to1[2] == e and (to1[3] & 7) == 7 and to1[1] % 2 == 0) else finish_from_O1_O1_c(s, to1, O1_o, E)
                        if wf:
                            full = w_piv + wo1 + wf
                            lib.verify_word(s, full, directed=True)
                            return full
                        # If to1 == (O1_o, b_odd, e, 7) with e < E, relay A -> O_piv2 and B -> O1_o/b_l to cross [e, E]:
                        if e < E and to1[2] == e and (to1[3] & 5) == 5 and len(od2_R_orig) >= 2:
                            for O_piv2 in od2_R_orig[1:]:
                                ev_in_12 = [i for i in evR_orig if O1_o < i < O_piv2]
                                rel_cands = [[(0, O_piv2), (2, E)]]
                                if b_l > E:
                                    rel_cands.append([(0, O_piv2 - 2), (1, b_l), (0, O_piv2), (2, E)])
                                    rel_cands.append([(1, b_l), (0, O_piv2), (2, E)])
                                    if ev_in_12:
                                        rel_cands.append([(0, ev_in_12[0] - 1), (1, b_l), (0, O_piv2), (2, E)])
                                if ev_in_12:
                                    v_12 = ev_in_12[0]
                                    rel_cands.append([(0, v_12), (1, O1_o), (0, O_piv2), (2, E)])
                                    if ev_in_12[-1] != v_12:
                                        rel_cands.append([(0, ev_in_12[-1]), (1, O1_o), (0, O_piv2), (2, E)])
                                for rel_ph in rel_cands:
                                    to2_r, wo2_r = run_ph(s, rel_ph, to1)
                                    if to2_r and to2_r[0] == O_piv2 and to2_r[2] == E and (to2_r[3] & 5) == 5:
                                        wf_r = finish_from_O1_anchor(s, to2_r, O_piv2, E)
                                        if wf_r:
                                            full_r = w_piv + wo1 + wo2_r + wf_r
                                            lib.verify_word(s, full_r, directed=True)
                                            return full_r
                                        ev_af_r = [i for i in evR_orig if i > O_piv2]
                                        if ev_af_r:
                                            Onx_r = min(i for i in range(ev_af_r[0] + 1, N, 2) if s[i] == 2)
                                            wk_r = max(i for i in ev_af_r if i < Onx_r)
                                            v_cands_r = [ev_af_r[0]] + ([wk_r] if wk_r != ev_af_r[0] else [])
                                            c_cands_r = [O1_o - 1, O1_o, O_piv2 - 2, O_piv2 - 1, O_piv2] if to2_r[1] >= O1_o else [O1_o - 1]
                                            for v_afr in v_cands_r:
                                                for c_pk_r in c_cands_r:
                                                    for mid_vr in ([[(1, v_afr)]] if v_afr == O_piv2 + 1 else [[(0, v_afr - 1), (1, v_afr)], [(1, v_afr), (0, v_afr)]]):
                                                        tv_r, wv_r = run_ph(s, [(2, c_pk_r)] + mid_vr, to2_r)
                                                        if tv_r and tv_r[:2] == (v_afr, v_afr) and (tv_r[3] & 3) == 3:
                                                            we_r = finish_from_even_Ok(s, tv_r, O_star_o, lam_o)
                                                            if we_r:
                                                                full_r2 = w_piv + wo1 + wo2_r + wv_r + we_r
                                                                lib.verify_word(s, full_r2, directed=True)
                                                                return full_r2

        # 3c. First internal even peak pivot c_piv == e (at (E, E, e, 3) waiting for strict right-witness):
        if c_piv == e and od2_R_orig:
            O1_o = od2_R_orig[0]
            ev0_o = [i for i in evR_orig if i < O1_o]
            od0_o = [i for i in odR_orig if i < O1_o]
            b_l = ev0_o[-1] if ev0_o else E
            lam_o = evR_orig[-1] if evR_orig else E
            O_star_o = min(i for i in range(lam_o + 1, N, 2) if s[i] == 2)
            # Direct right-witness via A -> O1_o (and C -> E if e < E):
            for ph_e_o1 in ([[(0, O1_o)]] if e == E else [[(0, O1_o), (2, E)], [(0, O1_o), (1, b_l), (2, E)]]):
                to1_e, wo1_e = run_ph(s, ph_e_o1, t_piv)
                if to1_e and to1_e[0] == O1_o and to1_e[2] == E and (to1_e[3] & 5) == 5:
                    wf_e = finish_from_O1_anchor(s, to1_e, O1_o, E)
                    if wf_e:
                        full_e = w_piv + wo1_e + wf_e
                        lib.verify_word(s, full_e, directed=True)
                        return full_e
            # Relay to O_piv2 > O1_o using B = E(2) and C = e(2), then escort C -> E and B5-Complete:
            if e < E and len(od2_R_orig) >= 2:
                for O_piv2 in od2_R_orig[1:]:
                    pre_o2_list = [[(0, O_piv2), (2, E)]]
                    if b_l > E:
                        pre_o2_list.append([(0, O_piv2 - 2), (1, b_l), (0, O_piv2), (2, E)])
                    for pre_o2 in pre_o2_list:
                        to2_e, wo2_e = run_ph(s, pre_o2, t_piv)
                        if to2_e and to2_e[0] == O_piv2 and to2_e[2] == E and (to2_e[3] & 5) == 5:
                            wf_o2 = finish_from_O1_anchor(s, to2_e, O_piv2, E)
                            if wf_o2:
                                full_o2 = w_piv + wo2_e + wf_o2
                                lib.verify_word(s, full_o2, directed=True)
                                return full_o2
                            ev_af_o2 = [i for i in evR_orig if i > O_piv2]
                            if ev_af_o2 and not od0_o:
                                v_af2 = ev_af_o2[0]
                                tv2_e, wv2_e = run_ph(s, [(2, O1_o - 1)] + ([(0, v_af2 - 1)] if v_af2 - 1 > O_piv2 else []) + [(1, v_af2)], to2_e)
                                if tv2_e and tv2_e[:2] == (v_af2, v_af2) and (tv2_e[3] & 3) == 3:
                                    we2_e = finish_from_even_Ok(s, tv2_e, O_star_o, lam_o)
                                    if we2_e:
                                        full2_e = w_piv + wo2_e + wv2_e + we2_e
                                        lib.verify_word(s, full2_e, directed=True)
                                        return full2_e

    for (c_piv, m_piv), w_piv in sorted_pivs:
        t_piv = (E, E, c_piv, m_piv)
        # 3d. Pure Binary Core (E, O_star_o): Truncated Super-Peak Lemma A Isomorphism,
        # Synchronized Even-1 Leap + Binary Parity Walk, and Ping-Pong Even-1 Teleportation:
        lam_3d = evR_orig[-1] if evR_orig else E
        O_star_3d = min(i for i in range(lam_3d + 1, N, 2) if s[i] == 2)
        if not [i for i in od2_R_orig if i < O_star_3d] and evR_orig:
            evR_c3 = [i for i in evR_orig if i < O_star_3d]
            odR_c3 = [i for i in odR_orig if i < O_star_3d]
            if evR_c3:
                lam_c3 = evR_c3[-1]
                al_c3 = odR_c3[-1] if odR_c3 else E - 1
                tail_O3 = [(2, N), (0, N)] if O_star_3d == N - 1 else [(2, O_star_3d), (1, N - 1), (2, N), (0, N)]
                tail_Om1_3 = [(2, N), (0, N)] if O_star_3d == N - 1 else [(1, N - 1), (2, N), (0, N)]

                # 3d-I: Truncated Super-Peak Lemma A Isomorphism
                starts_3d = []
                if c_piv % 2 == 1 and c_piv < e and m_piv == 7:
                    starts_3d.append((t_piv, '', E))
                elif c_piv % 2 == 0 and c_piv + 1 < e and E + 2 < O_star_3d:
                    ts3, ws3 = run_ph(s, [(0, E + 1), (1, E + 1), (0, E + 2)], t_piv)
                    if ts3 and ts3[:2] == (E + 2, E + 2):
                        starts_3d.append((ts3, ws3, E + 2))
                for t_st3, w_st3, E_st3 in starts_3d:
                    c_st3 = t_st3[2]
                    for P_tgt in [p for p in range(c_st3 + 2, e, 2) if s[p] == 2] + [e + 1]:
                        L_sl = tuple(1 if (i % 2 == 1 and s[i] == 2) else s[i] for i in range(c_st3 + 1, P_tgt - 1))
                        for pad in [(), (1, 1), (0, 1), (1, 1, 1, 1)]:
                            s_aux = (2, 2) + L_sl + pad + (2,) + tuple(s[E_st3 + 1:O_star_3d + 1]) + (2,)
                            E_aux = 2 + len(L_sl) + len(pad)
                            if E_aux < 4: continue
                            w_aux = cf.try_closed_form_dir(s_aux)
                            if not w_aux or not w_aux.endswith('yx'): continue
                            sc_a = lib.Sched(s_aux, E_aux - 1, directed=True); sc_a.go(1, E_aux)
                            if not w_aux.startswith(sc_a.word): continue
                            tc3 = t_st3; pr3 = []
                            for ch3 in w_aux[len(sc_a.word):-2]:
                                if tc3[0] >= O_star_3d - 1 and tc3[1] >= O_star_3d - 1:
                                    for fin3 in [
                                        [(0, O_star_3d), (1, O_star_3d), (2, O_star_3d)] + tail_Om1_3,
                                        [(1, O_star_3d), (0, O_star_3d), (2, O_star_3d)] + tail_Om1_3,
                                        [(2, O_star_3d)] + tail_Om1_3,
                                    ]:
                                        te3, we3 = run_ph(s, fin3, tc3)
                                        if te3 == (N, N, N, 7):
                                            full3 = w_piv + w_st3 + ''.join(pr3) + we3
                                            lib.verify_word(s, full3, directed=True)
                                            return full3
                                tc3 = lib.step(s, tc3, ch3, directed=True)
                                if tc3 is None: break
                                pr3.append(ch3)
                            if tc3 is not None:
                                for fin3 in [[(2, O_star_3d)] + tail_Om1_3, [(0, O_star_3d), (1, O_star_3d), (2, O_star_3d)] + tail_Om1_3]:
                                    te3, we3 = run_ph(s, fin3, tc3)
                                    if te3 == (N, N, N, 7):
                                        full3 = w_piv + w_st3 + ''.join(pr3) + we3
                                        lib.verify_word(s, full3, directed=True)
                                        return full3

                # 3d-II: Stay-Continuation Entry + Universal 4-Phase Synchronized Even-1 Leap + Binary Parity Walk
                b_entry_states = []
                if m_piv == 7 or c_piv % 2 == 1:
                    b_entry_states.append((t_piv, ''))
                if c_piv % 2 == 0 and c_piv < e and s[c_piv] == 1 and odR_c3:
                    r1_b = odR_c3[0]
                    for v_pick in [i for i in evR_c3 if i > r1_b]:
                        for pre_v1 in [
                            [(0, r1_b), (0, v_pick), (1, v_pick)],
                            [(0, r1_b), (2, c_piv + 2), (1, v_pick)],
                            [(0, v_pick - 1), (1, v_pick)],
                            [(0, v_pick), (1, r1_b), (1, v_pick)],
                        ]:
                            tv1, wv1 = run_ph(s, pre_v1, t_piv)
                            if tv1 and tv1[:2] == (v_pick, v_pick) and tv1[2] < e and tv1[3] == 7:
                                b_entry_states.append((tv1, wv1))
                                break

                leap_added = []
                for t_s0, w_s0 in list(b_entry_states):
                    p0, c0 = t_s0[0], t_s0[2]
                    if p0 == t_s0[1] and p0 % 2 == 0 and s[p0] >= 1 and c0 % 2 == 1 and c0 < e and s[c0] >= 1 and t_s0[3] == 7:
                        u0_nx = next((j for j in odR_c3 if j > p0), None)
                        if u0_nx is not None:
                            f_cands = [i for i in range(c0 + 1, e, 2) if s[i] == 1 and lib.M_od(s, c0 + 1, i) <= 1]
                            for f_nx_l in f_cands:
                                for v_far in [v for v in evR_c3 if v > u0_nx + 1]:
                                    for ph_leap in [
                                        [(1, v_far - 2), (0, u0_nx), (2, f_nx_l), (0, v_far)],
                                        [(1, v_far), (0, u0_nx), (2, f_nx_l), (0, v_far)],
                                    ]:
                                        tlp, wlp = run_ph(s, ph_leap, t_s0)
                                        if tlp == (v_far, v_far, f_nx_l, 7):
                                            leap_added.append((tlp, w_s0 + wlp))
                for t_ent, w_ent in b_entry_states + leap_added:
                    if t_ent[0] == t_ent[1] and t_ent[0] % 2 == 0 and t_ent[2] < e and t_ent[3] == 7:
                        w_pw = try_binary_parity_walk_to_Ostar(s, t_ent, O_star_3d, e, tail_Om1_3, N)
                        if w_pw:
                            full_pw = w_piv + w_ent + w_pw
                            lib.verify_word(s, full_pw, directed=True)
                            return full_pw

                # 3d-III: General C-Stepper + Ping-Pong Even-1 Teleportation across [E .. O_star_3d]
                tp_entry_states = b_entry_states + [st for st in leap_added if st[0][0] == lam_c3]
                for t_ent, w_ent in tp_entry_states:
                    c_ent = t_ent[2]
                    for Pk in [p for p in range(c_ent + (2 if c_ent % 2 == 1 else 1), e, 2) if s[p] == 2]:
                        ev_c_Pk = [i for i in range(c_ent + (1 if c_ent % 2 == 1 else 2), Pk, 2) if s[i] == 1]
                        c_goals = [Pk - 2] + ([ev_c_Pk[0] - 1, ev_c_Pk[-1] - 1] if ev_c_Pk else []) + ([ev_c_Pk[-2] - 1] if len(ev_c_Pk) >= 2 else [])
                        if c_ent % 2 == 0 and s[c_ent] == 1:
                            c_goals.append(c_ent)
                        for cg in sorted(set(g for g in c_goals if g >= c_ent)):
                            if cg == c_ent:
                                t_cg, w_cg = t_ent, ''
                            else:
                                if cg % 2 == 0: continue
                                t_cg, w_cg = step_c_to_goal_general(s, t_ent, cg, evR_c3, O_star_3d, E)
                            if t_cg is None: continue
                            pre_b_states = [(t_cg, '')]
                            if t_cg[2] % 2 == 1:
                                uy1 = lib.step(s, t_cg, 'y', directed=True)
                                if uy1 and (uy1[3] & 4):
                                    pre_b_states.append((uy1, 'y'))
                                    nx_a = next((i for i in evR_c3 if i > uy1[0]), None)
                                    nx_b = next((i for i in evR_c3 if i > uy1[1]), None)
                                    a0_cands = sorted(set(([nx_a] if nx_a else []) + [lam_c3]))
                                    b0_cands = sorted(set(([nx_b] if nx_b else []) + [lam_c3]))
                                    for a0_p in a0_cands:
                                        if a0_p > uy1[0]:
                                            ta0, wa0 = run_ph(s, [(0, a0_p)], uy1)
                                            if ta0:
                                                pre_b_states.append((ta0, 'y' + wa0))
                                                for b0_p in b0_cands:
                                                    if b0_p > ta0[1]:
                                                        tb0, wb0 = run_ph(s, [(1, b0_p)], ta0)
                                                        if tb0:
                                                            pre_b_states.append((tb0, 'y' + wa0 + wb0))
                                                        tb0p, wb0p = run_ph(s, [(2, Pk), (1, b0_p)], ta0)
                                                        if tb0p:
                                                            pre_b_states.append((tb0p, 'y' + wa0 + wb0p))
                            nx_b_cg = next((i for i in evR_c3 if i > t_cg[1]), None)
                            for b0_p in sorted(set(([nx_b_cg] if nx_b_cg else []) + [lam_c3])):
                                if b0_p > t_cg[1]:
                                    tb_pre, wb_pre = run_ph(s, [(1, b0_p)], t_cg)
                                    if tb_pre:
                                        pre_b_states.append((tb_pre, wb_pre))
                                        if tb_pre[2] % 2 == 1:
                                            uy2 = lib.step(s, tb_pre, 'y', directed=True)
                                            if uy2 and (uy2[3] & 4):
                                                pre_b_states.append((uy2, wb_pre + 'y'))
                            for t_base, w_base in pre_b_states:
                                b_stops = sorted(set(b for b in [lam_c3 - 3, lam_c3 - 2, lam_c3 - 1, lam_c3, t_base[1]] if t_base[1] <= b < O_star_3d))
                                for b_st in b_stops:
                                    tb, wb = run_ph(s, [(1, b_st)] if b_st > t_base[1] else [], t_base)
                                    if not tb: continue
                                    a_tps = sorted(set(a for a in [al_c3, lam_c3, O_star_3d - 4, O_star_3d - 3, O_star_3d - 2, O_star_3d - 1] if tb[0] <= a < O_star_3d))
                                    for a_tp in a_tps:
                                        a_ph = [(0, a_tp)] if a_tp > tb[0] else []
                                        end_cands = [
                                            a_ph + [(1, O_star_3d)] + tail_O3,
                                            a_ph + [(2, Pk), (1, O_star_3d)] + tail_O3,
                                            a_ph + [(2, Pk), (1, O_star_3d), (0, O_star_3d)] + tail_O3,
                                            a_ph + [(2, Pk), (1, O_star_3d), (0, O_star_3d)] + tail_Om1_3,
                                            a_ph + [(2, Pk), (1, O_star_3d), (0, O_star_3d), (2, O_star_3d)] + tail_Om1_3,
                                            a_ph + [(2, Pk - 1), (1, O_star_3d)] + tail_O3,
                                            a_ph + [(1, O_star_3d - 1), (0, O_star_3d - 1), (0, O_star_3d), (1, O_star_3d), (2, O_star_3d)] + tail_Om1_3,
                                            a_ph + [(1, O_star_3d - 1), (2, Pk - 2), (0, O_star_3d - 1), (0, O_star_3d), (1, O_star_3d), (2, O_star_3d)] + tail_Om1_3,
                                            a_ph + [(2, Pk), (1, O_star_3d - 1), (0, O_star_3d), (1, O_star_3d)] + tail_O3,
                                        ]
                                        for eph in end_cands:
                                            te, we = run_ph(s, eph, tb)
                                            if te == (N, N, N, 7):
                                                full_tp = w_piv + w_ent + w_cg + w_base + wb + we
                                                lib.verify_word(s, full_tp, directed=True)
                                                return full_tp

        # 3e. Multi-Peak Right-Wing Parity Walk + 4-Peak Relay Golden Bridge + B5-Complete:
        if od2_R_orig:
            O1_3e = od2_R_orig[0]
            t_3e = t_piv; w_acc_3e = ''
            for pos_odd in range(E + 1, N - 1, 2):
                c_lim_3e = E if pos_odd <= O1_3e else pos_odd - 1
                pair_3e = ('y', 'z') if (t_3e[2] % 2 == 1 and (t_3e[3] & 4)) else ('z', 'y')
                ok_3e = True; ws_3e = []
                for ch_3e in pair_3e:
                    t_3e = lib.step(s, t_3e, ch_3e, directed=True)
                    if t_3e is None: ok_3e = False; break
                    ws_3e.append(ch_3e)
                if not ok_3e: break
                wt_need_3e = s[pos_odd]
                if not (t_3e[3] & 1):
                    ev_c_3e = next((i for i in range(t_3e[2] + (1 if t_3e[2] % 2 == 1 else 2), c_lim_3e + 1, 2) if s[i] >= wt_need_3e), None)
                    if ev_c_3e is None: break
                    t_3e, wc1_3e = run_ph(s, [(2, ev_c_3e)], t_3e)
                    if t_3e is None or not (t_3e[3] & 1): break
                    ws_3e.append(wc1_3e)
                if not (t_3e[3] & 2):
                    od_c_3e = next((i for i in range(t_3e[2] + (2 if t_3e[2] % 2 == 1 else 1), c_lim_3e + 1, 2) if s[i] >= wt_need_3e), None)
                    if od_c_3e is None: break
                    t_3e, wc2_3e = run_ph(s, [(2, od_c_3e)], t_3e)
                    if t_3e is None or not (t_3e[3] & 2): break
                    ws_3e.append(wc2_3e)
                if s[pos_odd] == 2 and t_3e[2] < E:
                    Oa_cur = pos_odd
                    od2_after_oa = [o for o in od2_R_orig if o > Oa_cur]
                    if od2_after_oa and lib.M_ev(s, Oa_cur, od2_after_oa[0]) == 0:
                        Ob_nx = od2_after_oa[0]
                        for jmp_ob in [[(0, Ob_nx - 2), (1, Ob_nx), (2, E)], [(1, Ob_nx - 1), (0, Ob_nx), (2, E)]]:
                            t_ob, w_ob = run_ph(s, jmp_ob, t_3e)
                            if t_ob and t_ob[:2] == (Ob_nx, Ob_nx) and t_ob[2] >= E:
                                w_4p = try_four_peak_relay(s, t_ob, Ob_nx, od2_R_orig, evR_orig, O_star_3d, N)
                                if w_4p:
                                    full_4p = w_piv + w_acc_3e + ''.join(ws_3e) + w_ob + w_4p
                                    lib.verify_word(s, full_4p, directed=True)
                                    return full_4p
                                w_anc = finish_from_O1_anchor(s, t_ob, Ob_nx, E)
                                if w_anc:
                                    full_anc = w_piv + w_acc_3e + ''.join(ws_3e) + w_ob + w_anc
                                    lib.verify_word(s, full_anc, directed=True)
                                    return full_anc
                if s[pos_odd] == 2 and t_3e[2] >= E and pos_odd > O1_3e:
                    w_4p = try_four_peak_relay(s, t_3e, pos_odd, od2_R_orig, evR_orig, O_star_3d, N)
                    if w_4p:
                        full_4p = w_piv + w_acc_3e + ''.join(ws_3e) + w_4p
                        lib.verify_word(s, full_4p, directed=True)
                        return full_4p
                tx_3e = lib.step(s, t_3e, 'x', directed=True)
                if tx_3e is None: break
                ws_3e.append('x')
                t_3e = tx_3e; w_acc_3e += ''.join(ws_3e)
                p_ev_3e = pos_odd + 1
                if evR_orig and p_ev_3e > O1_3e and s[p_ev_3e] == 1 and (t_3e[3] & 3) == 3:
                    we_3e = finish_from_even_Ok(s, t_3e, O_star_3d, lam_3d)
                    if we_3e:
                        full_3e = w_piv + w_acc_3e + we_3e
                        lib.verify_word(s, full_3e, directed=True)
                        return full_3e
    return None

if __name__ == '__main__':
    def strip_wing(W):
        ev1 = [i for i in range(0, len(W), 2) if W[i] == 1]
        i_ev = ev1[0] if ev1 else len(W)
        od2 = [j for j in range(1, i_ev, 2) if W[j] == 2]
        j_pk = od2[-1] if od2 else -1
        return W[j_pk + 1:]

    def gen_core_wings(k):
        for w in product((0, 1, 2), repeat=k):
            if any(w[i] == 2 for i in range(0, k, 2)): continue
            if k > 0 and w[-1] == 2: continue
            if strip_wing(w) == w: yield w

    for mid in [(2,), (2, 0, 2), (2, 1, 2), (2, 0, 2, 0, 2)]:
        print(f'=== Exhaustive Core Check mid={mid} ===')
        for mode, pairs in [('P_vs_B', [(6,6), (6,8), (8,6)]), ('P_vs_P', [(4,4), (4,6), (6,6), (6,8)])]:
            for kL, kR in pairs:
                tot = cov = 0; rem = []
                for L in gen_core_wings(kL):
                    if 2 not in L: continue
                    for R in gen_core_wings(kR):
                        if (mode == 'P_vs_B') != (2 not in R): continue
                        if mode == 'P_vs_P' and kL == kR and L > R: continue
                        s = (2, 2) + L + mid + R[::-1] + (2, 2)
                        tot += 1
                        if solve_lemma_B_dir(s) or solve_lemma_B_dir(s[::-1]):
                            cov += 1
                        else:
                            rem.append((''.join(map(str, L)), ''.join(map(str, R))))
                print(f'  {mode} ({kL},{kR}): {cov}/{tot}, rem={len(rem)}', rem[:4])

    # Random 5000 UNSTRIPPED long Regime I patterns!
    rng = random.Random(20261125)
    rfails = []
    for _ in range(5000):
        def rand_wing():
            k = 2 * rng.randint(1, 18)
            w = []
            for i in range(k):
                if i % 2 == 0: w.append(rng.randint(0, 1))
                else: w.append(0 if i == k - 1 else rng.choice([0, 1, 2]))
            if w and w[-1] == 2: w[-1] = 1
            return tuple(w)
        L = rand_wing(); R = rand_wing()
        if 2 not in L and 2 not in R:
            if len(L) >= 2: L = (L[0], 2) + L[2:]
            else: continue
        mlen = rng.choice([1, 3, 5, 7, 9])
        mid = [2]
        for i in range(1, mlen - 1):
            allow2 = (mid[-1] != 2) and (i < mlen - 2)
            mid.append(rng.choice([0, 1, 2] if allow2 else [0, 1]))
        if mlen > 1: mid.append(2)
        s = (2, 2) + L + tuple(mid) + R[::-1] + (2, 2)
        if not (solve_lemma_B_dir(s) or solve_lemma_B_dir(s[::-1])):
            rfails.append((L, tuple(mid), R))
    print(f'Random 5000 unstripped long Regime I: {5000 - len(rfails)}/5000, fails={len(rfails)}')
    for L, mid, R in rfails[:5]:
        print('  rfail:', ''.join(map(str, L)), mid, ''.join(map(str, R)))
