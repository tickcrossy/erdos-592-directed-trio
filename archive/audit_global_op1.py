import sys
sys.path.insert(0, '/Users/jxy/.gemini/antigravity/brain/0023b7ba-1bbb-42f1-a285-1b0de4b7ee00/scratch')
import op1_lib as lib
from scan_multipeak_middles import try_all_known_dir, exec_ok

def check_global_dir(s):
    """
    Check ALL proved arbitrary-length theorems in a single direction `s`!
    Every branch constructs the explicit word and calls verify_word(s, w, directed=True)
    (via exec_ok) so ZERO unproved claims can slip through!
    """
    N = len(s) - 1
    ev_peaks = [i for i in range(2, N - 1, 2) if s[i] == 2]
    e, E = ev_peaks[0], ev_peaks[-1]

    # 1. E == N - 4 (Note 3 Eq. 9):
    # Covered by Note 3 Thm 1 (s[E+1]==0), Note 3 Thm 2 (s[N-3]==1 and max_ev <= s[N-2]), or Note 3 Eq. 8 (no odd 1 in tail and s[N-2]==1).
    tail_odds = [i for i in range(E + 1, N - 1, 2) if s[i] > 0]
    tail_has_odd_peak = any(s[i] == 2 for i in range(E + 1, N - 1, 2))
    max_tail_ev = lib.M_ev(s, E, N - 1)

    if not tail_has_odd_peak:
        # Note 3 Eq. 8 / Note 4: tail has NO odd 1s at all (all odd in (E, N-1) are 0), and max_tail_ev <= s[N-2]:
        if not tail_odds and max_tail_ev <= s[N - 2]:
            w = exec_ok(s, E - 1, [(1, N - 2), (0, N - 1), (2, N), (0, N)])
            if w: return 'Tail_NoOdd1_EndEv'

        # Note 3 Thm 1: max_tail_ev == 0 and s[E+1] == 0
        if max_tail_ev == 0 and s[E + 1] == 0:
            if not tail_odds:
                w = exec_ok(s, E - 1, [(1, N - 2), (0, N - 1), (2, N), (0, N)])
                if w: return 'N3T1_all0'
            else:
                alpha = tail_odds[-1]
                f = next(i for i in range(2, E + 1, 2) if s[i] > 0)
                t = max(i for i in range(1, f, 2) if s[i] > 0)
                if s[t] == 2:
                    w = exec_ok(s, E - 1, [(2, t), (1, N - 3), (2, f), (0, N - 1), (2, N), (0, N)])
                else:
                    g = max(i for i in range(1, f, 2) if s[i] == 2)
                    w = exec_ok(s, E - 1, [(2, g), (1, alpha), (2, t), (1, N - 3), (2, f), (0, N - 1), (2, N), (0, N)])
                if w: return 'N3T1'

        # Note 3 Thm 2: s[N-3] == 1 and max_tail_ev <= s[N-2]
        if s[N - 3] == 1 and max_tail_ev <= s[N - 2]:
            f = next(i for i in range(2, E + 1, 2) if s[i] > 0)
            g = max(i for i in range(1, f, 2) if s[i] == 2)
            w = exec_ok(s, E - 1, [(2, g), (1, N - 3), (2, f), (0, N - 1), (2, N), (0, N)])
            if w: return 'N3T2'

        # Note 4 Thm: s[E+1] == 0, s[E+2] == 1, s[N-2] == 1, and if tail_odds: exists even 1 in (alpha, N-2)
        if s[E + 1] == 0 and E + 2 <= N - 2 and s[E + 2] == 1 and s[N - 2] == 1:
            alpha = tail_odds[-1] if tail_odds else None
            if not tail_odds or any(s[i] == 1 for i in range(alpha + 1, N - 2, 2)):
                f = next(i for i in range(2, E + 1, 2) if s[i] > 0)
                h = max(i for i in range(1, f, 2) if s[i] > 0)
                if not tail_odds:
                    w = exec_ok(s, E - 1, [(1, N - 2), (0, N - 1), (2, N), (0, N)])
                elif s[h] == 2:
                    w = exec_ok(s, E - 1, [(2, h), (1, N - 3), (2, f), (0, N - 1), (2, N), (0, N)])
                else:
                    g = max(i for i in range(1, f, 2) if s[i] == 2)
                    w = exec_ok(s, E - 1, [(2, g), (1, alpha), (2, h), (1, N - 3), (2, f), (0, N - 1), (2, N), (0, N)])
                if w: return 'N4T1'

        # Note 5 Thm: max_tail_ev == 0, and (f < e or s[h] == 2)
        if max_tail_ev == 0:
            f = next(i for i in range(2, E + 1, 2) if s[i] > 0)
            h = max(i for i in range(1, f, 2) if s[i] > 0)
            if s[f] == 1 or s[h] == 2:
                if not tail_odds:
                    w = exec_ok(s, E - 1, [(1, N - 2), (0, N - 1), (2, N), (0, N)])
                elif s[h] == 2:
                    w = exec_ok(s, E - 1, [(2, h), (1, N - 3), (2, f), (0, N - 1), (2, N), (0, N)])
                else:
                    alpha = tail_odds[-1]
                    g = max(i for i in range(1, f, 2) if s[i] == 2)
                    if alpha == N - 3:
                        w = exec_ok(s, E - 1, [(2, g), (1, alpha), (2, f), (0, N - 1), (2, N), (0, N)])
                    else:
                        w = exec_ok(s, E - 1, [(2, g), (1, alpha), (2, f), (0, N - 3), (1, N - 1), (0, N - 1), (2, N), (0, N)])
                if w: return 'N5T1'

    # Note 2: max_tail_od == 0 and tail has at least one even 1, PROVIDED prefix has Z_E?
    # Wait: Note 2 only holds if Z_E holds, which is NOT unconditional. Skip unless explicit!

    # Note 6 Line 1342: Both wings even=0, and right wing has odd peak!
    if lib.M_ev(s, 1, e) == 0 and max_tail_ev == 0 and tail_has_odd_peak:
        p = max(i for i in range(1, e, 2) if s[i] == 2)
        alpha = tail_odds[-1]
        if alpha == N - 3:
            w = exec_ok(s, E - 1, [(2, p), (1, alpha), (2, e), (0, N - 1), (2, N), (0, N)])
        else:
            w = exec_ok(s, E - 1, [(2, p), (1, alpha), (2, e), (0, N - 2), (1, N - 1), (0, N - 1), (2, N), (0, N)])
        if w: return 'N6_WingOddPeak'

    # Note 6 Line 1360: Both wings even=0, and NO internal odd peak anywhere!
    if lib.M_ev(s, 1, e) == 0 and max_tail_ev == 0 and not any(s[i] == 2 for i in range(3, N - 1, 2)):
        p = max(i for i in range(1, e, 2) if s[i] > 0)
        w = exec_ok(s, E - 1, [(2, p), (1, N - 3), (2, e), (0, N - 1), (2, N), (0, N)])
        if w: return 'N6_NoOddPeak'

    # Note 6 Line 1379: e < E, odd peak in (e, N-1), M_e(1,e)<=s[e+1], M_o(1,e)<=s[E-1], M_e(E,N-1)<=s[N-2], M_o(E,N-1)<=s[e+1]
    if e < E and any(s[i] == 2 for i in range(e + 1, N - 1, 2)):
        if lib.M_ev(s, 1, e) <= s[e + 1] and lib.M_od(s, 1, e) <= s[E - 1] and max_tail_ev <= s[N - 2] and lib.M_od(s, E, N - 1) <= s[e + 1]:
            w = exec_ok(s, e - 1, [(1, E - 1), (2, e), (0, N - 2), (1, N - 1), (0, N - 1), (2, N), (0, N)])
            if w: return 'N6_Sandwiched'

    # Note 7 Common-Witness Theorem (in reverse direction — so check on s[::-1] by testing forward version before reversing? Wait: Note 7 constructs a word on s whose REVERSE is an OP1 word for s[::-1]! Actually let's check Note 7 directly on s^r):
    # On s^r, let sr = s[::-1]; if sr has L, T < e_r and E_r < O <= N-1 with the 4 inequalities, its reversed word is a valid OP1 word for s!
    sr = s[::-1]
    er, Er = N - E, N - e
    odd_peaks_L = [i for i in range(1, er, 2) if sr[i] == 2]
    odd_peaks_R = [i for i in range(Er + 1, N, 2) if sr[i] == 2]
    for L0 in odd_peaks_L:
        T_cands = [1] if L0 == 1 else odd_peaks_L
        for T0 in T_cands:
            if T0 > 1 and lib.M_ev(sr, 1, T0) > sr[L0 - 1]: continue
            if lib.M_ev(sr, L0, er) > sr[T0 + 1]: continue
            for O0 in odd_peaks_R:
                if lib.M_od(sr, L0, er) > sr[O0 - 1]: continue
                if lib.M_ev(sr, O0, N - 1) > sr[er + 1]: continue
                # Build普通 word on sr, reverse it, and verify_word on s!
                sc = lib.Sched(sr, L0 if T0 == 1 else L0 - 1, directed=False)
                phases = ([] if T0 == 1 else [(1, T0)]) + [(2, O0 - 1), (0, er), (1, N - 1), (2, N), (0, N)]
                ok_sr = True
                for cur, tgt in phases:
                    while sc.t[cur] < tgt:
                        tpar = (sc.t[cur] + 1) % 2
                        l = next(l for l, rs in lib.RULE.items() if (cur, tpar) in rs)
                        nxt = lib.step(sr, sc.t, l, directed=False)
                        if nxt is None: ok_sr = False; break
                        sc.t = nxt; sc.word += l
                    if not ok_sr: break
                if ok_sr:
                    w_rev = sc.word[::-1]
                    try:
                        lib.verify_word(s, w_rev, directed=True)
                        return 'N7_CommonWitness'
                    except AssertionError:
                        pass

    # Direction B residual family check:
    if e >= 6 and E <= N - 6 and lib.M_ev(s, 1, e) == 0 and max_tail_ev == 0 and s[e - 1] == 1 and s[E + 1] == 1 and s[3] == 0 and s[N - 3] == 0:
        if not any(s[i] == 2 for i in range(3, e, 2)) and not tail_has_odd_peak and any(s[i] == 2 for i in range(e + 1, E, 2)):
            if not (s[e + 1] == 1 and s[E - 1] == 1):
                rb = try_all_known_dir(s)
                if rb: return 'DirB_' + rb

    return None

if __name__ == '__main__':
    for N in (8, 10, 12, 14, 16):
        tot = cov = 0
        uncov = []
        for s in lib.hard_patterns(N):
            if s[::-1] < s: continue
            tot += 1
            r = check_global_dir(s) or check_global_dir(s[::-1])
            if r: cov += 1
            else: uncov.append(s)
        print(f'ALL Hard Patterns len {N+1}: {cov}/{tot} covered by proved theorems, remaining={len(uncov)}')
        if uncov:
            # Classify remaining!
            cats = {}
            for u in uncov:
                evp = [i for i in range(2, N - 1, 2) if u[i] == 2]
                e, E = evp[0], evp[-1]
                wL_ev = lib.M_ev(u, 1, e)
                wR_ev = lib.M_ev(u, E, N - 1)
                wL_od2 = any(u[i] == 2 for i in range(3, e, 2))
                wR_od2 = any(u[i] == 2 for i in range(E + 1, N - 1, 2))
                key = (len(evp), f'wEv=({wL_ev},{wR_ev})', f'wOd2=({int(wL_od2)},{int(wR_od2)})')
                cats.setdefault(key, []).append(''.join(map(str, u)))
            for k, v in sorted(cats.items(), key=lambda x: -len(x[1])):
                print(f'  {k}: {len(v)}  ex={v[:3]}')
