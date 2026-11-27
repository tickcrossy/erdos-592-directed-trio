import sys
sys.path.insert(0, '/Users/jxy/.gemini/antigravity/brain/0023b7ba-1bbb-42f1-a285-1b0de4b7ee00/scratch')
import op1_lib as lib
from prove_step1_complete import try_dir_step1

def gen_middles(mlen):
    assert mlen % 2 == 1 and mlen >= 7
    def rec(pref):
        idx = len(pref)
        if idx == mlen - 1:
            if pref[-1] == 2: return
            M = tuple(pref + [2])
            if M[::-1] < M: return
            if not any(M[i] == 2 for i in range(1, mlen - 1, 2)): return
            if M[1] == 1 and M[-2] == 1: return
            yield M
            return
        allow2 = pref[-1] != 2 and idx != mlen - 2
        for w in range(3 if allow2 else 2):
            yield from rec(pref + [w])
    yield from rec([2])

def exec_ok(s, a0, phases):
    sc = lib.Sched(s, a0)
    for cur, tgt in phases:
        while sc.t[cur] < tgt:
            target_par = (sc.t[cur] + 1) % 2
            l = next(l for l, rs in lib.RULE.items() if (cur, target_par) in rs)
            nxt = lib.step(s, sc.t, l, directed=True)
            if nxt is None: return None
            sc.t = nxt; sc.word += l
    try:
        lib.verify_word(s, sc.word, directed=True)
        return sc.word
    except AssertionError:
        return None

def finish_from_EEL_vev1(s, E):
    N = len(s) - 1
    R = max(i for i in range(E + 1, N - 1, 2) if s[i] == 1)
    return [(1, R), (2, E - 1), (1, N - 3), (0, N - 1), (2, N), (0, N)]

def try_all_known_dir(s):
    N = len(s) - 1
    ev_peaks = [i for i in range(4, N - 3, 2) if s[i] == 2]
    e, E = ev_peaks[0], ev_peaks[-1]
    odd_peaks = [i for i in range(e + 1, E, 2) if s[i] == 2]
    K, L = odd_peaks[0], odd_peaks[-1]
    R = max(i for i in range(E + 1, N - 1, 2) if s[i] == 1)
    e2 = ev_peaks[1] if len(ev_peaks) >= 2 else E
    lim = min(K, e2)
    ev_before_lim = [i for i in range(e + 2, lim, 2) if s[i] == 1]
    od_before_lim = [i for i in range(e + 1, lim, 2) if s[i] == 1]

    # Step 1 complete solver (single odd peak, no internal even peak)
    if len(ev_peaks) == 2 and len(odd_peaks) == 1:
        if try_dir_step1(s): return 'Step1'

    # 1. R3T1: s[E-2] == 2 and s[E-1] == 0
    if s[E - 2] == 2 and s[E - 1] == 0:
        if exec_ok(s, E - 3, [(1, L), (2, e - 2), (1, N - 3), (0, N - 1), (2, N), (0, N)]):
            return 'R3T1'

    # 2. Upgraded R3T2: s[L-1] == 0 and (L, E) all 0s
    if s[L - 1] == 0 and all(s[i] == 0 for i in range(L + 1, E)):
        if exec_ok(s, L - 1, [(2, L - 2), (0, E - 1), (1, N - 4), (2, E), (0, N - 1), (2, N), (0, N)]):
            return 'UpR3T2'

    # 3. Super-Theorem B2 (s[E-1] == 1)
    if s[E - 1] == 1:
        if all(s[i] == 0 for i in range(e + 1, K)):
            if exec_ok(s, e - 1, [(1, E - 1), (2, e), (0, N - 4), (2, K), (1, N - 1), (0, N - 1), (2, N), (0, N)]):
                return 'B2_K'
        if od_before_lim:
            kU = od_before_lim[0]
            if not ev_before_lim or kU < ev_before_lim[0]:
                if exec_ok(s, e - 1, [(1, E - 1), (2, e), (0, N - 4), (2, kU), (1, N - 2), (2, N), (0, N)]):
                    return 'B2a'
            else:
                if exec_ok(s, e - 1, [(1, E - 1), (2, e), (0, R - 1), (2, kU), (1, N - 2), (0, N - 1), (2, N), (0, N)]):
                    return 'B2b'

    # 4. Upgraded Result 2 (when s[E-1] == 1, s[K-1] == 1, M_ev(e,K-1)<=1, M_od(e,K-1)==1) + original Result 2
    if s[E - 1] == 1 and s[e + 1] == 0:
        if s[K - 1] == 1 and lib.M_ev(s, e, K - 1) <= 1 and lib.M_od(s, e, K - 1) == 1:
            if exec_ok(s, e - 1, [(1, E - 2), (2, e - 1), (0, E), (2, K - 1), (0, N - 3), (1, N - 1), (2, N), (0, N)]):
                return 'UpgRes2'
        if s[K - 1] == lib.M_od(s, E + 1, N - 2) and lib.M_ev(s, e, K - 2) == 1 and lib.M_od(s, e, K - 1) == 1:
            if exec_ok(s, e - 1, [(1, E - 2), (2, e - 1), (0, E), (2, K - 1), (0, N - 3), (1, N - 1), (2, N), (0, N)]):
                return 'Res2'

    # 5. Upgraded R3T3 & GenB5b
    mev_LE = lib.M_ev(s, L, E)
    mod_LE = lib.M_od(s, L, E)
    if s[e + 1] == 0 and mod_LE == 1 and mev_LE == s[e + 2]:
        if all(s[i] == 0 for i in range(e + 1, K)):
            if exec_ok(s, e - 1, [(1, L), (2, e - 2), (1, E - 1), (0, N - 4), (2, K), (1, N - 1), (0, N - 1), (2, N), (0, N)]):
                return 'UpR3T3_K'
        if od_before_lim:
            kU = od_before_lim[0]
            if not ev_before_lim or kU < ev_before_lim[0]:
                if exec_ok(s, e - 1, [(1, L), (2, e - 2), (1, E - 1), (0, N - 4), (2, kU), (1, N - 2), (2, N), (0, N)]):
                    return 'UpR3T3_kU'
            else:
                if exec_ok(s, e - 1, [(1, L), (2, e - 2), (1, E - 1), (0, R - 1), (2, kU), (1, N - 2), (0, N - 1), (2, N), (0, N)]):
                    return 'UpR3T3_fU'

    if s[e + 1] == 0 and s[L + 1] == 0 and mev_LE == 1 and mod_LE == 1 and ev_before_lim and od_before_lim:
        fU, kU = ev_before_lim[0], od_before_lim[0]
        if fU < kU:
            pref = [(1, L), (2, e - 2)] + ([(0, fU - 1)] if fU >= e + 4 else [])
            if exec_ok(s, e - 1, pref + [(1, E - 1), (0, R - 1), (2, kU), (1, N - 2), (0, N - 1), (2, N), (0, N)]):
                return 'GenB5b'

    # 6. Relay Theorem (K-Relay + General P-Relay + EEL_vev1 upgrade!)
    a_val = lib.M_od(s, L, E)
    G_K = next(i for i in range(K + 1, E + 1, 2) if s[i] > 0)
    b_K = lib.M_od(s, K, G_K)
    if a_val <= s[K - 1]:
        if b_K == 0:
            if exec_ok(s, L - 1, [(1, e - 2), (2, K - 1), (0, E), (1, N - 3), (2, G_K), (0, N - 1), (2, N), (0, N)]):
                return 'Relay_b0'
        if s[G_K] == 1 and b_K <= 1:
            if exec_ok(s, L - 1, [(1, e - 2), (2, K - 1), (0, E), (1, R), (2, G_K), (0, N - 3), (2, G_K + 1), (1, N - 1), (0, N - 1), (2, N), (0, N)]):
                return 'Relay_b1'

    for P in odd_peaks:
        if s[P - 2] < 1 or a_val != s[P - 1]:
            continue
        G_P = next(i for i in range(P + 1, E + 1, 2) if s[i] > 0)
        b_P = lib.M_od(s, P, G_P)
        if b_P == 0:
            if exec_ok(s, L - 1, [(2, P - 2), (1, e), (0, E), (1, N - 3), (2, G_P), (0, N - 1), (2, N), (0, N)]):
                return 'PRelay_b0'
        if s[G_P] == 1 and b_P <= 1:
            if exec_ok(s, L - 1, [(2, P - 2), (1, e), (0, E), (1, R), (2, G_P), (0, N - 2), (1, N - 1), (0, N - 1), (2, N), (0, N)]):
                return 'PRelay_b1'
        if P == L and mev_LE == 1 and mod_LE <= 1:
            if exec_ok(s, L - 1, [(2, L - 2), (1, e), (0, E)] + finish_from_EEL_vev1(s, E)):
                return 'LRelay_EEL'

    # 7. gen_5step
    if s[L - 1] == 1:
        G = next(i for i in range(L + 1, E + 1, 2) if s[i] > 0)
        q = max(i for i in range(L, G, 2) if s[i] > 0)
        if q > L and q + 1 == G and s[G] == 2 and G < E and lib.M_ev(s, G, E) == 0 and lib.M_od(s, G, E) == 0:
            if E - G < 4 or q == L + 2:
                if exec_ok(s, L - 1, [(2, L - 2), (0, q), (1, L), (0, E - 1), (2, q - 1), (1, E), (1, N - 3), (2, G), (0, N - 1), (2, N), (0, N)]):
                    return 'Gen5Step'

    # 8. Generalized User's Result 1: K == L, s[e+1] == 1, s[E-1] == 0, M_ev(e, q) == 0
    # Works for ANY (G, E) (even with arbitrary internal even peaks G <= ... <= E)!
    if K == L and s[e + 1] == 1 and s[E - 1] == 0:
        G = next(i for i in range(L + 1, E + 1, 2) if s[i] > 0)
        q = max(i for i in range(L, G, 2) if s[i] > 0)
        if lib.M_ev(s, e, q) == 0:
            if q == L:
                if exec_ok(s, 1, [(1, e - 2), (2, e - 1), (0, E - 2), (2, L - 1), (1, N - 3), (2, G), (0, N - 1), (2, N), (0, N)]):
                    return 'GenRes1_qL'
            else:
                if exec_ok(s, 1, [(1, e - 2), (2, e - 1), (0, E - 2), (1, L), (2, q - 1), (1, N - 3), (2, G), (0, N - 1), (2, N), (0, N)]):
                    return 'GenRes1_qgtL'

    # 9. Multi-Odd-Peak Collapse Theorem M1:
    # No internal even peaks in (L, E), M_ev(L, E) == 1, M_ev(K, L) == 0,
    # M_od(e, K) == 0, M_ev(e, K) == 1:
    # Let q be last positive odd pos in [L, E). If s[q+1] == 1 and all pos in (q+1, E) are 0:
    # S_2(q), C->K-1, B->K, C->L-1, A->E, B->E + finish_from_EEL_vev1!
    if len([x for x in ev_peaks if x > L]) == 1 and mev_LE == 1 and lib.M_ev(s, K, L) == 0:
        if lib.M_od(s, e, K) == 0 and lib.M_ev(s, e, K) == 1 and len([x for x in ev_peaks if x < K]) == 1:
            q_last = max(i for i in range(L, E, 2) if s[i] >= 1)
            if s[q_last + 1] == 1 and all(s[i] == 0 for i in range(q_last + 2, E)):
                phases = [(1, e - 2), (2, e - 1), (0, q_last), (2, K - 1), (1, K), (2, L - 1), (0, E), (1, E)] + finish_from_EEL_vev1(s, E)
                if exec_ok(s, 1, phases):
                    return 'ThmM1a'

    # 10. Multi-Peak Relay across Internal Even Peak G < E (Theorem M2):
    # Suppose s[L-1] == 1, K == L (or s[L-2] >= 1), G in (L, E) has s[G] == 2 (first pos >0 even after L),
    # q in (L, G) is last odd 1 before G, s[E-1] == 0:
    # If G + 2 < E and s[G+2] >= 1 and all pos in (G+2, E) are 0:
    # Reach (G+1, e, L-1, 7) -> B->q-1 (pushes C->L, A->G+2>=1 supporting M_ev(e,q-1)<=1 and passing L witnessing C=L!)
    # -> C->q-1 (pushes A->G+3, then A->E-1 if needed) -> z(B->q,C->q) -> B->E -> F_B!
    if s[L - 1] == 1 and s[E - 1] == 0:
        G = next(i for i in range(L + 1, E + 1, 2) if s[i] > 0)
        q = max(i for i in range(L, G, 2) if s[i] > 0)
        if q > L and s[G] == 2 and G < E and s[G + 2] >= 1 and all(s[i] == 0 for i in range(G + 3, E)):
            if K == L and lib.M_ev(s, e, L) <= 1:
                phases = [(1, e - 2), (2, L - 1), (0, G + 1), (1, q - 1), (2, q - 1), (0, E - 1), (1, q), (2, q), (1, N - 3), (2, G), (0, N - 1), (2, N), (0, N)]
                if exec_ok(s, L - 1, phases):
                    return 'ThmM2'

    # 11. Multi-Odd-Peak Collapse Theorem M1b:
    # No internal even peaks in (L, E), mev_LE == 1, s[E-1] == 0, s[e+1] == 1, M_ev(e, L) == 0:
    if len([x for x in ev_peaks if x > L]) == 1 and mev_LE == 1 and s[E - 1] == 0 and s[e + 1] == 1 and lib.M_ev(s, e, L) == 0:
        phases = [(1, e - 2), (2, e - 1), (0, E - 2), (1, e + 1), (2, e + 1), (1, K - 1), (2, K - 1), (1, K), (2, K), (2, L - 1), (1, E)] + finish_from_EEL_vev1(s, E)
        if exec_ok(s, 1, phases):
            return 'ThmM1b'

    # 11b. Multi-Odd-Peak Collapse Theorem M1c (hV < rV, M_od(e, K) == 0, M_ev(e, K) == 1, no internal even peaks in (e, E)):
    if len(ev_peaks) == 2 and mev_LE == 1 and mod_LE == 1 and lib.M_od(s, e, K) == 0 and lib.M_ev(s, e, K) == 1:
        evV = [i for i in range(L + 1, E, 2) if s[i] == 1]
        odV = [i for i in range(L + 2, E, 2) if s[i] == 1]
        hV, rV = evV[-1], odV[-1]
        fU = next(i for i in range(e + 2, K, 2) if s[i] == 1)
        if hV < rV:
            if rV == hV + 1:
                phases = [(1, e - 2), (2, e - 1), (0, hV), (1, K - 1), (2, L - 1), (0, E), (1, E)] + finish_from_EEL_vev1(s, E)
                if exec_ok(s, 1, phases):
                    return 'ThmM1c_adj'
            elif hV >= L + 1:
                phases = [(1, e - 2), (2, e - 1), (0, hV - 1), (2, fU - 2), (1, K - 1), (0, rV), (2, L - 1), (0, E), (1, E)] + finish_from_EEL_vev1(s, E)
                if exec_ok(s, 1, phases):
                    return 'ThmM1c_gen'

    # 12. Even-Peak Jump Theorem M3 (truncating internal even peaks e_2 <= ... <= e* < K):
    ev_before_K = [x for x in ev_peaks if e < x < K]
    if ev_before_K and s[E - 1] == 0:
        e_star = ev_before_K[-1]
        od_LE = [i for i in range(L + 2, E, 2) if s[i] == 1]
        if od_LE and lib.M_od(s, e, e_star) == 0 and lib.M_ev(s, e_star, K) == 0:
            q_last = od_LE[-1]
            if q_last == E - 3 and s[E - 2] == 0:
                od_after_estar = [i for i in range(e_star + 1, K, 2) if s[i] == 1]
                pref = [(1, q_last), (2, e), (0, K), (2, e_star)]
                if all(s[i] == 0 for i in range(e_star + 1, K)):
                    tgtA = N - 3 if K == e_star + 1 else N - 4
                    if exec_ok(s, e_star - 1, pref + [(0, tgtA), (2, K), (1, N - 1), (0, N - 1), (2, N), (0, N)]):
                        return 'ThmM3_K'
                elif od_after_estar:
                    kp = od_after_estar[0]
                    tgtA = N - 3 if kp == e_star + 1 else N - 4
                    if exec_ok(s, e_star - 1, pref + [(0, tgtA), (2, kp), (1, N - 2), (2, N), (0, N)]):
                        return 'ThmM3_kp'

    return None

if __name__ == '__main__':
    wL = (2,2,0,0,0,1,0,0,0,1)
    wR = (1,0,0,0,1,0,1,0,0,0,2,2)

    for mlen in (7, 9, 11, 13):
        tot = cov = 0
        uncov = []
        for M in gen_middles(mlen):
            tot += 1
            s = wL + M + wR
            r = try_all_known_dir(s) or try_all_known_dir(s[::-1])
            if r: cov += 1
            else: uncov.append(M)
        print(f'Middle len {mlen} (canon full len {mlen+12}): {cov}/{tot} covered, remaining={len(uncov)}')
        cats = {}
        for M in uncov:
            evp = [i for i in range(0, mlen, 2) if M[i] == 2]
            odp = [i for i in range(1, mlen, 2) if M[i] == 2]
            key = (len(evp), len(odp), M[1], M[-2])
            cats.setdefault(key, []).append(''.join(map(str, M)))
        for k, v in sorted(cats.items(), key=lambda x: -len(x[1])):
            print(f'  (ev={k[0]}, od={k[1]}, bdry=({k[2]},{k[3]})): {len(v)}  ex={v[:5]}')
