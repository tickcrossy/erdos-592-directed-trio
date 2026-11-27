import sys
sys.path.insert(0, '/Users/jxy/.gemini/antigravity/brain/0023b7ba-1bbb-42f1-a285-1b0de4b7ee00/scratch')
import op1_lib as lib

def gen_dirB_canonical(N):
    """
    Generate canonical Direction B residual patterns of index N (length N+1):
    s[0..5] = 2,2,0,0,0,1, s[6] = 2 (e=6), s[N-6] = 2 (E=N-6), s[N-5..N] = 1,0,0,0,2,2,
    at least one odd peak in (e, E), no adjacent 2s, not (s[e+1]==1 and s[E-1]==1),
    up to reversal s <= s[::-1].
    Note: what if e > 6 or E < N-6? Let's generate ALL Direction B residuals of index N!
    """
    e_min = 6
    # Actually let's generate ALL Direction B residuals of index N:
    # Both wings have even=0, odd<=1, s[3]=s[N-3]=0, s[e-1]=s[E+1]=1, at least one odd 2 in (e,E), (s[e+1],s[E-1])!=(1,1)
    def rec(pref):
        idx = len(pref)
        if idx == N - 1:
            s = tuple(pref + [2, 2])
            if s[::-1] < s:
                return
            ev_peaks = [i for i in range(4, N - 3, 2) if s[i] == 2]
            if not ev_peaks:
                return
            e, E = ev_peaks[0], ev_peaks[-1]
            if e < 6 or E > N - 6:
                return
            if s[e - 1] != 1 or s[E + 1] != 1:
                return
            if s[3] != 0 or s[N - 3] != 0:
                return
            # Left wing (1, e): even=0, odd<=1
            if any(s[i] != 0 for i in range(2, e, 2)) or any(s[i] == 2 for i in range(3, e, 2)):
                return
            # Right wing (E, N-1): even=0, odd<=1
            if any(s[i] != 0 for i in range(E + 2, N - 1, 2)) or any(s[i] == 2 for i in range(E + 1, N - 1, 2)):
                return
            # At least one odd 2 in (e, E)
            if not any(s[i] == 2 for i in range(e + 1, E, 2)):
                return
            if s[e + 1] == 1 and s[E - 1] == 1:
                return
            yield s
            return
        allow2 = pref[-1] != 2 and idx != N - 2 and idx not in (2, 3, N - 3, N - 2)
        for w in range(3 if allow2 else 2):
            if idx in (2, 3, N - 3, N - 2) and w != 0:
                continue
            yield from rec(pref + [w])
    yield from rec([2, 2])

def exec_ok(s, a0, phases):
    sc = lib.Sched(s, a0)
    for cur, tgt in phases:
        while sc.t[cur] < tgt:
            target_par = (sc.t[cur] + 1) % 2
            l = next(l for l, rs in lib.RULE.items() if (cur, target_par) in rs)
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

def finish_from_EEL_vev1(s, E):
    N = len(s) - 1
    R = max(i for i in range(E + 1, N - 1, 2) if s[i] == 1)
    return [(1, R), (2, E - 1), (1, N - 3), (0, N - 1), (2, N), (0, N)]

def finish_from_EEq_all0(s, E):
    N = len(s) - 1
    return [(1, N - 3), (2, E), (0, N - 1), (2, N), (0, N)]

def try_general_dirB(s):
    """Test ALL proved arbitrary-length theorems (existing + new multi-peak upgrades) in direction s."""
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

    # 1. User's Round 3 Thm 1: s[E-2] == 2 and s[E-1] == 0
    if s[E - 2] == 2 and s[E - 1] == 0:
        w = exec_ok(s, E - 3, [(1, L), (2, e - 2), (1, N - 3), (0, N - 1), (2, N), (0, N)])
        if w: return 'R3T1(s[E-2]=2,s[E-1]=0)'

    # 2. User's Round 3 Thm 2: s[L-2] == s[L-1] == 0 and (L, E) all 0s
    if s[L - 2] == 0 and s[L - 1] == 0 and all(s[i] == 0 for i in range(L + 1, E)):
        w = exec_ok(s, L - 1, [(2, L - 2), (0, E - 1), (1, N - 4), (2, E), (0, N - 1), (2, N), (0, N)])
        if w: return 'R3T2(zero_around_L)'

    # 3. Super-Theorem B2 (s[E-1] == 1):
    if s[E - 1] == 1:
        if all(s[i] == 0 for i in range(e + 1, K)):
            w = exec_ok(s, e - 1, [(1, E - 1), (2, e), (0, N - 4), (2, K), (1, N - 1), (0, N - 1), (2, N), (0, N)])
            if w: return 'B2_K(s[E-1]=1)'
        if od_before_lim:
            kU = od_before_lim[0]
            if not ev_before_lim or kU < ev_before_lim[0]:
                w = exec_ok(s, e - 1, [(1, E - 1), (2, e), (0, N - 4), (2, kU), (1, N - 2), (2, N), (0, N)])
                if w: return 'B2a(s[E-1]=1,kU_first)'
            else:
                w = exec_ok(s, e - 1, [(1, E - 1), (2, e), (0, R - 1), (2, kU), (1, N - 2), (0, N - 1), (2, N), (0, N)])
                if w: return 'B2b(s[E-1]=1,fU_first)'

    # 4. Generalized B->L Theorem (B3 + B5b for multi-peak!):
    # Works whenever (L, E) has NO even peaks (M_ev(L,E)<=1, M_od(L,E)==1) AND:
    # - either M_ev(L,E) == s[e+2] and s[e+1] == 0 (Upgraded R3T3)
    # - or s[L+1] == 0, M_ev(L,E) == 1, M_od(L,E) == 1, and (e, lim) has fU < kU!
    mev_LE = lib.M_ev(s, L, E)
    mod_LE = lib.M_od(s, L, E)
    if s[e + 1] == 0 and mod_LE == 1 and mev_LE == s[e + 2]:
        if all(s[i] == 0 for i in range(e + 1, K)):
            w = exec_ok(s, e - 1, [(1, L), (2, e - 2), (1, E - 1), (0, N - 4), (2, K), (1, N - 1), (0, N - 1), (2, N), (0, N)])
            if w: return 'UpR3T3_K'
        if od_before_lim:
            kU = od_before_lim[0]
            if not ev_before_lim or kU < ev_before_lim[0]:
                w = exec_ok(s, e - 1, [(1, L), (2, e - 2), (1, E - 1), (0, N - 4), (2, kU), (1, N - 2), (2, N), (0, N)])
                if w: return 'UpR3T3_kU'
            else:
                w = exec_ok(s, e - 1, [(1, L), (2, e - 2), (1, E - 1), (0, R - 1), (2, kU), (1, N - 2), (0, N - 1), (2, N), (0, N)])
                if w: return 'UpR3T3_fU'

    if s[e + 1] == 0 and s[L + 1] == 0 and mev_LE == 1 and mod_LE == 1 and ev_before_lim and od_before_lim:
        fU, kU = ev_before_lim[0], od_before_lim[0]
        if fU < kU:
            pref = [(1, L), (2, e - 2)]
            if fU >= e + 4:
                pref.append((0, fU - 1))
            w = exec_ok(s, e - 1, pref + [(1, E - 1), (0, R - 1), (2, kU), (1, N - 2), (0, N - 1), (2, N), (0, N)])
            if w: return 'GenB5b(fU<kU)'

    # 5. User's Relay Theorem (General P-Relay: for ANY internal odd peak P in [K, L]!)
    # Wait: let's check User's Relay Theorem + our General P-Relay!
    # User's Relay: a = M_od(L, E) <= s[K-1], and (b == 0 or (s[G]==1 and b<=1)) where G is first pos >0 even in (K, E]
    a_val = lib.M_od(s, L, E)
    G = next(i for i in range(K + 1, E + 1, 2) if s[i] > 0)
    b_val = lib.M_od(s, K, G)
    if a_val <= s[K - 1]:
        if b_val == 0:
            w = exec_ok(s, L - 1, [(1, e - 2), (2, K - 1), (0, E), (1, N - 3), (2, G), (0, N - 1), (2, N), (0, N)])
            if w: return 'Relay(b=0)'
        if s[G] == 1 and b_val <= 1:
            # User's Relay b=1 branch
            w = exec_ok(s, L - 1, [(1, e - 2), (2, K - 1), (0, E), (1, R), (2, G), (0, N - 3), (2, G + 1), (1, N - 1), (0, N - 1), (2, N), (0, N)])
            if w: return 'Relay(b=1)'
        # PLUS our new 6-phase EEL finisher when K == L (or even K <= L if (K, E) has no odd/even peaks?):
        if mev_LE == 1 and mod_LE <= 1 and all(s[i] < 2 for i in range(K + 1, E)):
            w = exec_ok(s, L - 1, [(1, e - 2), (2, K - 1), (0, E)] + finish_from_EEL_vev1(s, E))
            if w: return 'Relay+EEL_vev1'

    # 6. User's Result 2 / Upgraded Result 2 (Early meeting at C = e when s[e+1]==1 and s[K-1]==1 or M_od(L,E)==s[K-1]):
    if s[e + 1] == 1 and (s[K - 1] == 1 or lib.M_od(s, L, E) == s[K - 1]):
        # I(1), B->e-2, C->e-1, A->L-1, C->e, B->K-1, A->E-1? Let's recall Result 2:
        # Actually let's check Step 1 complete solver if len(ev_peaks)==2 and len(odd_peaks)==1!
        pass

    if len(ev_peaks) == 2 and len(odd_peaks) == 1:
        from prove_step1_complete import try_dir_step1
        r1 = try_dir_step1(s)
        if r1: return 'Step1_' + r1[0]

    return None

for N in (18, 20, 22, 24):
    tot = cov = 0
    uncov = []
    for s in gen_dirB_canonical(N):
        tot += 1
        r = try_general_dirB(s) or try_general_dirB(s[::-1])
        if r:
            cov += 1
        else:
            uncov.append(s)
    print(f'Length {N+1}: {cov}/{tot} covered (remaining={len(uncov)})')
    if uncov:
        for u in uncov[:12]:
            evp = [i for i in range(4, N - 3, 2) if u[i] == 2]
            odp = [i for i in range(evp[0] + 1, evp[-1], 2) if u[i] == 2]
            print(f'  {"".join(map(str, u))}  ev={evp} od={odp}')
