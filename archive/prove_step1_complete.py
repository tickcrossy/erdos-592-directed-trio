import sys
sys.path.insert(0, '/Users/jxy/.gemini/antigravity/brain/0023b7ba-1bbb-42f1-a285-1b0de4b7ee00/scratch')
import random
from itertools import product
import op1_lib as lib

def exec_and_verify(s, a0, phases):
    sc = lib.Sched(s, a0)
    for cur, tgt in phases:
        sc.go(cur, tgt)
    w = sc.word
    lib.verify_word(s, w, directed=True)
    return w

def finish_from_EEL_vev1(s, E):
    N = len(s) - 1
    R = max(i for i in range(E + 1, N - 1, 2) if s[i] == 1)
    return [(1, R), (2, E - 1), (1, N - 3), (0, N - 1), (2, N), (0, N)]

def finish_from_EEq_all0(s, E):
    N = len(s) - 1
    return [(1, N - 3), (2, E), (0, N - 1), (2, N), (0, N)]

def try_dir_step1(s):
    """
    Complete, tautological 7-branch solver for Step 1 (single odd peak L in (e, E),
    no internal even peaks in (e, E), arbitrary Direction B wings).
    """
    N = len(s) - 1
    ev_peaks = [i for i in range(4, N - 3, 2) if s[i] == 2]
    assert len(ev_peaks) == 2
    e, E = ev_peaks[0], ev_peaks[1]
    L = next(i for i in range(e + 1, E, 2) if s[i] == 2)
    evU = [i for i in range(e + 2, L, 2) if s[i] == 1]
    odU = [i for i in range(e + 1, L, 2) if s[i] == 1]
    evV = [i for i in range(L + 1, E, 2) if s[i] == 1]
    odV = [i for i in range(L + 2, E, 2) if s[i] == 1]

    # Branch 1: v_od = 0
    if not odV:
        phases = [(1, e - 2), (2, L - 1), (0, E)] + (finish_from_EEL_vev1(s, E) if evV else finish_from_EEq_all0(s, E))
        return ('B1(v_od=0)', exec_and_verify(s, L - 1, phases))

    if not odU:
        return None # handled in rev by Branch 1

    # Now odU and odV are BOTH non-empty!
    kU, rU = odU[0], odU[-1]
    kV, rV = odV[0], odV[-1]
    R = max(i for i in range(E + 1, N - 1, 2) if s[i] == 1)

    # Branch 2: s[E - 1] == 1
    if s[E - 1] == 1:
        if not evU or kU < evU[0]:
            phases = [(1, E - 1), (2, e), (0, N - 4), (2, kU), (1, N - 2), (2, N), (0, N)]
            return ('B2a(s[E-1]=1,kU_first)', exec_and_verify(s, e - 1, phases))
        else:
            phases = [(1, E - 1), (2, e), (0, R - 1), (2, kU), (1, N - 2), (0, N - 1), (2, N), (0, N)]
            return ('B2b(s[E-1]=1,fU_first)', exec_and_verify(s, e - 1, phases))

    if s[e + 1] == 1:
        return None # handled in rev by Branch 2

    # Now s[e + 1] == 0 and s[E - 1] == 0!

    # Branch 3: u_ev = 0 and v_ev = 0
    if not evU and not evV:
        phases = [(1, L), (2, e - 2), (1, E - 1), (0, N - 4), (2, kU), (1, N - 2), (2, N), (0, N)]
        return ('B3(u_ev=v_ev=0)', exec_and_verify(s, e - 1, phases))

    # Branch 4: u_ev = 0 and v_ev = 1 (rev handles u_ev = 1, v_ev = 0)
    if not evU and evV:
        phases = [(1, e - 2), (2, e - 1), (0, E - 2), (1, kU - 1), (2, L - 1), (1, E)] + finish_from_EEL_vev1(s, E)
        return ('B4(u_ev=0,v_ev=1)', exec_and_verify(s, 1, phases))

    if not evV:
        return None # handled in rev by Branch 4

    # Now evU and evV are BOTH non-empty!
    fU, hU = evU[0], evU[-1]
    fV, hV = evV[0], evV[-1]

    # Branch 5a: s[L - 1] == 1 (rev handles s[L + 1] == 1)
    if s[L - 1] == 1:
        phases = [(1, e - 2), (2, L - 1), (0, E)] + finish_from_EEL_vev1(s, E)
        return ('B5a(s[L-1]=1)', exec_and_verify(s, L - 1, phases))

    if s[L + 1] == 1:
        return None # handled in rev by Branch 5a

    # Now s[L - 1] == 0 and s[L + 1] == 0!

    # Branch 5b: fU < kU (rev handles rV < hV!)
    if fU < kU:
        pref = [(1, L), (2, e - 2)]
        if fU >= e + 4:
            pref.append((0, fU - 1))
        phases = pref + [(1, E - 1), (0, R - 1), (2, kU), (1, N - 2), (0, N - 1), (2, N), (0, N)]
        return ('B5b(fU<kU,s[L+1]=0)', exec_and_verify(s, e - 1, phases))

    # Branch 5c: kU < fU and hV < rV
    if kU < fU and hV < rV:
        phases = [(1, e - 2), (2, e - 1), (0, rV - 1), (1, kU - 1), (2, L - 1), (0, E)] + finish_from_EEL_vev1(s, E)
        return ('B5c(kU<fU,hV<rV)', exec_and_verify(s, 1, phases))

    return None

def solve_step1_complete(s):
    r = try_dir_step1(s)
    if r is not None:
        return ('fwd', r[0], r[1])
    r = try_dir_step1(s[::-1])
    if r is not None:
        return ('rev', r[0], r[1])
    raise AssertionError(f"IMPOSSIBLE! Uncovered single-odd-peak pattern: {s}")

if __name__ == '__main__':
    # 1. Test the exact monsters that failed earlier!
    wL = (2,2,0,0,0,1,0,0,0,1,2)
    wR = (2,1,0,0,0,1,0,1,0,0,0,2,2)
    for Us in ['0001100100', '0001101100', '000001101100', '0110101010100100']:
        U = tuple(map(int, Us)); V = U[::-1]
        s = wL + U + (2,) + V + wR
        d, tag, _ = solve_step1_complete(s)
        print(f'Monster U={Us}: PASSED via {d} {tag}!')

    # 2. Exhaustive verification on |U|, |V| in {(2,2), (2,4), (4,4), (2,6), (4,6), (6,6), (8,8)}
    for lu, lv in [(2,2), (2,4), (4,4), (2,6), (4,6), (6,6)]:
        tot = 0; counts = {}
        for U in product((0,1), repeat=lu):
            for V in product((0,1), repeat=lv):
                if U[0]==1 and V[-1]==1: continue
                if lu == lv and (V[::-1], U[::-1]) < (U, V): continue
                tot += 1
                s = wL + U + (2,) + V + wR
                _, tag, _ = solve_step1_complete(s)
                counts[tag] = counts.get(tag, 0) + 1
        print(f'[Exhaustive |U|={lu}, |V|={lv}, gapped wings] {tot}/{tot} PASSED!')

    tot8 = 0; counts8 = {}
    for U in product((0,1), repeat=8):
        for V in product((0,1), repeat=8):
            if U[0]==1 and V[-1]==1: continue
            if (V[::-1], U[::-1]) < (U, V): continue
            tot8 += 1
            s = (2,2,0,0,0,1,2) + U + (2,) + V + (2,1,0,0,0,2,2)
            _, tag, _ = solve_step1_complete(s)
            counts8[tag] = counts8.get(tag, 0) + 1
    print(f'[Exhaustive |U|=8, |V|=8] {tot8}/{tot8} PASSED! Breakdown: {counts8}')

    # 3. 5,000 random long patterns (up to total length ~250, adversarial + uniform)
    rng = random.Random(20261124)
    def rand_wL(k):
        m = []
        for _ in range(k): m += [rng.choice([0,1]), 0]
        return (2,2,0,0,0) + tuple(m) + (1,2)
    def rand_wR(k):
        m = []
        for _ in range(k): m += [0, rng.choice([0,1])]
        return (2,1) + tuple(m) + (0,0,0,2,2)

    rcounts = {}
    for idx in range(5000):
        lu = rng.choice([2, 4, 6, 10, 16, 30, 60, 100])
        lv = rng.choice([2, 4, 6, 10, 16, 30, 60, 100])
        if idx % 3 == 0:
            # Force double-zero + s[L-1]=s[L+1]=0 + leading zeros to stress B5b & B5c!
            U = [0]*lu; V = [0]*lv
            for i in range(rng.randint(1, max(1, lu-2)), lu-1): U[i] = rng.choice([0, 1])
            for i in range(1, rng.randint(2, max(2, lv))):
                if i < lv - 1: V[i] = rng.choice([0, 1])
            U, V = tuple(U), tuple(V)
        else:
            U = tuple(rng.choice([0,1]) for _ in range(lu))
            V = tuple(rng.choice([0,1]) for _ in range(lv))
        if U[0]==1 and V[-1]==1: U = (0,) + U[1:]
        s = rand_wL(rng.randint(0, 15)) + U + (2,) + V + rand_wR(rng.randint(0, 15))
        _, tag, _ = solve_step1_complete(s)
        rcounts[tag] = rcounts.get(tag, 0) + 1
    print(f'[Random 5,000 long patterns up to len ~250] 5000/5000 PASSED! Breakdown: {rcounts}')
