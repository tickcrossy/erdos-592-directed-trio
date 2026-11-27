"""
verify_op1_complete.py -- independent verification of the unified OP1 dispatcher.

  python3 verify_op1_complete.py exh  NMIN NMAX     # all hard patterns (classes s <= s^r)
  python3 verify_op1_complete.py rand SEED COUNT    # random long hard patterns, all regimes
  python3 verify_op1_complete.py r3   SEED COUNT    # random long Regime III (incl. residual family)
  python3 verify_op1_complete.py R    NMIN NMAX     # every member of the residual family R (Lemma C §3.7)
  python3 verify_op1_complete.py rR   SEED COUNT    # random long members of R (N up to ~170)

Every schedule is re-verified with op1_lib.verify_word(..., directed=True).
"""
import os, sys, random, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import op1_lib as lib
from solve_op1_complete import solve_op1, regime


def check(s):
    r = solve_op1(s)
    if r is None:
        return regime(s), False
    d, reg, w = r
    lib.verify_word(s if d == 'F' else s[::-1], w, directed=True)
    return reg, True


def rand_hard(rng, wmax, mmax):
    """Random hard pattern: wings with arbitrary odd values in {0,1,2} and even values in
    {0,1}, middle arbitrary (no adjacent 2s), regime chosen at random."""
    kind = rng.choice(['I', 'II', 'III', 'III'])
    def wing(k, outer_first):
        w = []
        pod = rng.random(); pev = rng.random() if kind == 'II' else 0.0
        p2 = rng.random() * 0.5 if kind == 'I' else 0.0
        for i in range(k):
            odd = (i % 2 == 1) if outer_first else (i % 2 == 0)
            if odd:
                r = rng.random()
                w.append(2 if r < p2 else (1 if rng.random() < pod else 0))
            else:
                w.append(1 if rng.random() < pev else 0)
        return w
    kL = 2 * rng.randint(1, wmax // 2); kR = 2 * rng.randint(1, wmax // 2)
    L = wing(kL, True)          # positions 2..e-1 : position 2+i, odd iff i odd
    R = wing(kR, False)         # positions E+1..N-2 : position E+1+i, odd iff i even
    L[-1] = L[-1] if L[-1] != 2 else 1
    R[0] = R[0] if R[0] != 2 else 1
    for w in (L, R):
        for i in range(1, len(w)):
            if w[i] == 2 and w[i - 1] == 2: w[i] = 1
    if R and R[-1] == 2: R[-1] = 1
    m = 2 * rng.randint(0, mmax // 2) + 1
    M = [2]; pb = rng.random() * 0.35 + 0.05; p1 = rng.random()
    for i in range(1, m - 1):
        allow2 = M[-1] != 2 and i < m - 2
        M.append(2 if (allow2 and rng.random() < pb) else (1 if rng.random() < p1 else 0))
    if m > 1: M.append(2)
    s = tuple([2, 2] + L + M + R + [2, 2])
    for i in range(1, len(s)):
        assert not (s[i] == 2 and s[i - 1] == 2) or i in (1, len(s) - 1), s
    return s


def residual_family(N):
    """Enumerate the Layer-1 residual family R of LEMMA_C_PROOF.md §3.7 at size N
    (pattern enumeration only; used to test the solver, never inside it)."""
    from itertools import product

    def mids(L):
        def rec(pref):
            if len(pref) == L:
                yield tuple(pref); return
            i = len(pref)
            opts = [0, 1]
            if i not in (0, L - 1) and (not pref or pref[-1] != 2): opts.append(2)
            for v in opts:
                yield from rec(pref + [v])
        yield from rec([])

    for e in range(6, N - 11, 2):
        for E in range(e + 6, N - 5, 2):
            nl = (e - 6) // 2; nr = (N - E - 6) // 2
            for mid in mids(E - e - 1):
                if not any(mid[k] == 2 for k in range(0, len(mid), 2)): continue
                if mid[0] == 1 and mid[-1] == 1: continue
                for lw in product((0, 1), repeat=nl):
                    for rw in product((0, 1), repeat=nr):
                        s = [0] * (N + 1)
                        s[0] = s[1] = s[N - 1] = s[N] = 2
                        for j, v in enumerate(lw): s[5 + 2 * j] = v
                        s[e - 1] = 1; s[e] = 2
                        for k, v in enumerate(mid): s[e + 1 + k] = v
                        s[E] = 2; s[E + 1] = 1
                        for j, v in enumerate(rw): s[E + 3 + 2 * j] = v
                        yield tuple(s)


def rand_residual(rng, wl=60, ml=41):
    """Random long member of the residual family R."""
    while True:
        kL = 2 * rng.randint(3, wl // 2); kR = 2 * rng.randint(3, wl // 2)
        L = [rng.randint(0, 1) if i % 2 else 0 for i in range(kL)]   # pos 2+i
        L[-1] = 1; L[1] = 0                                          # s[e-1]=1, s[3]=0
        R = [rng.randint(0, 1) if i % 2 == 0 else 0 for i in range(kR)]  # pos E+1+i
        R[0] = 1; R[-2] = 0                                          # s[E+1]=1, s[N-3]=0
        m = 2 * rng.randint(3, ml // 2) + 1
        M = [2]; pb = rng.random() * 0.4 + 0.1; p1 = rng.random()
        for i in range(1, m - 1):
            allow2 = M[-1] != 2 and i < m - 2
            M.append(2 if (allow2 and rng.random() < pb) else (1 if rng.random() < p1 else 0))
        M.append(2)
        s = tuple([2, 2] + L + M + R + [2, 2])
        N = len(s) - 1
        e = 2 + kL; E = e + m - 1
        if any(s[i] == 2 for i in range(e + 1, E, 2)) and not (s[e + 1] == 1 and s[E - 1] == 1):
            return s


if __name__ == '__main__':
    mode = sys.argv[1]
    t0 = time.time()
    if mode == 'R':
        for N in range(int(sys.argv[2]), int(sys.argv[3]) + 1, 2):
            tot = 0; bad = []
            for s in residual_family(N):
                if regime(s) != 'III':
                    raise AssertionError('residual family must lie in Regime III')
                tot += 1
                if not check(s)[1]: bad.append(s)
            print(f'R, N={N}: {tot - len(bad)}/{tot}  failures={len(bad)}  ({time.time() - t0:.0f}s)', flush=True)
            for s in bad[:5]:
                print('   FAIL', ''.join(map(str, s)))
        sys.exit(0)
    if mode == 'exh':
        for N in range(int(sys.argv[2]), int(sys.argv[3]) + 1, 2):
            cnt = {}; bad = []
            for s in lib.hard_patterns(N):
                if s[::-1] < s:
                    continue
                reg, ok = check(s)
                c = cnt.setdefault(reg, [0, 0]); c[0] += 1; c[1] += ok
                if not ok: bad.append(s)
            print(f'N={N}: ' + ', '.join(f'Regime {k}: {v[1]}/{v[0]}' for k, v in sorted(cnt.items()))
                  + f'  failures={len(bad)}  ({time.time() - t0:.0f}s)', flush=True)
            for s in bad[:5]:
                print('   FAIL', ''.join(map(str, s)))
    else:
        seed, count = int(sys.argv[2]), int(sys.argv[3])
        rng = random.Random(seed)
        cnt = {}; bad = []; maxN = 0
        for i in range(count):
            if mode == 'rand':
                s = rand_hard(rng, 60, 41)
            elif mode == 'rR':
                s = rand_residual(rng)
            else:
                sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
                s = rand_hard(rng, 60, 41)
                while regime(s) != 'III':
                    s = rand_hard(rng, 60, 41)
            maxN = max(maxN, len(s) - 1)
            reg, ok = check(s)
            c = cnt.setdefault(reg, [0, 0]); c[0] += 1; c[1] += ok
            if not ok: bad.append(s)
        print(f'{mode} seed={seed}: ' + ', '.join(f'Regime {k}: {v[1]}/{v[0]}' for k, v in sorted(cnt.items()))
              + f'  failures={len(bad)}  maxN={maxN}  ({time.time() - t0:.0f}s)', flush=True)
        for s in bad[:5]:
            print('   FAIL N=%d' % (len(s) - 1), ''.join(map(str, s)))
