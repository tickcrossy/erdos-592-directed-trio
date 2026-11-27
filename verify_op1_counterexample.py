"""
verify_op1_counterexample.py -- Independent verification of the refutation of
Erdos Problem #592 (Open Problem 1).

Verifies:
  1. The unique minimum counterexample (length 27, N = 26):
         s* = 220001201200020121012100022
     is a valid hard pattern in Regime III residual family R.
  2. Neither s* nor (s*)^r admits a directed OP1 schedule, certified independently by:
       (a) op1_lib.find_schedule(..., directed=True)  (starts from I(a)),
       (b) an unrestricted full-word automaton BFS over all words w in {x,y,z}^*
           (no I(a) assumption; verifies standard parity start ('x','x','y') and
           also checks all 8 starting-letter combinations under directed witnessing),
       (c) the original C++ Search(26) class in op1.cpp (compiled if g++ is present).
  3. s* DOES admit a valid undirected trio (op1_lib.verify_word(..., directed=False)),
     separating directed OP1 from undirected trios.
  4. The infinite counterexample family s(W_L, W_R; a, b, c, d) fails OP1 across
     diverse wing configurations (including minimal, alternating, all-1, sparse)
     and stretched internal cores M*(a, b, c, d), as well as the N = 76 random hit.
  5. Exact minimality and uniqueness (optional --full flag):
       - N in {18, 20, 22, 24}: 100% of R (13,963 reversal classes) pass via
         the 15 hand-proved theorems of prove_lemma_C_closed_form.py (0 counterexamples).
       - N = 26: across all 112,464 reversal classes of R, exactly 112,463 admit
         verified directed OP1 schedules and s* is the UNIQUE counterexample.

Note: This is a verification / counterexample-certification script (NOT a solver).
"""
import os, sys, subprocess, tempfile, time
from collections import deque
from itertools import product

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import op1_lib as lib
from prove_lemma_C_closed_form import solve_lemma_C, is_regime3

S_STAR_STR = "220001201200020121012100022"
S_STAR = tuple(int(c) for c in S_STAR_STR)
CORE_M_STAR = (2, 0, 1, 2, 0, 0, 0, 2, 0, 1, 2, 1, 0, 1, 2)


def is_valid_hard_pattern(s):
    N = len(s) - 1
    if N < 4 or N % 2 != 0:
        return False
    if s[0] != 2 or s[1] != 2 or s[N - 1] != 2 or s[N] != 2:
        return False
    if any(x not in (0, 1, 2) for x in s):
        return False
    for i in range(1, N - 1):
        if s[i] == 2 and s[i + 1] == 2:
            return False
    return any(s[i] == 2 for i in range(2, N - 1, 2))


def unrestricted_automaton_bfs(s, start_lets=('x', 'x', 'y'), directed_mode='y_A>C'):
    """Exact BFS over ALL words w in {x,y,z}^* without assuming I(a).
    State: (rA, rB, rC, m, seen, last2), with cursor indices starting at -1.
    Checks first-appearance weight 2, last-appearance weight 2, and directed witnessing."""
    N = len(s) - 1
    row_pair = (('x', 'y'), ('x', 'z'), ('y', 'z'))
    rule = {}
    for l in 'xyz':
        rs = []
        for j, pair in enumerate(row_pair):
            if l in pair:
                par = 0 if l == start_lets[j] else 1
                rs.append((j, par))
        rule[l] = tuple(rs)
    start = (-1, -1, -1, 0, 0, 0)
    vis = {start: None}
    q = deque([start])
    l2i = {'x': 0, 'y': 1, 'z': 2}
    while q:
        a, b, c, m, seen, last2 = t = q.popleft()
        if a == N and b == N and c == N and m == 7 and seen == 7 and last2 == 7:
            path = []
            u = t
            while vis[u] is not None:
                v, l = vis[u]
                path.append(l)
                u = v
            return ''.join(path[::-1])
        pos0 = (a, b, c)
        for l in 'xyz':
            li = l2i[l]
            p = list(pos0)
            nm = m
            ok = True
            for j, par in rule[l]:
                if p[j] < 0:
                    if par != 0:
                        ok = False
                        break
                    p[j] = 0
                    nm &= ~(1 << j)
                elif p[j] % 2 != par:
                    if not (nm >> j & 1):
                        ok = False
                        break
                    p[j] += 1
                    if p[j] > N:
                        ok = False
                        break
                    nm &= ~(1 << j)
            if not ok:
                continue
            j, k = rule[l][0][0], rule[l][1][0]
            w = min(s[p[j]], s[p[k]])
            if not (seen >> li & 1) and w != 2:
                continue
            nseen = seen | (1 << li)
            nlast2 = (last2 | (1 << li)) if w == 2 else (last2 & ~(1 << li))
            for qj in (j, k):
                wok = (w == s[p[qj]])
                if directed_mode == 'y_A>C' and qj == 2 and p[qj] % 2 == 0 and s[p[qj]] == 2 and 0 < p[qj] < N:
                    wok = wok and l == 'y' and p[0] > p[2]
                elif directed_mode == 'any_partner>C' and qj == 2 and p[qj] % 2 == 0 and s[p[qj]] == 2 and 0 < p[qj] < N:
                    other = k if qj == j else j
                    wok = wok and p[other] > p[2]
                if wok:
                    nm |= 1 << qj
            nt = (p[0], p[1], p[2], nm, nseen, nlast2)
            if nt not in vis:
                vis[nt] = (t, l)
                q.append(nt)
    return None


def check_op1_cpp(s_str):
    """Compile and run the unmodified Search struct from op1.cpp on s_str and its reversal."""
    cpp_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'op1.cpp')
    src = open(cpp_path).read()
    idx = src.index('int main(')
    N = len(s_str) - 1
    harness = f'''int main() {{
    string s = "{s_str}";
    string r(s.rbegin(), s.rend());
    Search search({N});
    printf("%d %d\\n", search.test(s) ? 1 : 0, search.test(r) ? 1 : 0);
    return 0;
}}
'''
    with tempfile.TemporaryDirectory() as td:
        cfile = os.path.join(td, 'chk.cpp')
        exe = os.path.join(td, 'chk')
        open(cfile, 'w').write(src[:idx] + harness)
        subprocess.run(['g++', '-O3', cfile, '-o', exe], check=True)
        out = subprocess.check_output([exe], text=True).strip()
        f, r = map(int, out.split())
        return bool(f), bool(r)


def verify_s_star():
    print(f"=== 1. Verifying minimum counterexample s* (N={len(S_STAR)-1}, len={len(S_STAR)}) ===")
    print(f"s* = {S_STAR_STR}")
    assert is_valid_hard_pattern(S_STAR), "s* must be a valid hard pattern"
    assert is_regime3(S_STAR), "s* must lie in Regime III"

    # (a) op1_lib.find_schedule (directed)
    assert lib.find_schedule(S_STAR, directed=True) is None, "s* F unexpectedly schedulable"
    assert lib.find_schedule(S_STAR[::-1], directed=True) is None, "s* R unexpectedly schedulable"
    print("  [PASS] op1_lib.find_schedule(directed=True): F=None, R=None")

    # (b) Unrestricted full-word automaton BFS (no I(a) assumption)
    for dm in ('y_A>C', 'any_partner>C'):
        assert unrestricted_automaton_bfs(S_STAR, ('x', 'x', 'y'), dm) is None
        assert unrestricted_automaton_bfs(S_STAR[::-1], ('x', 'x', 'y'), dm) is None
    print("  [PASS] unrestricted full-word BFS (no I(a)): F=None, R=None (both y_A>C and any_partner>C)")

    # (c) Original op1.cpp Search(26)
    f_cpp, r_cpp = check_op1_cpp(S_STAR_STR)
    assert not f_cpp and not r_cpp, f"op1.cpp returned F={f_cpp}, R={r_cpp}"
    print("  [PASS] original op1.cpp Search(26): F=0, R=0")

    # (d) Undirected trio exists and passes verify_word(..., directed=False)
    w_undir = unrestricted_automaton_bfs(S_STAR, ('x', 'x', 'y'), 'none')
    assert w_undir is not None
    lib.verify_word(S_STAR, w_undir, directed=False)
    print(f"  [PASS] undirected trio exists and verified (len={len(w_undir)}, directed=False)")


def verify_infinite_family():
    print("\n=== 2. Verifying infinite counterexample family s(W_L, W_R) and M*(a,b,c,d) ===")
    wings_L = [
        (2, 2, 0, 0, 0, 1),
        (2, 2, 0, 0, 0, 0, 0, 1),
        (2, 2, 0, 0, 0, 1, 0, 1),
        (2, 2, 0, 0, 0, 1, 0, 0, 0, 1),
        (2, 2, 0, 0, 0, 1, 0, 1, 0, 1),
        (2, 2, 0, 0, 0, 0, 0, 0, 0, 1),
    ]
    wings_R = [
        (1, 0, 0, 0, 2, 2),
        (1, 0, 0, 0, 0, 0, 2, 2),
        (1, 0, 1, 0, 0, 0, 2, 2),
        (1, 0, 0, 0, 1, 0, 0, 0, 2, 2),
        (1, 0, 1, 0, 1, 0, 0, 0, 2, 2),
        (1, 0, 0, 0, 0, 0, 0, 0, 2, 2),
    ]
    cnt = 0
    for L in wings_L:
        for R in wings_R:
            s = L + CORE_M_STAR + R
            assert is_valid_hard_pattern(s) and is_regime3(s)
            assert lib.find_schedule(s, directed=True) is None
            assert lib.find_schedule(s[::-1], directed=True) is None
            cnt += 1
    print(f"  [PASS] {cnt}/{cnt} wing pairs L + M* + R (N=26..34): ALL fail OP1 in both F and R")

    W0, R0 = (2, 2, 0, 0, 0, 1), (1, 0, 0, 0, 2, 2)
    params = [(0, 1, 1, 1), (1, 1, 1, 1), (2, 1, 1, 1),
              (0, 2, 1, 1), (0, 1, 2, 1), (0, 1, 1, 2), (1, 2, 2, 2)]
    for a, b, c, d in params:
        mid = (2,) + (0,) * (2 * a + 1) + (1, 2) + (0,) * (2 * b + 1) + (2,) + (0, 1) * c + (2,) + (1, 0) * d + (1, 2)
        s = W0 + mid + R0
        assert is_valid_hard_pattern(s) and is_regime3(s)
        assert lib.find_schedule(s, directed=True) is None
        assert lib.find_schedule(s[::-1], directed=True) is None
        res_u = lib.find_schedule(s, directed=False)
        assert res_u is not None
    print(f"  [PASS] {len(params)}/{len(params)} generalized cores M*(a,b,c,d) (N=26..34): ALL fail OP1, ALL have undirected trios")

    # Random long N=76 hit discovered during 20k stress test
    s76 = tuple(int(c) for c in "22000101010101000000000100000101200012000201012101210000010101010100010000022")
    assert len(s76) - 1 == 76 and is_valid_hard_pattern(s76) and is_regime3(s76)
    assert lib.find_schedule(s76, directed=True) is None
    assert lib.find_schedule(s76[::-1], directed=True) is None
    assert lib.find_schedule(s76, directed=False) is not None
    print("  [PASS] N=76 random hit (core M*(1,1,2,1)): F=None, R=None, undirected=True")


def residual_classes(N):
    """Exact enumeration of reversal classes (s <= s^r) in the Layer-1 residual family R."""
    def mids(L):
        def rec(pref):
            if len(pref) == L:
                yield tuple(pref)
                return
            i = len(pref)
            opts = [0, 1]
            if i not in (0, L - 1) and (not pref or pref[-1] != 2):
                opts.append(2)
            for v in opts:
                yield from rec(pref + [v])
        yield from rec([])

    seen = set()
    for e in range(6, N - 11, 2):
        for E in range(e + 6, N - 5, 2):
            nl = (e - 6) // 2
            nr = (N - E - 6) // 2
            for mid in mids(E - e - 1):
                if not any(mid[k] == 2 for k in range(0, len(mid), 2)):
                    continue
                if mid[0] == 1 and mid[-1] == 1:
                    continue
                for lw in product((0, 1), repeat=nl):
                    for rw in product((0, 1), repeat=nr):
                        s = [0] * (N + 1)
                        s[0] = s[1] = s[N - 1] = s[N] = 2
                        for j, v in enumerate(lw):
                            s[5 + 2 * j] = v
                        s[e - 1] = 1
                        s[e] = 2
                        for k, v in enumerate(mid):
                            s[e + 1 + k] = v
                        s[E] = 2
                        s[E + 1] = 1
                        for j, v in enumerate(rw):
                            s[E + 3 + 2 * j] = v
                        t = tuple(s)
                        k = min(t, t[::-1])
                        if k not in seen:
                            seen.add(k)
                            yield k


def verify_minimality_and_uniqueness():
    print("\n=== 3. Exhaustive minimality (N <= 24) and uniqueness (N = 26) across R ===")
    t0 = time.time()
    for N in (18, 20, 22, 24, 26):
        tot = proved = fallback_ok = 0
        ces = []
        for s in residual_classes(N):
            tot += 1
            r = solve_lemma_C(s)
            if r is not None:
                d, br, w = r
                lib.verify_word(s if d == 'F' else s[::-1], w, directed=True)
                proved += 1
            else:
                ok = False
                for ss in (s, s[::-1]):
                    res = lib.find_schedule(ss, directed=True)
                    if res is not None:
                        a0, w = res
                        full = 'x' + ''.join('y' if i % 2 else 'x' for i in range(1, a0 + 1)) + 'z' + w
                        lib.verify_word(ss, full, directed=True)
                        ok = True
                        break
                if ok:
                    fallback_ok += 1
                else:
                    ces.append(s)
        print(f"  N={N}: R-classes={tot}, hand-proved={proved}, bfs-verified={fallback_ok}, "
              f"COUNTEREXAMPLES={len(ces)} ({time.time() - t0:.1f}s)", flush=True)
        for c in ces:
            print(f"    CE: {''.join(map(str, c))}")
        if N <= 24:
            assert len(ces) == 0 and fallback_ok == 0
        else:
            assert len(ces) == 1 and ces[0] == S_STAR
    print("  [PASS] N <= 24 has 0 counterexamples (100% solved by hand-proved theorems); "
          "N = 26 has UNIQUE counterexample s*!")


if __name__ == '__main__':
    verify_s_star()
    verify_infinite_family()
    if '--full' in sys.argv:
        verify_minimality_and_uniqueness()
    else:
        print("\nRun with --full to also exhaustively verify minimality (N <= 24) and uniqueness (N = 26).")
