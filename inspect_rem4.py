import random
from itertools import product
import op1_lib as lib
from prove_lemma_B_v2 import solve_lemma_B_dir

def get_e_E(pat):
    ev2 = [i for i in range(2, len(pat) - 1, 2) if pat[i] == 2]
    return ev2[0], ev2[-1]

L1 = (1, 2, 0, 2, 0, 1, 0, 0)
for R in product((0, 1), repeat=6):
    s = (2, 2) + L1 + (2, 0, 2) + R[::-1] + (2, 2)
    if not (solve_lemma_B_dir(s) or solve_lemma_B_dir(s[::-1])):
        print('PB fail R:', R)
        res_s = lib.find_schedule(s, directed=True)
        res_sr = lib.find_schedule(s[::-1], directed=True)
        print('  BFS s:', res_s is not None, 'BFS sr:', res_sr is not None)
        use_s = s if res_s else s[::-1]
        a0, use_w = res_s or res_sr
        t = (a0, 1, 1, 7)
        tr = [t]
        for ch in use_w:
            t = lib.step(use_s, t, ch, directed=True)
            tr.append(t)
        print('  a0:', a0, 'e,E:', get_e_E(use_s), 'len:', len(use_s) - 1)
        print('  trace:', [x for i, x in enumerate(tr) if x[0] == x[1] or i == len(tr) - 1])

rng = random.Random(77777777)
for idx in range(5000):
    def rw():
        k = 2 * rng.randint(1, 32)
        return tuple((rng.randint(0, 1) if i % 2 == 0 else (0 if i == k - 1 else rng.choice([0, 1, 2]))) for i in range(k))
    L = rw()
    R = rw()
    if 2 not in L and 2 not in R:
        if len(L) >= 2:
            L = (L[0], 2) + L[2:]
        else:
            continue
    mlen = rng.choice(list(range(1, 16, 2)))
    mid = [2]
    for i in range(1, mlen - 1):
        allow2 = (mid[-1] != 2) and (i < mlen - 2)
        mid.append(rng.choice([0, 1, 2] if allow2 else [0, 1]))
    if mlen > 1:
        mid.append(2)
    s = (2, 2) + L + tuple(mid) + R[::-1] + (2, 2)
    if not (solve_lemma_B_dir(s) or solve_lemma_B_dir(s[::-1])):
        print('RAND7 fail idx:', idx, 'mid:', mid, 'e,E of s:', get_e_E(s), 'e,E of sr:', get_e_E(s[::-1]))
        for label, pat in [('s', s), ('sr', s[::-1])]:
            e, E = get_e_E(pat)
            N = len(pat) - 1
            od2L = [i for i in range(3, e, 2) if pat[i] == 2]
            od2R = [i for i in range(E + 1, N - 1, 2) if pat[i] == 2]
            evL = [i for i in range(2, e, 2) if pat[i] == 1]
            evR = [i for i in range(E + 2, N, 2) if pat[i] == 1]
            print(f'  [{label}] e={e} E={E} N={N} od2L={od2L[:3]}..{od2L[-3:]} evL_last={evL[-3:]} odL_af_P={[i for i in range(od2L[-1]+2 if od2L else 1, e, 2) if pat[i]==1]}')
            print(f'       od2R={od2R[:3]}..{od2R[-3:]} evR_first={evR[:3]} odR_before_O1={[i for i in range(E+1, od2R[0] if od2R else N-1, 2) if pat[i]==1]}')
