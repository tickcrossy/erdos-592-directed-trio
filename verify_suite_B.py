import sys
import random
from itertools import product
import op1_lib as lib
from prove_lemma_B_v2 import solve_lemma_B_dir

def strip_wing(W):
    ev1 = [i for i in range(0, len(W), 2) if W[i] == 1]
    i_ev = ev1[0] if ev1 else len(W)
    od2 = [j for j in range(1, i_ev, 2) if W[j] == 2]
    j_pk = od2[-1] if od2 else -1
    return W[j_pk + 1:]

def gen_core_wings(k):
    for w in product((0, 1, 2), repeat=k):
        if any(w[i] == 2 for i in range(0, k, 2)):
            continue
        if k > 0 and w[-1] == 2:
            continue
        if strip_wing(w) == w:
            yield w

def gen_any_wings(k):
    for w in product((0, 1, 2), repeat=k):
        if any(w[i] == 2 for i in range(0, k, 2)):
            continue
        if k > 0 and w[-1] == 2:
            continue
        if 2 in w:
            yield w

def check_one(s):
    w = solve_lemma_B_dir(s)
    if w is not None:
        lib.verify_word(s, w, directed=True)
        return True
    sr = s[::-1]
    wr = solve_lemma_B_dir(sr)
    if wr is not None:
        lib.verify_word(sr, wr, directed=True)
        return True
    return False

mode = sys.argv[1]

if mode == 'core_PB':
    for mid in [(2,), (2, 0, 2), (2, 1, 2), (2, 0, 2, 0, 2)]:
        for kL, kR in [(6, 6), (6, 8), (8, 6)]:
            tot = cov = 0
            fails = 0
            first_fail = None
            for L in gen_core_wings(kL):
                if 2 not in L:
                    continue
                for R in gen_core_wings(kR):
                    if 2 in R:
                        continue
                    s = (2, 2) + L + mid + R[::-1] + (2, 2)
                    tot += 1
                    if check_one(s):
                        cov += 1
                    else:
                        fails += 1
                        if first_fail is None:
                            first_fail = (L, mid, R)
            print(f'PB mid={mid} ({kL},{kR}): {cov}/{tot} (fails={fails}) first={first_fail}')

elif mode == 'core_PP':
    for mid in [(2,), (2, 0, 2), (2, 1, 2), (2, 0, 2, 0, 2)]:
        for kL, kR in [(4, 4), (4, 6), (6, 6), (6, 8)]:
            tot = cov = 0
            fails = 0
            first_fail = None
            for L in gen_core_wings(kL):
                if 2 not in L:
                    continue
                for R in gen_core_wings(kR):
                    if 2 not in R:
                        continue
                    if kL == kR and L > R:
                        continue
                    s = (2, 2) + L + mid + R[::-1] + (2, 2)
                    tot += 1
                    if check_one(s):
                        cov += 1
                    else:
                        fails += 1
                        if first_fail is None:
                            first_fail = (L, mid, R)
            print(f'PP mid={mid} ({kL},{kR}): {cov}/{tot} (fails={fails}) first={first_fail}')

elif mode == 'sym':
    for mid in [(2,), (2, 0, 2), (2, 1, 2), (2, 0, 1, 0, 2)]:
        for k in [4, 6, 8, 10]:
            tot = cov = 0
            fails = 0
            first_fail = None
            for W in gen_any_wings(k):
                s = (2, 2) + W + mid + W[::-1] + (2, 2)
                tot += 1
                if check_one(s):
                    cov += 1
                else:
                    fails += 1
                    if first_fail is None:
                        first_fail = (W, mid)
            print(f'SYM mid={mid} k={k}: {cov}/{tot} (fails={fails}) first={first_fail}')

elif mode == 'rand':
    for seed, max_half, max_mlen, count in [
        (20261125, 18, 9, 5000),
        (99999991, 30, 11, 5000),
        (77777777, 32, 15, 5000),
        (20261126, 40, 25, 10000),
    ]:
        rng = random.Random(seed)
        fails = 0
        first_fail = None
        for idx in range(count):
            def rand_wing():
                k = 2 * rng.randint(1, max_half)
                w = []
                for i in range(k):
                    if i % 2 == 0:
                        w.append(rng.randint(0, 1))
                    else:
                        w.append(0 if i == k - 1 else rng.choice([0, 1, 2]))
                return tuple(w)
            L = rand_wing()
            R = rand_wing()
            if 2 not in L and 2 not in R:
                if len(L) >= 2:
                    L = (L[0], 2) + L[2:]
                else:
                    continue
            mlen = rng.choice(list(range(1, max_mlen + 1, 2)))
            mid = [2]
            for i in range(1, mlen - 1):
                allow2 = (mid[-1] != 2) and (i < mlen - 2)
                mid.append(rng.choice([0, 1, 2] if allow2 else [0, 1]))
            if mlen > 1:
                mid.append(2)
            s = (2, 2) + L + tuple(mid) + R[::-1] + (2, 2)
            if not check_one(s):
                fails += 1
                if first_fail is None:
                    first_fail = (idx, len(L), len(mid), len(R), L, tuple(mid), R)
        print(f'RAND seed={seed} count={count}: {count - fails}/{count} (fails={fails}) first_idx={first_fail[0] if first_fail else None}')
        if first_fail:
            print('  detail:', first_fail[:4], 'mid=', first_fail[5])
            print('  L=', first_fail[4])
            print('  R=', first_fail[6])
