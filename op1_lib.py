from collections import deque

RULE = {'x': ((0, 0), (1, 0)), 'y': ((0, 1), (2, 0)), 'z': ((1, 1), (2, 1))}

def step(s, t, l, directed=True, common=None):
    p = list(t[:3]); m = t[3]; rule = RULE[l]
    for j, par in rule:
        if p[j] % 2 != par:
            if not (m >> j & 1):
                return None
            p[j] += 1
            if p[j] >= len(s):
                return None
            m &= ~(1 << j)
    j, k = rule[0][0], rule[1][0]
    w = min(s[p[j]], s[p[k]])
    for q in (j, k):
        ok = (w == s[p[q]])
        if directed and q == 2 and p[q] % 2 == 0 and s[p[q]] == 2 and 0 < p[q] < len(s) - 1:
            ok = ok and l == 'y' and p[0] > p[2] and (common is None or p[0] == common)
        if ok:
            m |= 1 << q
    return (*p, m)

def verify_word(s, w, directed=True, common=None):
    pos = [-1, -1, -1]
    weights = []
    rows = []
    for l in w:
        for j, par in RULE[l]:
            if pos[j] < 0:
                pos[j] = 0
            elif pos[j] % 2 != par:
                pos[j] += 1
            assert pos[j] < len(s), f"Out of bounds: {pos}"
        j, k = RULE[l][0][0], RULE[l][1][0]
        wt = min(s[pos[j]], s[pos[k]])
        weights.append(wt)
        rows.append(tuple(pos))
    for j, chars in enumerate(('xy', 'xz', 'yz')):
        out = []
        last = None
        for l, wt in zip(w, weights):
            if l not in chars:
                continue
            if l != last:
                out.append(wt)
                last = l
            else:
                out[-1] = max(out[-1], wt)
        assert out == list(s), (j, out, list(s))
    for l in 'xyz':
        a = [wt for c, wt in zip(w, weights) if c == l]
        assert a[0] == 2 and a[-1] == 2, (l, a[0], a[-1])
    if directed:
        for i in range(2, len(s) - 2, 2):
            if s[i] == 2:
                ok = any(
                    l == 'y' and p[2] == i and p[0] > i and s[p[0]] == 2 and wt == 2
                    and (common is None or p[0] == common)
                    for l, wt, p in zip(w, weights, rows)
                )
                assert ok, f"Missing designated witness for {i} in {s}"

class Sched:
    def __init__(self, s, a, directed=True):
        assert a >= 1
        self.s = s
        self.directed = directed
        self.t = (a, 1, 1, 7)
        self.word = 'x' + ''.join('y' if i % 2 else 'x' for i in range(1, a + 1)) + 'z'
    def emit(self, l):
        t = step(self.s, self.t, l, directed=self.directed)
        assert t is not None, (self.s, self.t, l, self.word)
        self.t = t
        self.word += l
    def go(self, j, q):
        while self.t[j] < q:
            target = (self.t[j] + 1) % 2
            l = next(l for l, rs in RULE.items() if (j, target) in rs)
            self.emit(l)

def M_ev(s, a, b):
    vals = [s[i] for i in range(a + 1, b) if i % 2 == 0]
    return max(vals) if vals else 0

def M_od(s, a, b):
    vals = [s[i] for i in range(a + 1, b) if i % 2 == 1]
    return max(vals) if vals else 0

def hard_patterns(N):
    def rec(pref):
        if len(pref) == N - 1:
            if 2 in pref[2::2]:
                yield tuple(pref + [2, 2])
            return
        allow2 = pref[-1] != 2 and len(pref) != N - 2
        for w in range(3 if allow2 else 2):
            yield from rec(pref + [w])
    yield from rec([2, 2])

def find_schedule(s, directed=True, common=None):
    N = len(s) - 1
    starts = [(a, 1, 1, 7) for a in range(1, N)]
    seen = {t: None for t in starts}
    q = deque(starts)
    while q:
        t = q.popleft()
        if t == (N, N, N, 7):
            path = []
            u = t
            while seen[u] is not None:
                v, l = seen[u]
                path.append(l)
                u = v
            return u[0], ''.join(path[::-1])
        for l in 'xyz':
            u = step(s, t, l, directed=directed, common=common)
            if u is not None and u not in seen:
                seen[u] = (t, l)
                q.append(u)
    return None

def trace_phases(s, a0, word, directed=True):
    t = (a0, 1, 1, 7)
    out = [f"I({a0}) -> {t[:3]}"]
    cur_tok = None
    for l in word:
        u = step(s, t, l, directed=directed)
        moved = [j for j in range(3) if u[j] != t[j]]
        out.append(f"  {l}: {t[:3]}({t[3]}) -> {u[:3]}({u[3]})")
        t = u
    return '\n'.join(out)
