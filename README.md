# Directed Trio Schedules for Erdős Problem #592 (Open Problem 1)

Closed-form constructive solvers, exact structural decompositions, and independent counterexample verification for **Open Problem 1 (OP1)** in the three-cursor scheduling framework associated with Erdős Problem #592.

## Main Results

Let $s = (s_0, s_1, \dots, s_N) \in \{0, 1, 2\}^{N+1}$ ($N$ even) be a **hard pattern**: $s_0 = s_1 = s_{N-1} = s_N = 2$, no two adjacent entries in $(1, N-1)$ are both $2$, and at least one internal even index has value $2$. Let $e \le E$ be the first and last internal even peaks, with left wing $W_L = (1, e)$ and right wing $W_R = (E, N-1)$.

A **directed OP1 schedule** for $s$ is a word $W \in \{x, y, z\}^*$ whose three cursor projections (`xy` for $A$, `xz` for $B$, `yz` for $C$) each realize $s$ under `min`-weights, with first and last occurrences of each letter having weight $2$, and such that every internal even peak $i$ visited by $C$ is witnessed by a weight-$2$ `y`-event with $A > i$. **OP1** asks whether every hard pattern $s$ admits a directed OP1 schedule in at least one of its two orientations $s$ or $s^r$.

1. **Refutation of OP1 for all even $N \ge 26$.**
   OP1 is **false** in general. For every even $N \ge 26$, there is an exponential family of counterexamples (at least $(m+1)2^m$ ordered patterns, where $m = (N - 26)/2$) obtained by placing the fixed $15$-entry middle core
   $$M^* = (2, 0, 1, 2, 0, 0, 0, 2, 0, 1, 2, 1, 0, 1, 2)$$
   between arbitrary Regime-III residual wings $W_L$ ($e \ge 6$, $s_3 = 0$, $s_{e-1} = 1$) and $W_R$ ($e' \ge 6$, $s_{E+1} = 1$, $s_{N-3} = 0$). Neither $s$ nor $s^r$ admits a directed OP1 schedule. A four-parameter generalization $M^*(a, b, c, d)$ ($a \ge 0$, $b, c, d \ge 1$) also fails OP1 in both orientations.

2. **Unique minimal counterexample at $N = 26$ (length $27$).**
   - Every hard pattern with even $N \le 24$ (length $\le 25$) satisfies OP1 ($0$ counterexamples).
   - At $N = 26$ (length $27$), there is a **unique** counterexample up to reversal:
     ```text
     s* = 220001201200020121012100022
     ```
   - `s*` still admits a valid **undirected trio** (`directed=False`, length $57$), strictly separating three natural scheduling properties:
     $$\text{OP2 (common witness, fails at } N=18\text{)} \;\subsetneq\; \text{OP1 (directed witness, fails at } N=26\text{)} \;\subsetneq\; \text{Undirected Trio (open)}.$$

3. **Exact structural boundary across the three wing regimes.**
   Partitioning all hard patterns by their wings $W_L, W_R$:
   - **Regime I** ($\max(M_{\mathrm{od}}(W_L), M_{\mathrm{od}}(W_R)) = 2$): **TRUE for all $N$** (closed-form constructive solver in `prove_lemma_B_v2.py`).
   - **Regime II** (not I, and $\max(M_{\mathrm{ev}}(W_L), M_{\mathrm{ev}}(W_R)) = 1$): **TRUE for all $N$** (closed-form constructive solver in `prove_lemma_A_closed_form.py`).
   - **Regime III** (both wings have even entries $0$ and odd entries $\le 1$):
     - **Layer 1 ($\text{Regime III} \setminus \mathcal{R}$)**: **TRUE for all $N$** via $6$ length-independent closed-form theorems (`layer1_dir` in `prove_lemma_C_closed_form.py`).
     - **Residual family $\mathcal{R}$**: **TRUE for all $N$** when there is a single internal odd peak and no additional internal even peaks ($|\mathcal{E}(s)| = 2$, $|\mathcal{O}(s)| = 1$); **FALSE for all even $N \ge 26$** in the multi-peak regime ($|\mathcal{E}(s)| \ge 3$, $|\mathcal{O}(s)| \ge 2$).

## Repository Structure

| File | Description |
|---|---|
| `op1_lib.py` | Reference three-cursor automaton (`step`, `verify_word`, `Sched`, `hard_patterns`, `find_schedule`). |
| `op1.cpp` | Standalone C++ reference search & verifier. |
| `prove_binary_suffix_complete.py` | Closed-form inductive solver for binary odd-peak suffixes (Theorem S). |
| `prove_lemma_A_closed_form.py` | Closed-form solver for **Regime II** (Lemma A). |
| `prove_lemma_B_v2.py` | Closed-form solver for **Regime I** (Lemma B). |
| `prove_lemma_C_closed_form.py` | Closed-form solver for **Regime III** (Layer 1 + $15$ hand-proved Layer-2 theorems on $\mathcal{R}$). |
| `solve_op1_complete.py` | Unified Regime I/II/III closed-form dispatcher (no search/BFS; every output verified by `op1_lib.verify_word`). |
| `verify_op1_counterexample.py` | Independent verification of `s*` (via `op1_lib`, unrestricted full-word automaton BFS without $I(a)$, and `op1.cpp`), undirected trio check, infinite family tests, and exhaustive minimality/uniqueness check for $\mathcal{R}$ ($N \le 26$). |
| `verify_op1_complete.py` | Exhaustive hard-pattern and random long-pattern verification suite across all regimes. |
| `verify_suite_B.py` | Dedicated verification suite for Regime I (Lemma B). |
| `archive/` | Earlier exploratory scripts preserved for reference. |

> **Zero-search guarantee for all solvers:** Static AST auditing confirms that `prove_lemma_A_closed_form.py`, `prove_lemma_B_v2.py`, `prove_lemma_C_closed_form.py`, and `solve_op1_complete.py` contain zero calls to `find_schedule`, `deque`, or BFS. Search is used exclusively inside independent verification/refutation scripts (`verify_op1_counterexample.py`, `op1.cpp`).

## Quick Start & Reproducibility

Requires Python 3.10+ (standard library only; `g++` optional for cross-checking `op1.cpp`).

### 1. Verify the counterexample `s*` and infinite family (~2 seconds)
```bash
python3 verify_op1_counterexample.py
```

### 2. Full minimality ($N \le 24$) and uniqueness ($N = 26$) check across $\mathcal{R}$ (~70 seconds)
```bash
python3 verify_op1_counterexample.py --full
```
Expected summary:
- `N = 18`: `7/7` hand-proved, `0` counterexamples
- `N = 20`: `110/110` hand-proved, `0` counterexamples
- `N = 22`: `1286/1286` hand-proved, `0` counterexamples
- `N = 24`: `12560/12560` hand-proved, `0` counterexamples
- `N = 26`: `112464` classes (`112430` hand-proved + `33` BFS-verified positive + `1` unique counterexample `s*`)

### 3. Exhaustive & random long-pattern verification across all regimes
```bash
# Exhaustive over all hard patterns for N = 8..16 (0 failures)
python3 verify_op1_complete.py exh 8 16

# 10,000 random long hard patterns (N up to ~164) across Regimes I, II, III
python3 verify_op1_complete.py rand 1 10000

# Dedicated Regime I (Lemma B) suite
python3 verify_suite_B.py
```

## Open Questions for Future Work

1. **Undirected trios (`directed=False`):** Does every hard pattern of arbitrary even length admit an undirected trio? Every counterexample in our family $s(W_L, W_R)$ and $M^*(a, b, c, d)$ still admits an undirected trio.
2. **Remaining positive subfamilies of $\mathcal{R}$:** Are the single-odd-peak multi-even-peak subfamily ($|\mathcal{O}(s)| = 1$, $|\mathcal{E}(s)| \ge 3$) and the two-even-peak multi-odd-peak subfamily ($|\mathcal{E}(s)| = 2$, $|\mathcal{O}(s)| \ge 2$) of $\mathcal{R}$ true for all lengths under directed OP1? (No counterexamples were found for $N \le 26$ or in $20{,}000$ random long samples.)

## License

This project is released under the [MIT License](LICENSE).
