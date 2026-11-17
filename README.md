# Erdős Problem #488 — Complete Lean 4 Formal Resolution

[![Lean Action CI](https://github.com/Alicienn/erdos-488-lean/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/Alicienn/erdos-488-lean/actions/workflows/lean_action_ci.yml)
![Lean 4](https://img.shields.io/badge/Lean_4-v4.33.1-blue)
![Mathlib](https://img.shields.io/badge/Mathlib-v4.33.1-informational)
![Sorry-Free](https://img.shields.io/badge/sorry-0-brightgreen)

This repository provides a complete, **`sorry`-free, axiom-audited Lean 4 formalization** resolving **Erdős Problem #488** (posed by Paul Erdős in 1961), matching the exact formal statement in Google DeepMind's [`formal-conjectures`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/488.lean) repository.

We formalize **both sides** of the phenomenon:
1. **General Disproof (`Erdos488.not_erdos_488`):** Erdős's universal factor-$2$ inequality is **false** in general. Using a purely discrete finite-telescoping construction over $256$-smooth integers (requiring **zero** real logarithms, simplex volume integrals, or analytic Mertens estimates), we exhibit an explicit finite witness $(A, n, m)$ with $|B \cap [1, m]| / m > 2 |B \cap [1, n]| / n$.
2. **Small-Cardinality Theorem (`Erdos488.erdos_488_card_le_two`):** Conversely, whenever $|A| \le 2$, Erdős's inequality holds **unconditionally** for all $m > n \ge \max(A)$.

---

## 1. Problem Statement

Let $A \subset \mathbb{Z}_{\ge 2}$ be a finite non-empty set of integers, and let
$$B = \{k \ge 1 : \exists a \in A,\ a \mid k\}$$
be its set of multiples. Erdős ([Er61, p. 241], [erdosproblems.com/488](https://www.erdosproblems.com/488)) asked whether for all integers $m > n \ge \max(A)$,
$$\frac{|B \cap [1, m]|}{m} < 2\,\frac{|B \cap [1, n]|}{n}.$$

In [`Erdos488/Statement.lean`](Erdos488/Statement.lean), we reproduce verbatim the statement from `FormalConjectures/ErdosProblems/488.lean`:

```lean
def Erdos488Prop : Prop :=
  ∀ (A : Finset ℕ), A.Nonempty →
    0 ∉ A → 1 ∉ A →
    letI B := {n ≥ 1 | ∃ a ∈ A, a ∣ n}
    ∀ᵉ (n : ℕ) (m > n), A.max ≤ n →
      ((Finset.Icc 1 m).filter (· ∈ B)).card / (m : ℚ) <
        2 * ((Finset.Icc 1 n).filter (· ∈ B)).card / n
```

---

## 2. Main Formalized Results

| Declaration | File | Statement | Axioms |
| :--- | :--- | :--- | :--- |
| `Erdos488.not_erdos_488` | [`Erdos488/Disproof.lean`](Erdos488/Disproof.lean) | `¬ Erdos488Prop` | `[propext, Classical.choice, Quot.sound]` |
| `Erdos488.erdos_488_card_le_two` | [`Erdos488/CardLeTwo.lean`](Erdos488/CardLeTwo.lean) | `Erdos488Prop` restricted to `A.card ≤ 2` | `[propext, Classical.choice, Quot.sound]` |

---

## 3. Mathematical Overview of the Discrete Lean 4 Proof

### 3.1. Purely Combinatorial Disproof (`Erdos488/Disproof.lean`)
An informal smooth-number refutation at smoothness scale $H = 2^{16} = 65536$ was recently reported in Zhang et al. ([arXiv:2610.02945](https://arxiv.org/abs/2610.02945), Oct 2026) using continuous simplex volume bounds over $\log_2 p_i$ and analytic Mertens estimates. Here we compress the smoothness threshold down to **$H = 256 = 2^8$** ($53$ odd primes) and eliminate all real analysis:

1. **Box Bound via Prime Factorization (`oddSmooth_pow_two_le`):** Let $O(y)$ denote the set of odd $256$-smooth integers in $[1, y]$. Injecting $w \in O(2^T)$ into exponent tuples `Fin 53 → Fin (T + 1)` via `Nat.factorization` yields $|O(2^T)| \le (T + 1)^{53}$.
2. **Finite Pigeonhole Telescoping (`exists_good_scale`):** Since $5^{3500} \cdot 28009^{53} < 6^{3500}$ (`norm_num`), the inequality $5\,|O(2^{8(j+1)})| > 6\,|O(2^{8j})|$ cannot hold for every $j \in \{1, \dots, 3500\}$. Hence there exists $j \in [1, 3500]$ with $x = 2^{8j} \ge 256$ satisfying
   $$5\,|O(256 x)| \le 6\,|O(x)|.$$
3. **Sparse Window at $n = 256 x$ (`upper_bound_at_n`):** Define $A = \{a \in [x, 2x) : a \text{ is } 256\text{-smooth}\}$. If $t \in [1, 256 x]$ is divisible by $a \in A$ ($t = aq$), then $1 \le q \le 256$, so every prime factor of $q$ is automatically $\le 256$. Hence $t$ itself is $256$-smooth in $[x, 256 x]$. Writing $t = 2^e w$ with $w \in O(n)$ admits at most $9$ exponents $e$ per odd core $w$ (as $2^9 = 512 > 256$), giving $|B \cap [1, n]| \le 9\,|O(n)|$, whence $5\,|B \cap [1, n]| \le 54\,|O(x)|$.
4. **Exact Totient Unfolding at $m = (2n)!\cdot Q$ (`lower_bound_at_m`):** Let $Q = \prod_{p \text{ odd} \le 256} p$. For each $w \in O(x)$, its unique dyadic lift $a_w = 2^{e(w)} w \in [x, 2x)$ lies in $A$ and satisfies $a_w < 2n$, so $a_w \mid (2n)!$ (`Nat.dvd_factorial`) and $a_w Q \mid m$. The fibers
   $$T_w = \{a_w u : 1 \le u \le m / a_w,\ \gcd(u, Q) = 1\} \subseteq B \cap [1, m]$$
   are pairwise disjoint across $w \in O(x)$ and each has exact cardinality $\frac{m}{a_w Q}\varphi(Q) > \frac{m\,\varphi(Q)}{2x Q}$.
5. **Exact Arithmetic Contradiction:** Evaluating $216\,Q < 1280\,\varphi(Q)$ (`decide`) combines the two bounds into $2\,|B \cap [1, n]|\,m < |B \cap [1, m]|\,n$.

### 3.2. Why Small Searches Never See Counterexamples (`Erdos488/CardLeTwo.lean` & `scripts/`)
At small cardinalities, adding generators *rigidifies* the density rather than destabilizing it:
- For $|A| = 1$, $\sup_{m > n \ge M} R(\{M\}, n, m) = 2 - \frac{1}{M}$ (attained at $n = 2M-1, m = 2M$).
- For $|A| = 2$ ($M \ge 4$), we prove $R(A, n, m) < 2$ formally in Lean 4 via strong induction on $n$ with period $\operatorname{lcm}(a, b)$. Computationally (`scripts/verify_extremal_small_card.py`), the exact maximum over primitive pairs with $\max(A) = M \ge 4$ is strictly smaller:
  $$R_{\max}^{(2)}(M) = \frac{(2M - 3)^2}{2(M - 1)^2} = 2 - \frac{2}{M} + O(M^{-2}),$$
  attained at $A = \{M-1, M\}$, $n = 2M-3$, $m = (M-1)^2$ (just prior to the first LCM collision $M(M-1)$).
- For $|A| = 3$ ($M \ge 9$), the extremal triple $\{M-2, M-1, M\}$ splits by parity of $M$: $m^* = (M-2)^2$ for odd $M$ ($R = 2 - \frac{3}{M} + O(M^{-2})$) and $m^* = (M-2)^2 / 2$ for even $M$ ($R = 2 - \frac{11}{3M} + O(M^{-2})$).

---

## 4. Building & Verifying Locally

Make sure [`elan`](https://github.com/leanprover/elan) is installed, then run:

```bash
git clone https://github.com/Alicienn/erdos-488-lean.git
cd erdos-488-lean
lake exe cache get
lake build
lake env lean CheckAxioms.lean
LEAN_NUM_THREADS=1 lake env leanchecker Erdos488
```

---

## 5. References & Attribution

- **[Er61]** P. Erdős, *Some unsolved problems*, Magyar Tud. Akad. Mat. Kutató Int. Közl. **6** (1961), 221–254.
- **[Bloom]** T. F. Bloom, *Erdős Problem #488*, [erdosproblems.com/488](https://www.erdosproblems.com/488) & [`teorth/erdosproblems`](https://github.com/teorth/erdosproblems).
- **[DeepMind]** The Formal Conjectures Authors, [`FormalConjectures/ErdosProblems/488.lean`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/488.lean) (Apache-2.0).
- **[Zhang+26]** Y. Zhang et al., *Continual Graph Memory for Mathematical Research Agents*, [arXiv:2610.02945](https://arxiv.org/abs/2610.02945) (Oct 2026) — prior informal smooth-number counterexample construction at $H = 2^{16}$.

### AI Assistance Disclosure
In accordance with community guidelines on [`teorth/erdosproblems`](https://github.com/teorth/erdosproblems/blob/main/CONTRIBUTING.md), we disclose that the C/Python computational exploration, the discrete $H = 256$ finite-telescoping proof simplification, and the Lean 4 (`v4.33.1`) formalizations in this repository were developed using **Google Antigravity**. All mathematical claims in `Erdos488` are machine-checked without `sorry` by the Lean 4 kernel (`leanchecker` and `axiom-audit` enforced in CI).
