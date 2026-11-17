module

public import Mathlib.Data.Finset.Max
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Data.Rat.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop

@[expose] public section

/-!
# Erdős Problem 488 — Advertised Challenge Statements

Let $A$ be a finite nonempty set of integers $\ge 2$ (equivalently $0 \notin A$ and $1 \notin A$),
and let
$$B = \{n \ge 1 : \exists a \in A,\ a \mid n\}$$
be its set of positive multiples. Paul Erdős ([Er61, p. 236], [Er66, p. 150],
<https://www.erdosproblems.com/488>) asked whether, for every pair of integers
$m > n \ge \max(A)$, the cumulative density satisfies
$$\frac{|B \cap [1, m]|}{m} < 2\,\frac{|B \cap [1, n]|}{n}.$$

This Challenge module states two complementary results using only standard Mathlib definitions,
matching verbatim the formulation in Google DeepMind's `FormalConjectures/ErdosProblems/488.lean`:

1. `Erdos488.not_erdos_488`: The universal inequality is **false** in general (there exist a finite
   nonempty set $A \subset \mathbb{N} \setminus \{0, 1\}$ and integers $m > n \ge \max(A)$ violating
   the factor-$2$ bound).
2. `Erdos488.erdos_488_card_le_two`: Whenever $|A| \le 2$, the strict factor-$2$ inequality holds
   **unconditionally** for all integers $m > n \ge \max(A)$.
-/

/-- **Disproof of Erdős Problem 488 (`Erdos488.not_erdos_488`):**
It is *not* true that for every finite nonempty set $A \subset \mathbb{N} \setminus \{0, 1\}$ and
every $m > n \ge \max(A)$, the proportion of multiples of $A$ in $[1, m]$ is strictly less than
twice the proportion of multiples of $A$ in $[1, n]$. -/
theorem Erdos488.not_erdos_488 :
    ¬ (∀ (A : Finset ℕ), A.Nonempty →
      0 ∉ A → 1 ∉ A →
      letI B := {n ≥ 1 | ∃ a ∈ A, a ∣ n}
      ∀ᵉ (n : ℕ) (m > n), A.max ≤ n →
        ((Finset.Icc 1 m).filter (· ∈ B)).card / (m : ℚ) <
          2 * ((Finset.Icc 1 n).filter (· ∈ B)).card / n) := by
  sorry

/-- **Positive Resolution for $|A| \le 2$ (`Erdos488.erdos_488_card_le_two`):**
For every finite nonempty set $A \subset \mathbb{N} \setminus \{0, 1\}$ with $|A| \le 2$ and every
pair of integers $m > n \ge \max(A)$, the strict factor-$2$ density inequality holds. -/
theorem Erdos488.erdos_488_card_le_two :
    ∀ (A : Finset ℕ), A.Nonempty → A.card ≤ 2 →
      0 ∉ A → 1 ∉ A →
      letI B := {n ≥ 1 | ∃ a ∈ A, a ∣ n}
      ∀ᵉ (n : ℕ) (m > n), A.max ≤ n →
        ((Finset.Icc 1 m).filter (· ∈ B)).card / (m : ℚ) <
          2 * ((Finset.Icc 1 n).filter (· ∈ B)).card / n := by
  sorry
