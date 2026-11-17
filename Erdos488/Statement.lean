import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

/-!
# Erdős Problem 488 — Exact Statement (matching Google DeepMind `formal-conjectures`)

Let $A$ be a finite nonempty set of integers with $0 \notin A$ and $1 \notin A$, and let
$$B = \{n \ge 1 : \exists a \in A,\ a \mid n\}.$$
Erdős asked whether for every $m > n \ge \max(A)$,
$$\frac{|B \cap [1, m]|}{m} < 2 \frac{|B \cap [1, n]|}{n}.$$
-/

namespace Erdos488

open scoped Classical in
/-- The exact statement of Erdős Problem 488 from `FormalConjectures/ErdosProblems/488.lean`. -/
def Erdos488Prop : Prop :=
  ∀ (A : Finset ℕ), A.Nonempty →
    0 ∉ A → 1 ∉ A →
    letI B := {n ≥ 1 | ∃ a ∈ A, a ∣ n}
    ∀ᵉ (n : ℕ) (m > n), A.max ≤ n →
      ((Finset.Icc 1 m).filter (· ∈ B)).card / (m : ℚ) <
        2 * ((Finset.Icc 1 n).filter (· ∈ B)).card / n

end Erdos488
