/-
Copyright 2025 The Formal Conjectures Authors.
Adapted from `FormalConjectures/ErdosProblems/488.lean` in
`google-deepmind/formal-conjectures` under the Apache License, Version 2.0.
-/
module

public import Mathlib.Data.Finset.Max
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Data.Rat.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop

@[expose] public section

/-!
# Erdős Problem 488 — Exact Statement (matching Google DeepMind `formal-conjectures`)

Let $A$ be a finite nonempty set of integers with $0 \notin A$ and $1 \notin A$, and let
$$B = \{n \ge 1 : \exists a \in A,\ a \mid n\}.$$
Erdős asked whether for every $m > n \ge \max(A)$,
$$\frac{|B \cap [1, m]|}{m} < 2 \frac{|B \cap [1, n]|}{n}.$$
-/

namespace Erdos488

/-- The exact statement of Erdős Problem 488 from `FormalConjectures/ErdosProblems/488.lean`. -/
def Erdos488Prop : Prop :=
  ∀ (A : Finset ℕ), A.Nonempty →
    0 ∉ A → 1 ∉ A →
    letI B := {n ≥ 1 | ∃ a ∈ A, a ∣ n}
    ∀ᵉ (n : ℕ) (m > n), A.max ≤ n →
      ((Finset.Icc 1 m).filter (· ∈ B)).card / (m : ℚ) <
        2 * ((Finset.Icc 1 n).filter (· ∈ B)).card / n

end Erdos488
