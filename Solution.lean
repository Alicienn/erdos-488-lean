module

public import Erdos488

@[expose] public section

/-!
# Erdős Problem 488 — Proved Solution

Supplies machine-checked proofs for every theorem declared in `Challenge.lean`, with identical
names and types and depending only on `[propext, Quot.sound, Classical.choice]`.
-/

theorem Erdos488.not_erdos_488 :
    ¬ (∀ (A : Finset ℕ), A.Nonempty →
      0 ∉ A → 1 ∉ A →
      letI B := {n ≥ 1 | ∃ a ∈ A, a ∣ n}
      ∀ᵉ (n : ℕ) (m > n), A.max ≤ n →
        ((Finset.Icc 1 m).filter (· ∈ B)).card / (m : ℚ) <
          2 * ((Finset.Icc 1 n).filter (· ∈ B)).card / n) :=
  Erdos488.not_erdos_488_proof

theorem Erdos488.erdos_488_card_le_two :
    ∀ (A : Finset ℕ), A.Nonempty → A.card ≤ 2 →
      0 ∉ A → 1 ∉ A →
      letI B := {n ≥ 1 | ∃ a ∈ A, a ∣ n}
      ∀ᵉ (n : ℕ) (m > n), A.max ≤ n →
        ((Finset.Icc 1 m).filter (· ∈ B)).card / (m : ℚ) <
          2 * ((Finset.Icc 1 n).filter (· ∈ B)).card / n :=
  Erdos488.erdos_488_card_le_two_proof
