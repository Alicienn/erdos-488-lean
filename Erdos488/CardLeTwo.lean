import Erdos488.Statement

/-!
# Positive Resolution of Erdős Problem 488 for $|A| \le 2$

We prove unconditionally that Erdős's inequality holds whenever $|A| \le 2$.
-/

namespace Erdos488

open scoped Classical

/-- Counting function $|B \cap [1, x]|$ as a `Finset` cardinality. -/
noncomputable def countMultiples (A : Finset ℕ) (x : ℕ) : ℕ :=
  ((Finset.Icc 1 x).filter (fun k => k ≥ 1 ∧ ∃ a ∈ A, a ∣ k)).card

lemma countMultiples_eq_filter_Set (A : Finset ℕ) (x : ℕ) :
    letI B := {n ≥ 1 | ∃ a ∈ A, a ∣ n}
    ((Finset.Icc 1 x).filter (· ∈ B)).card = countMultiples A x := by
  rfl

/-- Exact cardinality of multiples of `a > 0` in `[1, x]`. -/
lemma card_multiples_single {a : ℕ} (ha : 0 < a) (x : ℕ) :
    ((Finset.Icc 1 x).filter (fun k => a ∣ k)).card = x / a := by
  symm
  have hcard : (Finset.Icc 1 (x / a)).card = x / a := by simp
  rw [← hcard]
  apply Finset.card_bij (fun q _ => q * a)
  · intro q hq
    rw [Finset.mem_Icc] at hq
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, dvd_mul_left a q⟩
    · calc 1 ≤ q * 1 := by omega
        _ ≤ q * a := Nat.mul_le_mul_left q ha
    · calc q * a ≤ (x / a) * a := Nat.mul_le_mul_right a hq.2
        _ ≤ x := Nat.div_mul_le_self x a
  · intro q₁ _ q₂ _ h
    exact Nat.eq_of_mul_eq_mul_right ha h
  · intro k hk
    rw [Finset.mem_filter, Finset.mem_Icc] at hk
    rcases hk with ⟨⟨hk1, hkx⟩, ⟨q, rfl⟩⟩
    refine ⟨q, ?_, mul_comm q a⟩
    rw [Finset.mem_Icc]
    have hqpos : 1 ≤ q := by
      by_contra hq0
      have : q = 0 := by omega
      subst this
      omega
    have hqle : q ≤ x / a := by
      have : (a * q) / a ≤ x / a := Nat.div_le_div_right hkx
      rwa [Nat.mul_div_right q ha] at this
    exact ⟨hqpos, hqle⟩

lemma countMultiples_singleton {a : ℕ} (ha : 0 < a) (x : ℕ) :
    countMultiples {a} x = x / a := by
  unfold countMultiples
  have hEq : (Finset.Icc 1 x).filter (fun k => k ≥ 1 ∧ ∃ u ∈ ({a} : Finset ℕ), u ∣ k) =
      (Finset.Icc 1 x).filter (fun k => a ∣ k) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton, exists_eq_left]
    tauto
  rw [hEq, card_multiples_single ha x]

/-- Key single-divisor bound: for `1 ≤ a ≤ n`, `n < 2 * (n / a) * a`. -/
lemma lt_two_mul_div_mul {a n : ℕ} (ha : 0 < a) (han : a ≤ n) :
    n < 2 * (n / a) * a := by
  have hq : 1 ≤ n / a := Nat.div_pos han ha
  have hmod : n < (n / a + 1) * a := by
    have h1 := Nat.div_add_mod n a
    have h2 := Nat.mod_lt n ha
    nlinarith
  nlinarith

/-- Singleton case in natural arithmetic: `countMultiples {a} m * n < 2 * countMultiples {a} n * m`. -/
lemma nat_ineq_singleton {a n m : ℕ} (ha : 2 ≤ a) (han : a ≤ n) (hnm : n < m) :
    countMultiples {a} m * n < 2 * countMultiples {a} n * m := by
  have ha0 : 0 < a := by omega
  rw [countMultiples_singleton ha0 m, countMultiples_singleton ha0 n]
  have h1 : n < 2 * (n / a) * a := lt_two_mul_div_mul ha0 han
  have h2 : (m / a) * a ≤ m := Nat.div_mul_le_self m a
  have hq : 1 ≤ n / a := Nat.div_pos han ha0
  rcases Nat.eq_zero_or_pos (m / a) with hm0 | hmpos
  · rw [hm0, zero_mul]
    have hm1 : 0 < m := by omega
    nlinarith
  · calc (m / a) * n < (m / a) * (2 * (n / a) * a) := Nat.mul_lt_mul_of_pos_left h1 hmpos
      _ = 2 * (n / a) * ((m / a) * a) := by ring
      _ ≤ 2 * (n / a) * m := Nat.mul_le_mul_left _ h2

/-- Inclusion-exclusion for a pair `{a, b}`: `countMultiples {a, b} x + x / lcm a b = x / a + x / b`. -/
lemma countMultiples_pair_add_lcm {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (x : ℕ) :
    countMultiples {a, b} x + x / Nat.lcm a b = x / a + x / b := by
  unfold countMultiples
  set Fa := (Finset.Icc 1 x).filter (fun k => a ∣ k)
  set Fb := (Finset.Icc 1 x).filter (fun k => b ∣ k)
  have hU : (Finset.Icc 1 x).filter (fun k => k ≥ 1 ∧ ∃ u ∈ ({a, b} : Finset ℕ), u ∣ k) = Fa ∪ Fb := by
    ext k
    constructor
    · intro hk
      rw [Finset.mem_filter] at hk
      rcases hk with ⟨hkI, _, u, huAB, hdvd⟩
      rw [Finset.mem_union]
      rcases Finset.mem_insert.mp huAB with rfl | hub
      · left; exact Finset.mem_filter.mpr ⟨hkI, hdvd⟩
      · right
        rw [Finset.mem_singleton.mp hub] at hdvd
        exact Finset.mem_filter.mpr ⟨hkI, hdvd⟩
    · intro hk
      rw [Finset.mem_filter]
      rw [Finset.mem_union] at hk
      rcases hk with hka | hkb
      · rw [Finset.mem_filter] at hka
        exact ⟨hka.1, (Finset.mem_Icc.mp hka.1).1, a, Finset.mem_insert_self a {b}, hka.2⟩
      · rw [Finset.mem_filter] at hkb
        exact ⟨hkb.1, (Finset.mem_Icc.mp hkb.1).1, b,
          Finset.mem_insert_of_mem (Finset.mem_singleton_self b), hkb.2⟩
  have hI : Fa ∩ Fb = (Finset.Icc 1 x).filter (fun k => Nat.lcm a b ∣ k) := by
    ext k
    simp only [Finset.mem_inter, Finset.mem_filter, Fa, Fb, Nat.lcm_dvd_iff]
    tauto
  have hLpos : 0 < Nat.lcm a b := Nat.lcm_pos ha hb
  rw [hU]
  have hcard := Finset.card_union_add_card_inter Fa Fb
  rw [hI, card_multiples_single ha x, card_multiples_single hb x, card_multiples_single hLpos x] at hcard
  exact hcard

/-- Periodicity step for `{a, b}`: shifting by `L = lcm a b` adds `L/a + L/b - 1`. -/
lemma countMultiples_pair_add_period {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (x : ℕ) :
    countMultiples {a, b} (x + Nat.lcm a b) =
      countMultiples {a, b} x + (Nat.lcm a b / a + Nat.lcm a b / b - 1) := by
  set L := Nat.lcm a b
  have hLpos : 0 < L := Nat.lcm_pos ha hb
  have hdvd_a : a ∣ L := Nat.dvd_lcm_left a b
  have hdvd_b : b ∣ L := Nat.dvd_lcm_right a b
  have h1 := countMultiples_pair_add_lcm ha hb (x + L)
  have h2 := countMultiples_pair_add_lcm ha hb x
  change countMultiples {a, b} (x + L) + (x + L) / L = (x + L) / a + (x + L) / b at h1
  change countMultiples {a, b} x + x / L = x / a + x / b at h2
  have hda : (x + L) / a = x / a + L / a := by
    rcases hdvd_a with ⟨v, hv⟩
    rw [hv, Nat.add_mul_div_left x v ha, Nat.mul_div_cancel_left v ha]
  have hdb : (x + L) / b = x / b + L / b := by
    rcases hdvd_b with ⟨u, hu⟩
    rw [hu, Nat.add_mul_div_left x u hb, Nat.mul_div_cancel_left u hb]
  have hdL : (x + L) / L = x / L + 1 := Nat.add_div_right x hLpos
  have hv1 : 1 ≤ L / a := Nat.div_pos (Nat.le_of_dvd hLpos hdvd_a) ha
  have hu1 : 1 ≤ L / b := Nat.div_pos (Nat.le_of_dvd hLpos hdvd_b) hb
  rw [hda, hdb, hdL] at h1
  omega

/-- Key lower bound for primitive pairs: `n * (u + v) < 2 * countMultiples {a, b} n * L` for all `n ≥ b`. -/
lemma pair_lower_bound {a b : ℕ} (ha : 2 ≤ a) (hab : a < b) (hndvd : ¬ (a ∣ b)) :
    ∀ n : ℕ, b ≤ n →
      n * (Nat.lcm a b / b + Nat.lcm a b / a) < 2 * countMultiples {a, b} n * Nat.lcm a b := by
  set L := Nat.lcm a b
  set v := L / a
  set u := L / b
  have ha0 : 0 < a := by omega
  have hb0 : 0 < b := by omega
  have hLpos : 0 < L := Nat.lcm_pos ha0 hb0
  have hdvd_a : a ∣ L := Nat.dvd_lcm_left a b
  have hdvd_b : b ∣ L := Nat.dvd_lcm_right a b
  have haL : a * v = L := Nat.mul_div_cancel' hdvd_a
  have hbL : b * u = L := Nat.mul_div_cancel' hdvd_b
  have hu2 : 2 ≤ u := by
    have hu1 : 1 ≤ u := Nat.div_pos (Nat.le_of_dvd hLpos hdvd_b) hb0
    by_contra hlt
    have hu_eq : u = 1 := by omega
    rw [hu_eq, mul_one] at hbL
    rw [← hbL] at hdvd_a
    exact hndvd hdvd_a
  have hv3 : 3 ≤ v := by
    have huv : a * u < a * v := by
      calc a * u < b * u := Nat.mul_lt_mul_of_pos_right hab (by omega)
        _ = L := hbL
        _ = a * v := haL.symm
    have : u < v := Nat.lt_of_mul_lt_mul_left huv
    omega
  -- Introduce `w = u + v - 1` without subtraction in `nlinarith`
  set w := u + v - 1
  have hw_add : w + 1 = u + v := by omega
  have hw4 : 4 ≤ w := by omega
  have hperiod_w : ∀ x : ℕ, countMultiples {a, b} (x + L) = countMultiples {a, b} x + w := by
    intro x
    have hp := countMultiples_pair_add_period ha0 hb0 x
    change countMultiples {a, b} (x + L) = countMultiples {a, b} x + (v + u - 1) at hp
    have hvu : v + u - 1 = w := by omega
    rw [hp, hvu]
  have h2bL : 2 * b ≤ L := by nlinarith
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hbn
    by_cases hnL : n < L
    · -- Case 1: b ≤ n < L
      have hndivL : n / L = 0 := Nat.div_eq_of_lt hnL
      have hcnt := countMultiples_pair_add_lcm ha0 hb0 n
      change countMultiples {a, b} n + n / L = n / a + n / b at hcnt
      rw [hndivL, add_zero] at hcnt
      have hna : n < 2 * (n / a) * a := lt_two_mul_div_mul ha0 (by omega)
      have hnb : n < 2 * (n / b) * b := lt_two_mul_div_mul hb0 hbn
      have h1 : n * v < 2 * (n / a) * L := by
        calc n * v < (2 * (n / a) * a) * v := Nat.mul_lt_mul_of_pos_right hna (by omega)
          _ = 2 * (n / a) * (a * v) := by ring
          _ = 2 * (n / a) * L := by rw [haL]
      have h2 : n * u < 2 * (n / b) * L := by
        calc n * u < (2 * (n / b) * b) * u := Nat.mul_lt_mul_of_pos_right hnb (by omega)
          _ = 2 * (n / b) * (b * u) := by ring
          _ = 2 * (n / b) * L := by rw [hbL]
      calc n * (u + v) = n * v + n * u := by ring
        _ < 2 * (n / a) * L + 2 * (n / b) * L := Nat.add_lt_add h1 h2
        _ = 2 * (n / a + n / b) * L := by ring
        _ = 2 * countMultiples {a, b} n * L := by rw [hcnt]
    · have hnL' : L ≤ n := by omega
      by_cases hnLb : n < L + b
      · -- Case 2: L ≤ n < L + b
        set r := n - L
        have hnr : n = r + L := by omega
        have hr_lt_b : r < b := by omega
        have hr_lt_L : r < L := by omega
        have hperiod := hperiod_w r
        have hcnt_r := countMultiples_pair_add_lcm ha0 hb0 r
        change countMultiples {a, b} r + r / L = r / a + r / b at hcnt_r
        rw [Nat.div_eq_of_lt hr_lt_L, add_zero] at hcnt_r
        have hcnt_n : countMultiples {a, b} n = (r / a + r / b) + w := by
          rw [hnr, hperiod, hcnt_r]
        by_cases hra : r < a
        · -- Subcase 2a: 0 ≤ r < a
          have hr_uv : r * (u + v) < 2 * L := by
            calc r * (u + v) < a * (u + v) := Nat.mul_lt_mul_of_pos_right hra (by omega)
              _ = a * u + a * v := by ring
              _ < a * v + a * v := by nlinarith
              _ = 2 * L := by nlinarith
          have hcnt_ge : w ≤ countMultiples {a, b} n := by
            rw [hcnt_n]
            exact Nat.le_add_left w (r / a + r / b)
          have hgap : (L + r) * (u + v) < 2 * w * L := by nlinarith
          calc n * (u + v) = (L + r) * (u + v) := by rw [hnr]; ring
            _ < 2 * w * L := hgap
            _ ≤ 2 * countMultiples {a, b} n * L :=
                Nat.mul_le_mul_right L (Nat.mul_le_mul_left 2 hcnt_ge)
        · -- Subcase 2b: a ≤ r < b
          have hra' : a ≤ r := by omega
          have hra1 : 1 ≤ r / a := Nat.div_pos hra' ha0
          have hcnt_ge : u + v ≤ countMultiples {a, b} n := by
            rw [hcnt_n, ← hw_add]
            have h1le : 1 ≤ r / a + r / b := le_trans hra1 (Nat.le_add_right _ _)
            omega
          have hLr : n < 2 * L := by omega
          calc n * (u + v) < (2 * L) * (u + v) := Nat.mul_lt_mul_of_pos_right hLr (by omega)
            _ = 2 * (u + v) * L := by ring
            _ ≤ 2 * countMultiples {a, b} n * L :=
                Nat.mul_le_mul_right L (Nat.mul_le_mul_left 2 hcnt_ge)
      · -- Case 3: n ≥ L + b (inductive step by subtracting L)
        set n' := n - L
        have hnn' : n = n' + L := by omega
        have hn'_lt : n' < n := by omega
        have hn'_ge : b ≤ n' := by omega
        have h_ih := ih n' hn'_lt hn'_ge
        have hperiod := hperiod_w n'
        have hL_step : L * (u + v) ≤ 2 * w * L := by nlinarith
        rw [hnn', hperiod]
        calc (n' + L) * (u + v) = n' * (u + v) + L * (u + v) := by ring
          _ < 2 * countMultiples {a, b} n' * L + 2 * w * L :=
              Nat.add_lt_add_of_lt_of_le h_ih hL_step
          _ = 2 * (countMultiples {a, b} n' + w) * L := by ring

/-- Primitive pair case in natural arithmetic. -/
lemma nat_ineq_pair {a b n m : ℕ} (ha : 2 ≤ a) (hab : a < b) (hndvd : ¬ (a ∣ b))
    (hbn : b ≤ n) (hnm : n < m) :
    countMultiples {a, b} m * n < 2 * countMultiples {a, b} n * m := by
  have ha0 : 0 < a := by omega
  have hb0 : 0 < b := by omega
  set L := Nat.lcm a b
  have hLpos : 0 < L := Nat.lcm_pos ha0 hb0
  set v := L / a
  set u := L / b
  have haL : a * v = L := Nat.mul_div_cancel' (Nat.dvd_lcm_left a b)
  have hbL : b * u = L := Nat.mul_div_cancel' (Nat.dvd_lcm_right a b)
  have hm_ie := countMultiples_pair_add_lcm ha0 hb0 m
  have hm_le : countMultiples {a, b} m ≤ m / a + m / b := Nat.le.intro hm_ie
  have hma : (m / a) * L ≤ m * v := by
    calc (m / a) * L = (m / a) * (a * v) := by rw [haL]
      _ = ((m / a) * a) * v := by ring
      _ ≤ m * v := Nat.mul_le_mul_right v (Nat.div_mul_le_self m a)
  have hmb : (m / b) * L ≤ m * u := by
    calc (m / b) * L = (m / b) * (b * u) := by rw [hbL]
      _ = ((m / b) * b) * u := by ring
      _ ≤ m * u := Nat.mul_le_mul_right u (Nat.div_mul_le_self m b)
  have hub : countMultiples {a, b} m * L ≤ m * (u + v) := by
    calc countMultiples {a, b} m * L ≤ (m / a + m / b) * L := Nat.mul_le_mul_right L hm_le
      _ = (m / a) * L + (m / b) * L := by ring
      _ ≤ m * v + m * u := Nat.add_le_add hma hmb
      _ = m * (u + v) := by ring
  have hlb : n * (u + v) < 2 * countMultiples {a, b} n * L := pair_lower_bound ha hab hndvd n hbn
  have hmpos : 0 < m := by omega
  have hmul : (countMultiples {a, b} m * n) * L < (2 * countMultiples {a, b} n * m) * L := by
    calc (countMultiples {a, b} m * n) * L = (countMultiples {a, b} m * L) * n := by ring
      _ ≤ (m * (u + v)) * n := Nat.mul_le_mul_right n hub
      _ = m * (n * (u + v)) := by ring
      _ < m * (2 * countMultiples {a, b} n * L) := Nat.mul_lt_mul_of_pos_left hlb hmpos
      _ = (2 * countMultiples {a, b} n * m) * L := by ring
  exact Nat.lt_of_mul_lt_mul_right hmul

/-- **Theorem (Positive Side):** Erdős Problem 488 holds unconditionally for all sets with `A.card ≤ 2`. -/
theorem erdos_488_card_le_two (A : Finset ℕ) (hA : A.Nonempty) (hcard : A.card ≤ 2)
    (h0 : 0 ∉ A) (h1 : 1 ∉ A) :
    letI B := {n ≥ 1 | ∃ a ∈ A, a ∣ n}
    ∀ᵉ (n : ℕ) (m > n), A.max ≤ n →
      ((Finset.Icc 1 m).filter (· ∈ B)).card / (m : ℚ) <
        2 * ((Finset.Icc 1 n).filter (· ∈ B)).card / n := by
  intro n m hnm hmax
  rw [countMultiples_eq_filter_Set A m, countMultiples_eq_filter_Set A n]
  have hall_ge2 : ∀ x ∈ A, 2 ≤ x := by
    intro x hx
    by_contra hlt
    interval_cases x
    · exact h0 hx
    · exact h1 hx
  have hall_le_n : ∀ x ∈ A, x ≤ n := by
    intro x hx
    exact WithBot.coe_le_coe.mp ((Finset.le_max hx).trans hmax)
  have hnat : countMultiples A m * n < 2 * countMultiples A n * m := by
    have hpos_card : 1 ≤ A.card := Finset.Nonempty.card_pos hA
    interval_cases hAk : A.card
    · rcases Finset.card_eq_one.mp hAk with ⟨a, rfl⟩
      exact nat_ineq_singleton (hall_ge2 a (Finset.mem_singleton_self a))
        (hall_le_n a (Finset.mem_singleton_self a)) hnm
    · rcases Finset.card_eq_two.mp hAk with ⟨x, y, hxy, rfl⟩
      have hpair : ∀ u v : ℕ, u < v → 2 ≤ u → v ≤ n →
          countMultiples {u, v} m * n < 2 * countMultiples {u, v} n * m := by
        intro u v huv hu2 hvn
        by_cases hdvd : u ∣ v
        · have hred : ∀ t, countMultiples {u, v} t = countMultiples {u} t := by
            intro t
            unfold countMultiples
            congr 1
            ext k
            rw [Finset.mem_filter, Finset.mem_filter]
            constructor
            · rintro ⟨hkI, hk1, z, hz, hzk⟩
              rcases Finset.mem_insert.mp hz with rfl | hzv
              · exact ⟨hkI, hk1, z, Finset.mem_singleton_self z, hzk⟩
              · rw [Finset.mem_singleton.mp hzv] at hzk
                exact ⟨hkI, hk1, u, Finset.mem_singleton_self u, dvd_trans hdvd hzk⟩
            · rintro ⟨hkI, hk1, z, hz, hzk⟩
              rw [Finset.mem_singleton.mp hz] at hzk
              exact ⟨hkI, hk1, u, Finset.mem_insert_self u {v}, hzk⟩
          rw [hred m, hred n]
          exact nat_ineq_singleton hu2 (by omega) hnm
        · exact nat_ineq_pair hu2 huv hdvd hvn hnm
      by_cases hlt : x < y
      · exact hpair x y hlt (hall_ge2 x (by simp)) (hall_le_n y (by simp))
      · have hyx : y < x := by omega
        rw [Finset.pair_comm x y]
        exact hpair y x hyx (hall_ge2 y (by simp)) (hall_le_n x (by simp))
  have hn0 : (0 : ℚ) < n := by
    rcases hA with ⟨a, ha⟩
    have : 2 ≤ n := le_trans (hall_ge2 a ha) (hall_le_n a ha)
    exact_mod_cast (by omega : 0 < n)
  have hm0 : (0 : ℚ) < m := by
    have : 0 < n := by exact_mod_cast hn0
    exact_mod_cast (by omega : 0 < m)
  rw [div_lt_div_iff₀ hm0 hn0]
  exact_mod_cast hnat

end Erdos488
