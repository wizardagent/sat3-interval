import Sat3.Basic

/-
  Pair bound formula: 2 * (k + 3 * C(k,2)) = k * (3k - 1) for k ≥ 1.
-/

namespace Sat3

def pairBound (k : Nat) : Nat :=
  k + 3 * (k * (k - 1) / 2)

private theorem two_mul_div_two_of_even (n : Nat) (h : n % 2 = 0) :
    2 * (n / 2) = n :=
  Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h)

private theorem succ_mul_self_even (m : Nat) : ((m + 1) * m) % 2 = 0 := by
  have : m % 2 = 0 ∨ m % 2 = 1 := Nat.mod_two_eq_zero_or_one m
  rcases this with h | h
  · rw [Nat.mul_mod, h]; simp
  · have : (m + 1) % 2 = 0 := by omega
    rw [Nat.mul_comm, Nat.mul_mod, this]; simp

/-- `2 * pairBound (m+1) = (m+1) * (3m + 2)`. -/
theorem pairBound_succ (m : Nat) :
    2 * pairBound (m + 1) = (m + 1) * (3 * m + 2) := by
  have hdiv : 2 * ((m + 1) * m / 2) = (m + 1) * m :=
    two_mul_div_two_of_even ((m + 1) * m) (succ_mul_self_even m)
  unfold pairBound
  rw [Nat.add_sub_cancel]
  -- goal: 2 * (m+1 + 3 * ((m+1)*m/2)) = (m+1)*(3m+2)
  let q := (m + 1) * m / 2
  have hq : 2 * q = (m + 1) * m := hdiv
  change 2 * (m + 1 + 3 * q) = (m + 1) * (3 * m + 2)
  have h1 : 2 * (m + 1 + 3 * q) = 2 * (m + 1) + 6 * q := by omega
  rw [h1]
  have h2 : 6 * q = 3 * (2 * q) := by omega
  rw [h2, hq]
  -- 2(m+1) + 3(m+1)m = (m+1)(2 + 3m) = (m+1)(3m+2)
  have h3 : 2 * (m + 1) + 3 * ((m + 1) * m) = (m + 1) * (3 * m + 2) := by
    have ha : 2 * (m + 1) = 2 * m + 2 := by omega
    have hb : (m + 1) * m = m * m + m := by
      rw [Nat.succ_mul]
    have hc : 3 * (m * m + m) = 3 * (m * m) + 3 * m := by
      omega
    have hd : (m + 1) * (3 * m + 2) = m * (3 * m + 2) + (3 * m + 2) := by
      rw [Nat.succ_mul]
    have he : m * (3 * m + 2) = 3 * (m * m) + 2 * m := by
      rw [Nat.mul_add]
      have : m * (3 * m) = 3 * (m * m) := by
        calc
          m * (3 * m) = (m * 3) * m := by rw [← Nat.mul_assoc]
          _ = (3 * m) * m := by rw [Nat.mul_comm m 3]
          _ = 3 * (m * m) := by rw [Nat.mul_assoc]
      rw [this]
      rw [Nat.mul_comm m 2]
    -- LHS: 2m+2 + 3(m²+m) = 2m+2 + 3m² + 3m = 3m² + 5m + 2
    -- RHS: 3m² + 2m + 3m + 2 = 3m² + 5m + 2
    rw [ha, hb, hc, hd, he]
    omega
  exact h3

/-- For `k ≥ 1`, `2 * pairBound k = k * (3 * k - 1)`. -/
theorem pairBound_double (k : Nat) (hk : 1 ≤ k) :
    2 * pairBound k = k * (3 * k - 1) := by
  cases k with
  | zero => omega
  | succ m =>
    have h := pairBound_succ m
    have hpred : 3 * (m + 1) - 1 = 3 * m + 2 := by omega
    rw [hpred]
    exact h

/-- `k(3k-1)/2 = pairBound k` for `k ≥ 1`. -/
theorem pairBound_half (k : Nat) (hk : 1 ≤ k) :
    k * (3 * k - 1) / 2 = pairBound k := by
  have h := pairBound_double k hk
  have heven : (k * (3 * k - 1)) % 2 = 0 := by omega
  have hdiv : 2 * ((k * (3 * k - 1)) / 2) = k * (3 * k - 1) :=
    Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero heven)
  omega

/-- If `k(3k-1)/2 < n` then no maximal 3-AP-free set of size `k` can
cover `[n]`, in the counting sense of Proposition 2.2. -/
theorem pairBound_lt_forces (k n : Nat) (hk : 1 ≤ k)
    (h : pairBound k < n) : ¬ n ≤ k * (3 * k - 1) / 2 := by
  rw [pairBound_half k hk]
  exact Nat.not_le_of_gt h

/-- `pairBound` is nondecreasing. -/
theorem pairBound_le_succ (k : Nat) : pairBound k ≤ pairBound (k + 1) := by
  cases k with
  | zero =>
    simp [pairBound]
  | succ m =>
    have hL := pairBound_double (m + 1) (Nat.succ_le_succ (Nat.zero_le _))
    have hR := pairBound_double (m + 2) (by omega)
    have h1 : 3 * (m + 1) - 1 = 3 * m + 2 := by omega
    have h2 : 3 * (m + 2) - 1 = 3 * m + 5 := by omega
    have hL' : 2 * pairBound (m + 1) = (m + 1) * (3 * m + 2) := by
      rw [hL, h1]
    have hR' : 2 * pairBound (m + 2) = (m + 2) * (3 * m + 5) := by
      rw [hR, h2]
    have hexpL : (m + 1) * (3 * m + 2) = 3 * m * m + 5 * m + 2 := by
      have : (m + 1) * (3 * m + 2) = m * (3 * m + 2) + (3 * m + 2) :=
        Nat.succ_mul m (3 * m + 2)
      have : m * (3 * m + 2) = 3 * m * m + 2 * m := by
        rw [Nat.mul_add, Nat.mul_comm m 2]
        have : m * (3 * m) = 3 * m * m := by
          rw [← Nat.mul_assoc, Nat.mul_comm m 3, Nat.mul_assoc]
        rw [this]
      omega
    have hexpR : (m + 2) * (3 * m + 5) = 3 * m * m + 11 * m + 10 := by
      have : (m + 2) * (3 * m + 5) = m * (3 * m + 5) + 2 * (3 * m + 5) := by
        rw [Nat.succ_mul, Nat.succ_mul]
        omega
      have hm : m * (3 * m + 5) = 3 * m * m + 5 * m := by
        rw [Nat.mul_add]
        have : m * (3 * m) = 3 * m * m := by
          rw [← Nat.mul_assoc, Nat.mul_comm m 3, Nat.mul_assoc]
        rw [this, Nat.mul_comm m 5]
      have h2 : 2 * (3 * m + 5) = 6 * m + 10 := by omega
      omega
    have hmul : 2 * pairBound (m + 1) ≤ 2 * pairBound (m + 2) := by
      rw [hL', hR', hexpL, hexpR]
      omega
    exact Nat.le_of_mul_le_mul_left hmul (by decide : 0 < 2)

theorem pairBound_mono {a b : Nat} (h : a ≤ b) : pairBound a ≤ pairBound b := by
  induction b with
  | zero =>
    have : a = 0 := Nat.eq_zero_of_le_zero h
    subst a
    exact Nat.le_refl _
  | succ b ih =>
    by_cases h' : a ≤ b
    · exact Nat.le_trans (ih h') (pairBound_le_succ b)
    · have : a = b + 1 := by omega
      subst a
      exact Nat.le_refl _

/-- Quadratic form of the pair bound: `3k² ≥ 2n` whenever
`n ≤ pairBound k`. Hence `k ≥ √(2n/3)` in ordinary mathematics. -/
theorem pairBound_quadratic (k n : Nat) (hk : 1 ≤ k)
    (hn : n ≤ pairBound k) : 2 * n ≤ 3 * k * k := by
  have h := pairBound_double k hk
  have : 2 * n ≤ 2 * pairBound k := Nat.mul_le_mul_left 2 hn
  have : 2 * n ≤ k * (3 * k - 1) := by omega
  have : k * (3 * k - 1) ≤ 3 * k * k := by
    have : k * (3 * k - 1) = 3 * k * k - k := by
      have h1 : 3 * k - 1 ≤ 3 * k := by omega
      have h2 : k * (3 * k) = 3 * k * k := by
        rw [Nat.mul_comm k (3 * k), Nat.mul_assoc]
      have h3 : k * (3 * k - 1) = k * (3 * k) - k * 1 :=
        Nat.mul_sub_left_distrib k (3 * k) 1
      omega
    omega
  omega

end Sat3
