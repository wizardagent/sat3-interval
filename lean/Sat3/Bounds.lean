import Sat3.Basic

/-
  Arithmetic for I_k and the comparison (2^k)^2 < 4 n.
  Paper Lemma 9.1 and the last line of Theorem 9.2.
-/

namespace Sat3

/-- Lower endpoint of `I_k = [(3^k-1)/2, (4^k-1)/3]`. -/
def Ilo (k : Nat) : Nat := (3 ^ k - 1) / 2

/-- Upper endpoint of `I_k`. -/
def Ihi (k : Nat) : Nat := (4 ^ k - 1) / 3

theorem three_pow_odd (k : Nat) : 3 ^ k % 2 = 1 := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [Nat.pow_succ, Nat.mul_mod, ih]

theorem four_pow_mod_three (k : Nat) : 4 ^ k % 3 = 1 := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [Nat.pow_succ, Nat.mul_mod, ih]

theorem two_mul_Ilo (k : Nat) : 2 * Ilo k = 3 ^ k - 1 := by
  unfold Ilo
  have hodd : (3 ^ k) % 2 = 1 := three_pow_odd k
  have h2 : 1 ≤ 3 ^ k := Nat.one_le_pow k 3 (by decide)
  have heven : (3 ^ k - 1) % 2 = 0 := by omega
  exact Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero heven)

theorem three_mul_Ihi (k : Nat) : 3 * Ihi k = 4 ^ k - 1 := by
  unfold Ihi
  have hmod : (4 ^ k) % 3 = 1 := four_pow_mod_three k
  have h1 : 1 ≤ 4 ^ k := Nat.one_le_pow k 4 (by decide)
  have hdvd : (4 ^ k - 1) % 3 = 0 := by omega
  exact Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hdvd)

theorem Ilo_succ (k : Nat) : Ilo (k + 1) = 3 * Ilo k + 1 := by
  have hL : 2 * Ilo (k + 1) = 3 ^ (k + 1) - 1 := two_mul_Ilo (k + 1)
  have hS : 2 * Ilo k = 3 ^ k - 1 := two_mul_Ilo k
  have hk : 1 ≤ 3 ^ k := Nat.one_le_pow k 3 (by decide)
  have hpow : 3 ^ (k + 1) = 3 ^ k * 3 := Nat.pow_succ 3 k
  omega

theorem Ihi_succ (k : Nat) : Ihi (k + 1) = 4 * Ihi k + 1 := by
  have hL : 3 * Ihi (k + 1) = 4 ^ (k + 1) - 1 := three_mul_Ihi (k + 1)
  have hS : 3 * Ihi k = 4 ^ k - 1 := three_mul_Ihi k
  have hk : 1 ≤ 4 ^ k := Nat.one_le_pow k 4 (by decide)
  have hpow : 4 ^ (k + 1) = 4 ^ k * 4 := Nat.pow_succ 4 k
  omega

theorem Ilo_one : Ilo 1 = 1 := by decide
theorem Ihi_one : Ihi 1 = 1 := by decide

theorem Ilo_le_Ihi (k : Nat) (hk : 1 ≤ k) : Ilo k ≤ Ihi k := by
  induction k with
  | zero => omega
  | succ m ih =>
    match m with
    | 0 =>
      exact (by decide : Ilo 1 ≤ Ihi 1)
    | m + 1 =>
      have h : Ilo (m + 1) ≤ Ihi (m + 1) := ih (Nat.succ_le_succ (Nat.zero_le _))
      have hs : Ilo (m + 1 + 1) = 3 * Ilo (m + 1) + 1 := Ilo_succ (m + 1)
      have ht : Ihi (m + 1 + 1) = 4 * Ihi (m + 1) + 1 := Ihi_succ (m + 1)
      omega

/-- `4^k = 3 * Ihi k + 1`. -/
theorem four_pow_Ihi (k : Nat) : 4 ^ k = 3 * Ihi k + 1 := by
  have h : 3 * Ihi k = 4 ^ k - 1 := three_mul_Ihi k
  have hk : 1 ≤ 4 ^ k := Nat.one_le_pow k 4 (by decide)
  omega

/-- `3^k = 2 * Ilo k + 1`. -/
theorem three_pow_Ilo (k : Nat) : 3 ^ k = 2 * Ilo k + 1 := by
  have h : 2 * Ilo k = 3 ^ k - 1 := two_mul_Ilo k
  have hk : 1 ≤ 3 ^ k := Nat.one_le_pow k 3 (by decide)
  omega

theorem two_pow_mul (k : Nat) : 2 ^ k * 2 ^ k = 4 ^ k := by
  induction k with
  | zero => decide
  | succ k ih =>
    have h2 : 2 ^ (k + 1) = 2 ^ k * 2 := Nat.pow_succ 2 k
    have h4 : 4 ^ (k + 1) = 4 ^ k * 4 := Nat.pow_succ 4 k
    rw [h2, h4]
    calc
      (2 ^ k * 2) * (2 ^ k * 2)
          = 2 ^ k * (2 * (2 ^ k * 2)) := by rw [Nat.mul_assoc]
      _ = 2 ^ k * ((2 * 2 ^ k) * 2) := by rw [← Nat.mul_assoc 2]
      _ = 2 ^ k * ((2 ^ k * 2) * 2) := by rw [Nat.mul_comm 2]
      _ = 2 ^ k * (2 ^ k * (2 * 2)) := by rw [Nat.mul_assoc (2 ^ k)]
      _ = (2 ^ k * 2 ^ k) * 4 := by
          rw [← Nat.mul_assoc]
      _ = 4 ^ k * 4 := by rw [ih]

/-- Last line of Theorem 9.2: `4^{k-1} < n` implies `(2^k)^2 < 4 n`. -/
theorem two_pow_sq_lt (k n : Nat) (hk : 1 ≤ k) (hn : 4 ^ (k - 1) < n) :
    2 ^ k * 2 ^ k < 4 * n := by
  cases k with
  | zero => omega
  | succ m =>
    have hpow : 2 ^ (m + 1) * 2 ^ (m + 1) = 4 ^ (m + 1) := two_pow_mul (m + 1)
    have h4 : 4 ^ (m + 1) = 4 ^ m * 4 := Nat.pow_succ 4 m
    have hn' : 4 ^ m < n := hn
    have : 4 ^ (m + 1) < 4 * n := by
      rw [h4, Nat.mul_comm (4 ^ m)]
      exact Nat.mul_lt_mul_of_pos_left hn' (by decide)
    omega

/-- `3^k ≤ 2 * 4^{k-1} + 1` for `k ≥ 1`. -/
theorem lower_window (k : Nat) (hk : 1 ≤ k) : 3 ^ k ≤ 2 * 4 ^ (k - 1) + 1 := by
  induction k with
  | zero => omega
  | succ m ih =>
    match m with
    | 0 => decide
    | m + 1 =>
      have ih' : 3 ^ (m + 1) ≤ 2 * 4 ^ m + 1 := ih (Nat.succ_le_succ (Nat.zero_le _))
      have h3 : 3 ^ (m + 2) = 3 ^ (m + 1) * 3 := Nat.pow_succ 3 (m + 1)
      have h4 : 4 ^ (m + 1) = 4 ^ m * 4 := Nat.pow_succ 4 m
      have hmul : 3 ^ (m + 1) * 3 ≤ (2 * 4 ^ m + 1) * 3 :=
        Nat.mul_le_mul_right 3 ih'
      have hpow4 : 1 ≤ 4 ^ m := Nat.one_le_pow m 4 (by decide)
      have hcmp : (2 * 4 ^ m + 1) * 3 ≤ 2 * (4 ^ m * 4) + 1 := by omega
      have : 3 ^ (m + 2) ≤ 2 * 4 ^ (m + 1) + 1 := by
        rw [h3, h4]
        omega
      simpa using this

theorem Ilo_succ_le (k : Nat) (hk : 1 ≤ k) :
    Ilo k + 1 ≤ 4 ^ (k - 1) + 1 := by
  have h3 : 3 ^ k = 2 * Ilo k + 1 := three_pow_Ilo k
  have hw : 3 ^ k ≤ 2 * 4 ^ (k - 1) + 1 := lower_window k hk
  omega

theorem le_max_left' (a b : Nat) : a ≤ max a b := by
  rw [Nat.max_def]
  by_cases h : a ≤ b <;> simp [h]

theorem le_max_right' (a b : Nat) : b ≤ max a b := by
  rw [Nat.max_def]
  by_cases h : a ≤ b
  · simp [h]
  · simp [h]
    omega

theorem max_le' {a b c : Nat} (ha : a ≤ c) (hb : b ≤ c) : max a b ≤ c := by
  rw [Nat.max_def]
  by_cases h : a ≤ b <;> simp [h] <;> omega

theorem max_add_one (a b : Nat) : max a b + 1 = max (a + 1) (b + 1) := by
  rw [Nat.max_def, Nat.max_def]
  by_cases h : a ≤ b <;> by_cases h' : a + 1 ≤ b + 1 <;> simp [h, h'] <;> omega

/-- Chosen radius: `max(Ilo k, ⌈(n-1)/3⌉)`. -/
def chosenR (k n : Nat) : Nat :=
  max (Ilo k) ((n + 1) / 3)

theorem three_mul_add_two_div (m : Nat) : (3 * m + 2) / 3 = m := by
  omega

/-- Lemma 9.1: `chosenR k n` lies in `I_k` and satisfies `R+1 ≤ n ≤ 3R+1`. -/
theorem chosenR_window (k n : Nat) (hk : 1 ≤ k) (hn2 : 2 ≤ n)
    (_hnlo : 4 ^ (k - 1) < n) (hnhi : n ≤ 4 ^ k) :
    Ilo k ≤ chosenR k n ∧
    chosenR k n ≤ Ihi k ∧
    chosenR k n + 1 ≤ n ∧
    n ≤ 3 * chosenR k n + 1 := by
  have hI : Ilo k ≤ Ihi k := Ilo_le_Ihi k hk
  have h4eq : 4 ^ k = 3 * Ihi k + 1 := four_pow_Ihi k
  have h4 : n ≤ 3 * Ihi k + 1 := by omega
  have hceil_le : (n + 1) / 3 ≤ Ihi k := by
    have : n + 1 ≤ 3 * Ihi k + 2 := by omega
    have hdiv : (n + 1) / 3 ≤ (3 * Ihi k + 2) / 3 :=
      Nat.div_le_div_right this
    have heq : (3 * Ihi k + 2) / 3 = Ihi k := three_mul_add_two_div (Ihi k)
    omega
  have hR_le : chosenR k n ≤ Ihi k := by
    unfold chosenR
    exact max_le' hI hceil_le
  have hR_ge : Ilo k ≤ chosenR k n := by
    unfold chosenR
    exact le_max_left' _ _
  have hceil_n : (n + 1) / 3 + 1 ≤ n := by
    have : n + 1 ≤ 3 * (n - 1) + 2 := by omega
    have hdiv : (n + 1) / 3 ≤ (3 * (n - 1) + 2) / 3 :=
      Nat.div_le_div_right this
    have heq : (3 * (n - 1) + 2) / 3 = n - 1 := three_mul_add_two_div (n - 1)
    omega
  have hIlo_n : Ilo k + 1 ≤ n := by
    have := Ilo_succ_le k hk
    omega
  have hR1 : chosenR k n + 1 ≤ n := by
    unfold chosenR
    rw [max_add_one]
    exact max_le' hIlo_n hceil_n
  have hnR : n ≤ 3 * chosenR k n + 1 := by
    have hge : (n + 1) / 3 ≤ chosenR k n := by
      unfold chosenR
      exact le_max_right' _ _
    have hmul : 3 * ((n + 1) / 3) ≤ 3 * chosenR k n := Nat.mul_le_mul_left 3 hge
    have hdiv : 3 * ((n + 1) / 3) ≤ n + 1 := Nat.mul_div_le (n + 1) 3
    omega
  exact ⟨hR_ge, hR_le, hR1, hnR⟩

end Sat3
