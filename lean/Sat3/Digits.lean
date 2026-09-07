import Sat3.Bounds

/-
  Greedy predecessor for Corollary 8.3.
  If R ∈ I_{k+1} then S = min(Ihi k, ⌊(R-1)/3⌋) lies in I_k
  and d = R - S is an admissible digit.
-/

namespace Sat3

/-- Greedy previous sum: largest point of `I_k` that can precede `R`. -/
def greedyPred (k R : Nat) : Nat :=
  min (Ihi k) ((R - 1) / 3)

theorem le_min_left' (a b : Nat) : min a b ≤ a := by
  rw [Nat.min_def]
  by_cases h : a ≤ b
  · simp [h]
  · simp [h]
    omega

theorem le_min_right' (a b : Nat) : min a b ≤ b := by
  rw [Nat.min_def]
  by_cases h : a ≤ b
  · simp [h]
  · simp [h]

theorem le_min' {a b c : Nat} (ha : a ≤ b) (hb : a ≤ c) : a ≤ min b c := by
  rw [Nat.min_def]
  by_cases h : b ≤ c
  · simp [h]
    exact ha
  · simp [h]
    exact hb

theorem Ilo_two : Ilo 2 = 4 := by decide
theorem Ihi_two : Ihi 2 = 5 := by decide

/-- `Ilo k ≥ 4` for `k ≥ 2`. -/
theorem Ilo_ge_four (k : Nat) (hk : 2 ≤ k) : 4 ≤ Ilo k := by
  obtain ⟨m, hm⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  subst k
  induction m with
  | zero =>
    exact (by decide : 4 ≤ Ilo 2)
  | succ m ih =>
    rw [Ilo_succ (m + 2)]
    omega

theorem greedyPred_eq_Ihi (k R : Nat) (h : Ihi k ≤ (R - 1) / 3) :
    greedyPred k R = Ihi k := by
  unfold greedyPred
  rw [Nat.min_def]
  simp [h]

theorem greedyPred_eq_div (k R : Nat) (h : ¬ Ihi k ≤ (R - 1) / 3) :
    greedyPred k R = (R - 1) / 3 := by
  unfold greedyPred
  rw [Nat.min_def]
  simp [h]

/-- The `k = 1` step: `I_2 = {4,5}` and `S = 1`. -/
theorem greedyPred_spec_one (R : Nat) (hlo : 4 ≤ R) (hhi : R ≤ 5) :
    greedyPred 1 R = 1 := by
  have hR : R = 4 ∨ R = 5 := by omega
  have hI : Ihi 1 = 1 := Ihi_one
  rcases hR with hR | hR
  · subst R
    unfold greedyPred
    rw [hI]
    decide
  · subst R
    unfold greedyPred
    rw [hI]
    decide

theorem greedyPred_le_Ihi (k R : Nat) : greedyPred k R ≤ Ihi k :=
  le_min_left' _ _

theorem greedyPred_le_div (k R : Nat) : greedyPred k R ≤ (R - 1) / 3 :=
  le_min_right' _ _

theorem greedyPred_three (k R : Nat) :
    3 * greedyPred k R ≤ R - 1 ∨ R = 0 := by
  by_cases hR : R = 0
  · exact Or.inr hR
  · have : 1 ≤ R := by omega
    have hdiv : 3 * ((R - 1) / 3) ≤ R - 1 := Nat.mul_div_le (R - 1) 3
    have hS : greedyPred k R ≤ (R - 1) / 3 := greedyPred_le_div k R
    exact Or.inl (Nat.le_trans (Nat.mul_le_mul_left 3 hS) hdiv)

theorem greedyPred_ge_Ilo (k R : Nat) (hk : 1 ≤ k)
    (hlo : Ilo (k + 1) ≤ R) :
    Ilo k ≤ greedyPred k R := by
  have hI : Ilo k ≤ Ihi k := Ilo_le_Ihi k hk
  have hsucc : Ilo (k + 1) = 3 * Ilo k + 1 := Ilo_succ k
  have hR1 : 3 * Ilo k ≤ R - 1 := by omega
  have : Ilo k ≤ (R - 1) / 3 := by
    have hdiv : (3 * Ilo k) / 3 ≤ (R - 1) / 3 := Nat.div_le_div_right hR1
    omega
  exact le_min' hI this

/-- One backward step, `k ≥ 2`. -/
theorem greedyPred_spec_ge_two (k R : Nat) (hk : 2 ≤ k)
    (hlo : Ilo (k + 1) ≤ R) (hhi : R ≤ Ihi (k + 1)) :
    Ilo k ≤ greedyPred k R ∧
    greedyPred k R ≤ Ihi k ∧
    2 * greedyPred k R + 1 ≤ R - greedyPred k R ∧
    R - greedyPred k R ≤ 3 * greedyPred k R + 1 := by
  have hk1 : 1 ≤ k := Nat.le_trans (by decide : 1 ≤ 2) hk
  have hRpos : 1 ≤ R := by
    have h1 : 1 ≤ 3 ^ (k + 1) := Nat.one_le_pow (k + 1) 3 (by decide)
    have := two_mul_Ilo (k + 1)
    omega
  have hS_ge := greedyPred_ge_Ilo k R hk1 hlo
  have hS_le := greedyPred_le_Ihi k R
  have h3 : 3 * greedyPred k R ≤ R - 1 := by
    have h := greedyPred_three k R
    omega
  have hd_ge : 2 * greedyPred k R + 1 ≤ R - greedyPred k R := by omega
  have h4 : 4 ≤ Ilo k := Ilo_ge_four k hk
  have hS2 : 2 ≤ greedyPred k R := Nat.le_trans (by omega) hS_ge
  have hsucc : Ihi (k + 1) = 4 * Ihi k + 1 := Ihi_succ k
  have hd_le : R - greedyPred k R ≤ 3 * greedyPred k R + 1 := by
    by_cases hcase : Ihi k ≤ (R - 1) / 3
    · have hS := greedyPred_eq_Ihi k R hcase
      omega
    · have hS := greedyPred_eq_div k R hcase
      have hmod := Nat.div_add_mod (R - 1) 3
      have hr : (R - 1) % 3 < 3 := Nat.mod_lt (R - 1) (by decide)
      omega
  exact ⟨hS_ge, hS_le, hd_ge, hd_le⟩

/-- One backward step of Corollary 8.3. -/
theorem greedyPred_spec (k R : Nat) (hk : 1 ≤ k)
    (hlo : Ilo (k + 1) ≤ R) (hhi : R ≤ Ihi (k + 1)) :
    Ilo k ≤ greedyPred k R ∧
    greedyPred k R ≤ Ihi k ∧
    2 * greedyPred k R + 1 ≤ R - greedyPred k R ∧
    R - greedyPred k R ≤ 3 * greedyPred k R + 1 := by
  cases k with
  | zero => omega
  | succ k =>
    cases k with
    | zero =>
      have hIlo2 : Ilo 2 = 4 := Ilo_two
      have hIhi2 : Ihi 2 = 5 := Ihi_two
      change Ilo 2 ≤ R at hlo
      change R ≤ Ihi 2 at hhi
      rw [hIlo2] at hlo
      rw [hIhi2] at hhi
      have hS := greedyPred_spec_one R hlo hhi
      have hIlo : Ilo 1 = 1 := Ilo_one
      have hIhi : Ihi 1 = 1 := Ihi_one
      rw [hS, hIlo, hIhi]
      omega
    | succ k =>
      exact greedyPred_spec_ge_two (k + 2) R (by omega) hlo hhi

/-- Forward half of Corollary 8.3: an admissible step from `I_k` lands in `I_{k+1}`. -/
theorem admissible_sum_in_I (k S d : Nat) (_hk : 1 ≤ k)
    (hSlo : Ilo k ≤ S) (hShi : S ≤ Ihi k)
    (hdlo : 2 * S + 1 ≤ d) (hdhi : d ≤ 3 * S + 1) :
    Ilo (k + 1) ≤ S + d ∧ S + d ≤ Ihi (k + 1) := by
  have hsuccL : Ilo (k + 1) = 3 * Ilo k + 1 := Ilo_succ k
  have hsuccR : Ihi (k + 1) = 4 * Ihi k + 1 := Ihi_succ k
  constructor
  · have : 3 * S + 1 ≤ S + d := by omega
    omega
  · have : S + d ≤ 4 * S + 1 := by omega
    omega

/-- Admissible digits are exactly the sums in `[3S+1, 4S+1]`. -/
theorem greedyPred_in_image (k R : Nat) (hk : 1 ≤ k)
    (hlo : Ilo (k + 1) ≤ R) (hhi : R ≤ Ihi (k + 1)) :
    3 * greedyPred k R + 1 ≤ R ∧ R ≤ 4 * greedyPred k R + 1 := by
  have h := greedyPred_spec k R hk hlo hhi
  omega

/-- Consecutive images `[3S+1, 4S+1]` and `[3(S+1)+1, 4(S+1)+1]` meet
once `S ≥ 2`, because `3S+4 ≤ 4S+2`. -/
theorem consecutive_images_overlap (S : Nat) (hS : 2 ≤ S) :
    3 * (S + 1) + 1 ≤ 4 * S + 2 := by
  omega

/-- `I_1 = {1}`. -/
theorem I_one : Ilo 1 = 1 ∧ Ihi 1 = 1 :=
  ⟨Ilo_one, Ihi_one⟩

def sumList : List Nat → Nat
  | [] => 0
  | x :: xs => x + sumList xs

theorem sumList_append (xs ys : List Nat) :
    sumList (xs ++ ys) = sumList xs + sumList ys := by
  induction xs with
  | nil => simp [sumList]
  | cons x xs ih =>
    simp [sumList, ih]
    omega

theorem sumList_singleton (x : Nat) : sumList [x] = x := by
  simp [sumList]

/-- Greedy digit sequence of length `k` summing to `R ∈ I_k`. -/
def greedyDigits : Nat → Nat → List Nat
  | 0, _ => []
  | 1, _ => [1]
  | k + 2, R =>
      greedyDigits (k + 1) (greedyPred (k + 1) R) ++
        [R - greedyPred (k + 1) R]

theorem greedyDigits_one (R : Nat) : greedyDigits 1 R = [1] := rfl

theorem greedyDigits_succ (k R : Nat) :
    greedyDigits (k + 2) R =
      greedyDigits (k + 1) (greedyPred (k + 1) R) ++
        [R - greedyPred (k + 1) R] := rfl

theorem greedyDigits_length :
    ∀ k R, 1 ≤ k → Ilo k ≤ R → R ≤ Ihi k → (greedyDigits k R).length = k
  | 0, R, hk, _, _ => by omega
  | 1, R, _, _, _ => by simp [greedyDigits]
  | k + 2, R, hk, hlo, hhi => by
      rw [greedyDigits_succ]
      have hk1 : 1 ≤ k + 1 := by omega
      have hpred := greedyPred_spec (k + 1) R hk1 (by simpa using hlo) (by simpa using hhi)
      have hlen := greedyDigits_length (k + 1) (greedyPred (k + 1) R) hk1 hpred.1 hpred.2.1
      simp [hlen]

theorem greedyDigits_sum :
    ∀ k R, 1 ≤ k → Ilo k ≤ R → R ≤ Ihi k → sumList (greedyDigits k R) = R
  | 0, R, hk, _, _ => by omega
  | 1, R, _, hlo, hhi => by
      have hIlo : Ilo 1 = 1 := Ilo_one
      have hIhi : Ihi 1 = 1 := Ihi_one
      have : R = 1 := by omega
      simp [greedyDigits, sumList, this]
  | k + 2, R, hk, hlo, hhi => by
      rw [greedyDigits_succ, sumList_append, sumList_singleton]
      have hk1 : 1 ≤ k + 1 := by omega
      have hpred := greedyPred_spec (k + 1) R hk1 (by simpa using hlo) (by simpa using hhi)
      have hsum := greedyDigits_sum (k + 1) (greedyPred (k + 1) R) hk1 hpred.1 hpred.2.1
      omega

/-- Unfolding: the last digit of `greedyDigits (k+1) R` is the greedy step. -/
theorem greedyDigits_cons_last (k R : Nat) (hk : 1 ≤ k) :
    greedyDigits (k + 1) R =
      greedyDigits k (greedyPred k R) ++ [R - greedyPred k R] := by
  cases k with
  | zero => omega
  | succ m =>
    exact greedyDigits_succ m R

/-- Every greedy step is admissible: the prefix sums to a point of `I_k`
and the last digit satisfies `2S+1 ≤ d ≤ 3S+1`. -/
theorem greedyDigits_last_admissible (k R : Nat) (hk : 1 ≤ k)
    (hlo : Ilo (k + 1) ≤ R) (hhi : R ≤ Ihi (k + 1)) :
    Ilo k ≤ greedyPred k R ∧
    greedyPred k R ≤ Ihi k ∧
    2 * greedyPred k R + 1 ≤ R - greedyPred k R ∧
    R - greedyPred k R ≤ 3 * greedyPred k R + 1 ∧
    greedyDigits (k + 1) R =
      greedyDigits k (greedyPred k R) ++ [R - greedyPred k R] := by
  have h := greedyPred_spec k R hk hlo hhi
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, greedyDigits_cons_last k R hk⟩

/-- Remaining digits after a prefix of sum `S` obey the bounds
`2S+1 ≤ d ≤ 3S+1` at each step. -/
def AdmissibleFrom (S : Nat) : List Nat → Prop
  | [] => True
  | d :: ds => 2 * S + 1 ≤ d ∧ d ≤ 3 * S + 1 ∧ AdmissibleFrom (S + d) ds

/-- A nonempty list is admissible if it starts with `1` and the tail
is admissible from prefix sum `1`. -/
def IsAdmissible : List Nat → Prop
  | [] => False
  | d :: rest => d = 1 ∧ AdmissibleFrom 1 rest

theorem IsAdmissible_one : IsAdmissible [1] := by
  simp [IsAdmissible, AdmissibleFrom]

theorem AdmissibleFrom_snoc (S : Nat) :
    ∀ ds T d,
      AdmissibleFrom S ds →
      S + sumList ds = T →
      2 * T + 1 ≤ d →
      d ≤ 3 * T + 1 →
      AdmissibleFrom S (ds ++ [d])
  | [], T, d, _, hsum, hdlo, hdhi => by
      simp [AdmissibleFrom, sumList] at *
      omega
  | x :: xs, T, d, h, hsum, hdlo, hdhi => by
      simp [AdmissibleFrom] at h ⊢
      refine ⟨h.1, h.2.1, ?_⟩
      have hsum' : (S + x) + sumList xs = T := by
        simp [sumList] at hsum
        omega
      exact AdmissibleFrom_snoc (S + x) xs T d h.2.2 hsum' hdlo hdhi

theorem IsAdmissible_snoc (ds : List Nat) (S d : Nat)
    (hds : IsAdmissible ds) (hsum : sumList ds = S)
    (hdlo : 2 * S + 1 ≤ d) (hdhi : d ≤ 3 * S + 1) :
    IsAdmissible (ds ++ [d]) := by
  match ds with
  | [] =>
    cases hds
  | x :: xs =>
    simp [IsAdmissible] at hds ⊢
    refine ⟨hds.1, ?_⟩
    have hT : 1 + sumList xs = S := by
      simp [sumList] at hsum
      omega
    exact AdmissibleFrom_snoc 1 xs S d hds.2 hT hdlo hdhi

/-- The greedy list for `R ∈ I_k` is an admissible digit sequence. -/
theorem greedyDigits_admissible :
    ∀ k R, 1 ≤ k → Ilo k ≤ R → R ≤ Ihi k → IsAdmissible (greedyDigits k R)
  | 0, R, hk, _, _ => by omega
  | 1, R, _, hlo, hhi => by
      have hIlo : Ilo 1 = 1 := Ilo_one
      have hIhi : Ihi 1 = 1 := Ihi_one
      have : R = 1 := by omega
      simp [greedyDigits, IsAdmissible, AdmissibleFrom]
  | k + 2, R, hk, hlo, hhi => by
      rw [greedyDigits_succ]
      have hk1 : 1 ≤ k + 1 := by omega
      have hpred := greedyPred_spec (k + 1) R hk1 (by simpa using hlo) (by simpa using hhi)
      have hds := greedyDigits_admissible (k + 1) (greedyPred (k + 1) R)
        hk1 hpred.1 hpred.2.1
      have hsum := greedyDigits_sum (k + 1) (greedyPred (k + 1) R)
        hk1 hpred.1 hpred.2.1
      exact IsAdmissible_snoc _ _ _ hds hsum hpred.2.2.1 hpred.2.2.2

end Sat3
