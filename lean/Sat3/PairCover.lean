import Sat3.PairBound
import Sat3.Sound

/-
  Proposition 2.2, covering half: every point of [n] lies in A or
  among the three third-points of some pair from A.
-/

namespace Sat3

def pairThirds (x y : Int) : List Int :=
  [2 * y - x, 2 * x - y, (x + y) / 2]

theorem pairThirds_of_forms (x y t : Int) (h : FormsAP3 x y t) :
    t ∈ pairThirds x y := by
  rcases h with ⟨_, _, _, hor⟩
  rcases hor with h1 | h2 | h3
  · have : t = 2 * x - y := by omega
    simp [pairThirds, this]
  · have : t = 2 * y - x := by omega
    simp [pairThirds, this]
  · have hdiv : (x + y) / 2 = t := by
      have : x + y = 2 * t := by omega
      rw [this]
      exact Int.mul_ediv_cancel_left t (by decide : (2 : Int) ≠ 0)
    simp [pairThirds, hdiv]

def pairsCover : List Int → List Int
  | [] => []
  | x :: xs =>
      List.flatMap (pairThirds x) xs ++ pairsCover xs

def coverList (A : List Int) : List Int :=
  A ++ pairsCover A

theorem pairsCover_of_mem :
    ∀ A x y t,
      x ∈ A → y ∈ A → x ≠ y → t ∈ pairThirds x y → t ∈ pairsCover A
  | [], _, _, _, hx, _, _, _ => by cases hx
  | a :: xs, x, y, t, hx, hy, hne, ht => by
      simp [pairsCover]
      cases (List.mem_cons.mp hx) with
      | inl hx =>
        subst x
        cases (List.mem_cons.mp hy) with
        | inl hy =>
          subst y
          exact (hne rfl).elim
        | inr hy =>
          exact Or.inl ⟨y, hy, ht⟩
      | inr hx =>
        cases (List.mem_cons.mp hy) with
        | inl hy =>
          subst y
          have ht' : t ∈ pairThirds a x := by
            simp [pairThirds] at ht ⊢
            rcases ht with h | h | h
            · exact Or.inr (Or.inl h)
            · exact Or.inl h
            · have : (x + a) / 2 = (a + x) / 2 := by
                rw [Int.add_comm]
              exact Or.inr (Or.inr (this ▸ h))
          exact Or.inl ⟨x, hx, ht'⟩
        | inr hy =>
          exact Or.inr (pairsCover_of_mem xs x y t hx hy hne ht)

theorem coverList_of_completed (A : List Int) (t : Int)
    (h : CompletedBy (ofIntList A) t) : t ∈ coverList A := by
  obtain ⟨x, y, hx, hy, hf⟩ := h
  have hne : x ≠ y := hf.1
  have ht := pairThirds_of_forms x y t hf
  have : t ∈ pairsCover A := pairsCover_of_mem A x y t hx hy hne ht
  exact List.mem_append.mpr (Or.inr this)

/-- Every point of `[n]` is either in `A` or among the three third
points of some pair from `A`. -/
theorem coverList_covers (n : Nat) (A : List Int)
    (h : MaximalAP3Free n (ofIntList A)) :
    ∀ t, InIcc1 n t → t ∈ coverList A := by
  intro t ht
  have hcov := h.2.2 t ht
  cases hcov with
  | inl hA =>
    exact List.mem_append.mpr (Or.inl hA)
  | inr hC =>
    exact coverList_of_completed A t hC

theorem nodup_subset_length :
    ∀ (S L : List Int),
      S.Nodup → (∀ x, x ∈ S → x ∈ L) → S.length ≤ L.length
  | [], L, _, _ => Nat.zero_le _
  | a :: S, L, hN, hsub => by
      have ⟨hna, hNS⟩ := List.nodup_cons.mp hN
      have ha : a ∈ L := hsub a (by simp)
      have hsub' : ∀ x, x ∈ S → x ∈ L.erase a := by
        intro x hx
        have hxL : x ∈ L := hsub x (by simp [hx])
        have hne : x ≠ a := by
          intro h
          subst x
          exact hna hx
        exact (List.mem_erase_of_ne hne).mpr hxL
      have ih := nodup_subset_length S (L.erase a) hNS hsub'
      have hlen : (L.erase a).length = L.length - 1 :=
        List.length_erase_of_mem ha
      have : S.length + 1 ≤ L.length := by
        have : S.length ≤ L.length - 1 := by
          rw [← hlen]
          exact ih
        have hpos : 1 ≤ L.length := by
          cases L with
          | nil => cases ha
          | cons _ _ => simp
        omega
      simpa using this

def intervalList (n : Nat) : List Int :=
  (List.range n).map fun i : Nat => (i : Int) + 1

theorem intervalList_length (n : Nat) : (intervalList n).length = n := by
  simp [intervalList]

theorem intervalList_nodup (n : Nat) : (intervalList n).Nodup := by
  unfold intervalList
  induction n with
  | zero => simp
  | succ n ih =>
    have hrange : List.range (n + 1) = List.range n ++ [n] :=
      List.range_succ
    simp [hrange, List.map_append]
    refine List.nodup_append.mpr ⟨ih, ?_, ?_⟩
    · simp
    · intro a ha b hb
      have hb' : b = (n : Int) + 1 := by
        simp at hb
        exact hb
      intro h
      subst b
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
      have : i < n := List.mem_range.mp hi
      omega

/-- Covering injection: `[n]` injects into `coverList A`. -/
theorem interval_le_cover (n : Nat) (A : List Int)
    (h : MaximalAP3Free n (ofIntList A)) :
    n ≤ (coverList A).length := by
  have hcov := coverList_covers n A h
  have hsub : ∀ x, x ∈ intervalList n → x ∈ coverList A := by
    intro x hx
    have : InIcc1 n x := by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      have : i < n := List.mem_range.mp hi
      simp [InIcc1]
      omega
    exact hcov x this
  have hlen := nodup_subset_length (intervalList n) (coverList A)
    (intervalList_nodup n) hsub
  have hL : (intervalList n).length = n := intervalList_length n
  omega

theorem even_succ_mul (m : Nat) : ((m + 1) * m) % 2 = 0 := by
  have : m % 2 = 0 ∨ m % 2 = 1 := Nat.mod_two_eq_zero_or_one m
  rcases this with h | h
  · rw [Nat.mul_comm, Nat.mul_mod, h]; simp
  · have : (m + 1) % 2 = 0 := by omega
    rw [Nat.mul_mod, this]; simp

theorem two_mul_binom (m : Nat) : 2 * ((m + 1) * m / 2) = (m + 1) * m :=
  Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero (even_succ_mul m))

theorem binom_succ (m : Nat) :
    (m + 1) * m / 2 = m + m * (m - 1) / 2 := by
  cases m with
  | zero => simp
  | succ m =>
    -- goal: (m+2)(m+1)/2 = (m+1) + (m+1)m/2
    have hL : 2 * ((m + 2) * (m + 1) / 2) = (m + 2) * (m + 1) :=
      two_mul_binom (m + 1)
    have hR : 2 * ((m + 1) * m / 2) = (m + 1) * m := two_mul_binom m
    have hexp : (m + 2) * (m + 1) = 2 * (m + 1) + (m + 1) * m := by
      calc
        (m + 2) * (m + 1) = m * (m + 1) + 2 * (m + 1) := by
          rw [Nat.succ_mul, Nat.succ_mul]
          omega
        _ = 2 * (m + 1) + (m + 1) * m := by
          rw [Nat.mul_comm m]
          omega
    have : 2 * ((m + 2) * (m + 1) / 2) =
        2 * (m + 1) + 2 * ((m + 1) * m / 2) := by
      rw [hL, hR, hexp]
    have hcancel :
        (m + 2) * (m + 1) / 2 = (m + 1) + (m + 1) * m / 2 := by
      have hleft := this
      have : 2 * ((m + 2) * (m + 1) / 2) =
          2 * ((m + 1) + (m + 1) * m / 2) := by
        have : 2 * (m + 1) + 2 * ((m + 1) * m / 2) =
            2 * ((m + 1) + (m + 1) * m / 2) := by
          omega
        omega
      exact Nat.mul_left_cancel (by decide : 0 < 2) this
    simpa using hcancel

theorem pairThirds_length (x y : Int) : (pairThirds x y).length = 3 := rfl

theorem flatMap_pairThirds_length (x : Int) :
    ∀ xs, (List.flatMap (pairThirds x) xs).length = 3 * xs.length
  | [] => rfl
  | y :: ys => by
      have ih := flatMap_pairThirds_length x ys
      simp [List.flatMap_cons, List.length_append, pairThirds_length, ih]
      omega

theorem pairsCover_length :
    ∀ A, (pairsCover A).length = 3 * (A.length * (A.length - 1) / 2)
  | [] => by simp [pairsCover]
  | x :: xs => by
      have ih := pairsCover_length xs
      have hflat := flatMap_pairThirds_length x xs
      have hlen : (pairsCover (x :: xs)).length =
          3 * xs.length + 3 * (xs.length * (xs.length - 1) / 2) := by
        simp [pairsCover, List.length_append, hflat, ih]
      have hb := binom_succ xs.length
      have hgoal : 3 * xs.length + 3 * (xs.length * (xs.length - 1) / 2) =
          3 * ((xs.length + 1) * xs.length / 2) := by
        rw [hb]
        omega
      have hA : (x :: xs).length = xs.length + 1 := rfl
      calc
        (pairsCover (x :: xs)).length
            = 3 * xs.length + 3 * (xs.length * (xs.length - 1) / 2) := hlen
        _ = 3 * ((xs.length + 1) * xs.length / 2) := hgoal
        _ = 3 * ((x :: xs).length * ((x :: xs).length - 1) / 2) := by
            rw [hA]
            have : xs.length + 1 - 1 = xs.length := Nat.add_sub_cancel xs.length 1
            rw [this]

theorem coverList_length (A : List Int) :
    (coverList A).length = pairBound A.length := by
  unfold coverList pairBound
  rw [List.length_append, pairsCover_length]

/-- Proposition 2.2: a maximal 3-AP-free list of length `k` forces
`n ≤ pairBound k`. -/
theorem pairBound_of_maximal (n : Nat) (A : List Int)
    (h : MaximalAP3Free n (ofIntList A)) :
    n ≤ pairBound A.length := by
  have h1 := interval_le_cover n A h
  have h2 := coverList_length A
  omega

end Sat3
