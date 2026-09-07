import Sat3.Sound
import Sat3.Sort

/-
  Strictly increasing k-tuples in [n], for exhaustive small-k
  maximality checks. Native-decide on combinations, not n^k.
-/

namespace Sat3

/-- Increasing `k`-tuples from `[lo, n]`. `lo` is a 1-based lower bound. -/
def incFrom (lo n : Nat) : Nat → List (List Int)
  | 0 => [[]]
  | k + 1 =>
      (List.range n).flatMap fun (i : Nat) =>
        if decide (lo ≤ i + 1) then
          (incFrom (i + 2) n k).map fun rest =>
            ((i : Int) + 1) :: rest
        else
          []

def incK (n k : Nat) : List (List Int) :=
  incFrom 1 n k

def anyMaximalInc (n k : Nat) : Bool :=
  (incK n k).any fun A => maximal n A

theorem anyMaximal4inc_18 : anyMaximalInc 18 4 = false := by native_decide
theorem anyMaximal5inc_18 : anyMaximalInc 18 5 = false := by native_decide
theorem anyMaximal4inc_19 : anyMaximalInc 19 4 = false := by native_decide
theorem anyMaximal5inc_19 : anyMaximalInc 19 5 = false := by native_decide
theorem anyMaximal4inc_20 : anyMaximalInc 20 4 = false := by native_decide
theorem anyMaximal5inc_20 : anyMaximalInc 20 5 = false := by native_decide
theorem anyMaximal4inc_21 : anyMaximalInc 21 4 = false := by native_decide
theorem anyMaximal5inc_21 : anyMaximalInc 21 5 = false := by native_decide
theorem anyMaximal4inc_22 : anyMaximalInc 22 4 = false := by native_decide
theorem anyMaximal5inc_22 : anyMaximalInc 22 5 = false := by native_decide
theorem anyMaximal5inc_23 : anyMaximalInc 23 5 = false := by native_decide
theorem anyMaximal5inc_24 : anyMaximalInc 24 5 = false := by native_decide
theorem anyMaximal5inc_25 : anyMaximalInc 25 5 = false := by native_decide
theorem anyMaximal5inc_26 : anyMaximalInc 26 5 = false := by native_decide

/-- If `y :: ys` is strictly sorted and `t` is in the tail, then `y ≤ t`. -/
theorem le_of_mem_strictSorted (y : Int) :
    ∀ ys t, StrictSorted (y :: ys) → MemInt ys t → y ≤ t
  | [], t, _, ht => by cases ht
  | z :: zs, t, hS, ht => by
      have hyz : y < z := hS.1
      cases ht with
      | inl h => omega
      | inr h =>
        have := le_of_mem_strictSorted z zs t hS.2 h
        omega

theorem mem_incFrom_step (lo n k i : Nat) (rest : List Int)
    (hlo : lo ≤ i + 1) (hi : i < n)
    (hrest : rest ∈ incFrom (i + 2) n k) :
    ((i : Int) + 1) :: rest ∈ incFrom lo n (k + 1) := by
  unfold incFrom
  refine List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, ?_⟩
  have hdec : decide (lo ≤ i + 1) = true := decide_eq_true hlo
  rw [hdec]
  simp
  exact hrest

theorem incFrom_has :
    ∀ (k lo n : Nat) (P : List Int),
      P.length = k →
      StrictSorted P →
      (∀ t, MemInt P t → InIcc1 n t) →
      (∀ t, MemInt P t → (lo : Int) ≤ t) →
      P ∈ incFrom lo n k
  | 0, lo, n, P, hlen, _, _, _ => by
      match P with
      | [] => simp [incFrom]
      | _ :: _ => cases hlen
  | k + 1, lo, n, [], hlen, _, _, _ => by cases hlen
  | k + 1, lo, n, x :: xs, hlen, hS, hsupp, hlo => by
      have hx : InIcc1 n x := hsupp x (Or.inl rfl)
      obtain ⟨i, hi, hix⟩ := range_mem n x hx
      have hi_lt : i < n := List.mem_range.mp hi
      have hlen' : xs.length = k := by simp at hlen; exact hlen
      have hS' : StrictSorted xs := by
        match xs with
        | [] => trivial
        | _ :: _ => exact hS.2
      have hsupp' : ∀ t, MemInt xs t → InIcc1 n t := by
        intro t ht
        exact hsupp t (Or.inr ht)
      have hxlo : (lo : Int) ≤ x := hlo x (Or.inl rfl)
      have hloi : lo ≤ i + 1 := by
        have : (i : Int) + 1 = x := hix
        have : (lo : Int) ≤ (i : Int) + 1 := by omega
        exact Int.ofNat_le.mp this
      have hlo' : ∀ t, MemInt xs t → ((i + 2 : Nat) : Int) ≤ t := by
        intro t ht
        have hxt : x < t := by
          match xs with
          | [] => cases ht
          | y :: ys =>
            have hxy : x < y := hS.1
            cases ht with
            | inl h => omega
            | inr h =>
              have hy_le : y ≤ t := le_of_mem_strictSorted y ys t hS.2 h
              omega
        have : (i : Int) + 1 = x := hix
        omega
      have ih := incFrom_has k (i + 2) n xs hlen' hS' hsupp' hlo'
      have hxeq : x = (i : Int) + 1 := hix.symm
      simpa [hxeq] using mem_incFrom_step lo n k i xs hloi hi_lt ih

theorem anyMaximalInc_of_sorted (n k : Nat) (P : List Int)
    (hlen : P.length = k)
    (hS : StrictSorted P)
    (h : MaximalAP3Free n (ofIntList P)) :
    anyMaximalInc n k = true := by
  have hsupp : ∀ t, MemInt P t → InIcc1 n t := by
    intro t ht
    exact h.1 t ((ofIntList_of_memInt P t).mpr ht)
  have hlo : ∀ t, MemInt P t → (1 : Int) ≤ t := by
    intro t ht
    exact (hsupp t ht).1
  have hmem := incFrom_has k 1 n P hlen hS hsupp hlo
  have hmax : maximal n P = true := maximal_complete n P h
  unfold anyMaximalInc incK
  exact List.any_eq_true.mpr ⟨P, hmem, hmax⟩

theorem anyMaximalInc_of_HasMaximal (n k : Nat)
    (h : HasMaximalOfSize n k) :
    anyMaximalInc n k = true := by
  obtain ⟨A, P, hA, hN, hlen, hiff⟩ := h
  have hP := MaximalAP3Free_ofIntList n P A hA hiff
  have hsort := MaximalAP3Free_sort n P hP
  have hlen' : (sortList P).length = k := by
    rw [length_sortList P, hlen]
  have hS := strictSorted_sortList P hN
  exact anyMaximalInc_of_sorted n k (sortList P) hlen' hS hsort

theorem not_HasMaximalOfSize_of_inc (n k : Nat)
    (hfalse : anyMaximalInc n k = false) :
    ¬ HasMaximalOfSize n k := by
  intro h
  have := anyMaximalInc_of_HasMaximal n k h
  exact Bool.false_ne_true (hfalse.symm.trans this)

theorem nodupInt_cert18 : NodupInt [1, 2, 4, 8, 9, 11] := by
  refine ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, trivial⟩⟩⟩⟩⟩⟩
  · intro h
    rcases h with h | h | h | h | h | h
    · omega
    · omega
    · omega
    · omega
    · omega
    · cases h
  · intro h
    rcases h with h | h | h | h | h
    · omega
    · omega
    · omega
    · omega
    · cases h
  · intro h
    rcases h with h | h | h | h
    · omega
    · omega
    · omega
    · cases h
  · intro h
    rcases h with h | h | h
    · omega
    · omega
    · cases h
  · intro h
    rcases h with h | h
    · omega
    · cases h
  · intro h
    cases h

theorem HasMaximalOfSize_18_6 : HasMaximalOfSize 18 6 :=
  ⟨ofIntList [1, 2, 4, 8, 9, 11], [1, 2, 4, 8, 9, 11],
    maximal_of_cert_n18, nodupInt_cert18, rfl,
    ofIntList_of_memInt [1, 2, 4, 8, 9, 11]⟩

theorem sat3_eq_eighteen : sat3 18 (by decide) = 6 := by
  have hspec := sat3_spec 18 (by decide)
  have hle : sat3 18 (by decide) ≤ 6 :=
    hspec.2.1 6 HasMaximalOfSize_18_6
  have hge : 6 ≤ sat3 18 (by decide) := by
    have hk := hspec.2.2.2.1
    have hcases :
        sat3 18 (by decide) = 1 ∨ sat3 18 (by decide) = 2 ∨
        sat3 18 (by decide) = 3 ∨ sat3 18 (by decide) = 4 ∨
        sat3 18 (by decide) = 5 ∨ 6 ≤ sat3 18 (by decide) := by omega
    rcases hcases with h1 | h2 | h3 | h4 | h5 | h6
    · have hsz : HasMaximalOfSize 18 1 := by simpa [h1] using hspec.1
      have hpb := HasMaximalOfSize_pairBound 18 1 hsz
      have : pairBound 1 = 1 := by simp [pairBound]
      omega
    · have hsz : HasMaximalOfSize 18 2 := by simpa [h2] using hspec.1
      exact (not_HasMaximalOfSize_2_of_gt_five 18 (by decide) hsz).elim
    · have hsz : HasMaximalOfSize 18 3 := by simpa [h3] using hspec.1
      exact (not_HasMaximalOfSize_3_of_gt_twelve 18 (by decide) hsz).elim
    · have hsz : HasMaximalOfSize 18 4 := by simpa [h4] using hspec.1
      exact (not_HasMaximalOfSize_of_inc 18 4 anyMaximal4inc_18 hsz).elim
    · have hsz : HasMaximalOfSize 18 5 := by simpa [h5] using hspec.1
      exact (not_HasMaximalOfSize_of_inc 18 5 anyMaximal5inc_18 hsz).elim
    · exact h6
  omega



theorem nodupInt_cert19 : NodupInt [1, 2, 4, 8, 17, 18] := by
  refine ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, trivial⟩⟩⟩⟩⟩⟩
  · intro h; rcases h with h | h | h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h <;> first | omega | cases h
  · intro h; cases h

theorem nodupInt_cert20 : NodupInt [1, 2, 4, 9, 11, 15] := by
  refine ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, trivial⟩⟩⟩⟩⟩⟩
  · intro h; rcases h with h | h | h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h <;> first | omega | cases h
  · intro h; cases h

theorem HasMaximalOfSize_19_6 : HasMaximalOfSize 19 6 :=
  ⟨ofIntList [1, 2, 4, 8, 17, 18], [1, 2, 4, 8, 17, 18],
    maximal_of_cert_n19, nodupInt_cert19, rfl,
    ofIntList_of_memInt [1, 2, 4, 8, 17, 18]⟩

theorem HasMaximalOfSize_20_6 : HasMaximalOfSize 20 6 :=
  ⟨ofIntList [1, 2, 4, 9, 11, 15], [1, 2, 4, 9, 11, 15],
    maximal_of_cert_n20, nodupInt_cert20, rfl,
    ofIntList_of_memInt [1, 2, 4, 9, 11, 15]⟩

theorem sat3_eq_six_of (n : Nat) (hn : 1 ≤ n) (hn13 : 13 ≤ n)
    (h4 : anyMaximalInc n 4 = false)
    (h5 : anyMaximalInc n 5 = false)
    (h6 : HasMaximalOfSize n 6) :
    sat3 n hn = 6 := by
  have hspec := sat3_spec n hn
  have hle : sat3 n hn ≤ 6 := hspec.2.1 6 h6
  have hge : 6 ≤ sat3 n hn := by
    have hk := hspec.2.2.2.1
    have hcases :
        sat3 n hn = 1 ∨ sat3 n hn = 2 ∨ sat3 n hn = 3 ∨
        sat3 n hn = 4 ∨ sat3 n hn = 5 ∨ 6 ≤ sat3 n hn := by omega
    rcases hcases with h1 | h2 | h3 | h4' | h5' | h6'
    · have hsz : HasMaximalOfSize n 1 := by simpa [h1] using hspec.1
      have hpb := HasMaximalOfSize_pairBound n 1 hsz
      have : pairBound 1 = 1 := by simp [pairBound]
      omega
    · have hsz : HasMaximalOfSize n 2 := by simpa [h2] using hspec.1
      exact (not_HasMaximalOfSize_2_of_gt_five n (Nat.le_trans (by decide : 6 ≤ 13) hn13) hsz).elim
    · have hsz : HasMaximalOfSize n 3 := by simpa [h3] using hspec.1
      exact (not_HasMaximalOfSize_3_of_gt_twelve n hn13 hsz).elim
    · have hsz : HasMaximalOfSize n 4 := by simpa [h4'] using hspec.1
      exact (not_HasMaximalOfSize_of_inc n 4 h4 hsz).elim
    · have hsz : HasMaximalOfSize n 5 := by simpa [h5'] using hspec.1
      exact (not_HasMaximalOfSize_of_inc n 5 h5 hsz).elim
    · exact h6'
  omega

theorem sat3_eq_nineteen : sat3 19 (by decide) = 6 :=
  sat3_eq_six_of 19 (by decide) (by decide)
    anyMaximal4inc_19 anyMaximal5inc_19 HasMaximalOfSize_19_6

theorem sat3_eq_twenty : sat3 20 (by decide) = 6 :=
  sat3_eq_six_of 20 (by decide) (by decide)
    anyMaximal4inc_20 anyMaximal5inc_20 HasMaximalOfSize_20_6

theorem pairBound_four : pairBound 4 = 22 := by
  simp [pairBound]

theorem not_HasMaximalOfSize_4_of_gt_twentytwo (n : Nat) (hn : 23 ≤ n) :
    ¬ HasMaximalOfSize n 4 := by
  intro h
  have := HasMaximalOfSize_pairBound n 4 h
  have : pairBound 4 = 22 := pairBound_four
  omega

theorem nodupInt_cert21 : NodupInt [1, 2, 4, 9, 11, 15] :=
  nodupInt_cert20

theorem nodupInt_cert22 : NodupInt [1, 2, 10, 11, 15, 16] := by
  refine ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, trivial⟩⟩⟩⟩⟩⟩
  · intro h; rcases h with h | h | h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h <;> first | omega | cases h
  · intro h; cases h

theorem nodupInt_cert23 : NodupInt [2, 3, 11, 12, 16, 17] := by
  refine ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, trivial⟩⟩⟩⟩⟩⟩
  · intro h; rcases h with h | h | h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h <;> first | omega | cases h
  · intro h; cases h

theorem nodupInt_cert24 : NodupInt [4, 5, 7, 12, 14, 18] := by
  refine ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, trivial⟩⟩⟩⟩⟩⟩
  · intro h; rcases h with h | h | h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h <;> first | omega | cases h
  · intro h; cases h

theorem nodupInt_cert25 : NodupInt [5, 6, 8, 13, 15, 19] := by
  refine ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, trivial⟩⟩⟩⟩⟩⟩
  · intro h; rcases h with h | h | h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h <;> first | omega | cases h
  · intro h; cases h

theorem nodupInt_cert26 : NodupInt [8, 10, 11, 15, 17, 18] := by
  refine ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, trivial⟩⟩⟩⟩⟩⟩
  · intro h; rcases h with h | h | h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h <;> first | omega | cases h
  · intro h; cases h

theorem HasMaximalOfSize_21_6 : HasMaximalOfSize 21 6 :=
  ⟨ofIntList [1, 2, 4, 9, 11, 15], [1, 2, 4, 9, 11, 15],
    maximal_of_cert_n21, nodupInt_cert21, rfl,
    ofIntList_of_memInt [1, 2, 4, 9, 11, 15]⟩

theorem HasMaximalOfSize_22_6 : HasMaximalOfSize 22 6 :=
  ⟨ofIntList [1, 2, 10, 11, 15, 16], [1, 2, 10, 11, 15, 16],
    maximal_of_cert_n22, nodupInt_cert22, rfl,
    ofIntList_of_memInt [1, 2, 10, 11, 15, 16]⟩

theorem HasMaximalOfSize_23_6 : HasMaximalOfSize 23 6 :=
  ⟨ofIntList [2, 3, 11, 12, 16, 17], [2, 3, 11, 12, 16, 17],
    maximal_of_cert_n23, nodupInt_cert23, rfl,
    ofIntList_of_memInt [2, 3, 11, 12, 16, 17]⟩

theorem HasMaximalOfSize_24_6 : HasMaximalOfSize 24 6 :=
  ⟨ofIntList [4, 5, 7, 12, 14, 18], [4, 5, 7, 12, 14, 18],
    maximal_of_cert_n24, nodupInt_cert24, rfl,
    ofIntList_of_memInt [4, 5, 7, 12, 14, 18]⟩

theorem HasMaximalOfSize_25_6 : HasMaximalOfSize 25 6 :=
  ⟨ofIntList [5, 6, 8, 13, 15, 19], [5, 6, 8, 13, 15, 19],
    maximal_of_cert_n25, nodupInt_cert25, rfl,
    ofIntList_of_memInt [5, 6, 8, 13, 15, 19]⟩

theorem HasMaximalOfSize_26_6 : HasMaximalOfSize 26 6 :=
  ⟨ofIntList [8, 10, 11, 15, 17, 18], [8, 10, 11, 15, 17, 18],
    maximal_of_cert_n26, nodupInt_cert26, rfl,
    ofIntList_of_memInt [8, 10, 11, 15, 17, 18]⟩

theorem sat3_eq_six_of_pair4 (n : Nat) (hn : 1 ≤ n) (hn23 : 23 ≤ n)
    (h5 : anyMaximalInc n 5 = false)
    (h6 : HasMaximalOfSize n 6) :
    sat3 n hn = 6 := by
  have hspec := sat3_spec n hn
  have hle : sat3 n hn ≤ 6 := hspec.2.1 6 h6
  have hge : 6 ≤ sat3 n hn := by
    have hk := hspec.2.2.2.1
    have hcases :
        sat3 n hn = 1 ∨ sat3 n hn = 2 ∨ sat3 n hn = 3 ∨
        sat3 n hn = 4 ∨ sat3 n hn = 5 ∨ 6 ≤ sat3 n hn := by omega
    rcases hcases with h1 | h2 | h3 | h4' | h5' | h6'
    · have hsz : HasMaximalOfSize n 1 := by simpa [h1] using hspec.1
      have hpb := HasMaximalOfSize_pairBound n 1 hsz
      have : pairBound 1 = 1 := by simp [pairBound]
      omega
    · have hsz : HasMaximalOfSize n 2 := by simpa [h2] using hspec.1
      exact (not_HasMaximalOfSize_2_of_gt_five n (Nat.le_trans (by decide : 6 ≤ 23) hn23) hsz).elim
    · have hsz : HasMaximalOfSize n 3 := by simpa [h3] using hspec.1
      exact (not_HasMaximalOfSize_3_of_gt_twelve n (Nat.le_trans (by decide : 13 ≤ 23) hn23) hsz).elim
    · have hsz : HasMaximalOfSize n 4 := by simpa [h4'] using hspec.1
      exact (not_HasMaximalOfSize_4_of_gt_twentytwo n hn23 hsz).elim
    · have hsz : HasMaximalOfSize n 5 := by simpa [h5'] using hspec.1
      exact (not_HasMaximalOfSize_of_inc n 5 h5 hsz).elim
    · exact h6'
  omega

theorem sat3_eq_twentyone : sat3 21 (by decide) = 6 :=
  sat3_eq_six_of 21 (by decide) (by decide)
    anyMaximal4inc_21 anyMaximal5inc_21 HasMaximalOfSize_21_6

theorem sat3_eq_twentytwo : sat3 22 (by decide) = 6 :=
  sat3_eq_six_of 22 (by decide) (by decide)
    anyMaximal4inc_22 anyMaximal5inc_22 HasMaximalOfSize_22_6

theorem sat3_eq_twentythree : sat3 23 (by decide) = 6 :=
  sat3_eq_six_of_pair4 23 (by decide) (by decide)
    anyMaximal5inc_23 HasMaximalOfSize_23_6

theorem sat3_eq_twentyfour : sat3 24 (by decide) = 6 :=
  sat3_eq_six_of_pair4 24 (by decide) (by decide)
    anyMaximal5inc_24 HasMaximalOfSize_24_6

theorem sat3_eq_twentyfive : sat3 25 (by decide) = 6 :=
  sat3_eq_six_of_pair4 25 (by decide) (by decide)
    anyMaximal5inc_25 HasMaximalOfSize_25_6

theorem sat3_eq_twentysix : sat3 26 (by decide) = 6 :=
  sat3_eq_six_of_pair4 26 (by decide) (by decide)
    anyMaximal5inc_26 HasMaximalOfSize_26_6

end Sat3
