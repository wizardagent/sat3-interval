import Sat3.Free

/-
  Recursive 3-AP-free search for maximality, without materialising
  the list of all free k-sets. Native-decide on DFS, not on C(n,k).
-/

namespace Sat3

/-- DFS: some increasing free completion of `pref` of leftover length `k`
is maximal in `[n]`. -/
def existsMax (lo n : Nat) (pref : List Int) : Nat → Bool
  | 0 => maximal n pref
  | k + 1 =>
      (List.range n).any fun (i : Nat) =>
        if decide (lo ≤ i + 1) then
          if blocks pref ((i : Int) + 1) then
            false
          else
            existsMax (i + 2) n (pref ++ [((i : Int) + 1)]) k
        else
          false

def anyMaximalSearch (n k : Nat) : Bool :=
  existsMax 1 n [] k

theorem existsMax_step (lo n k i : Nat) (pref : List Int)
    (hlo : lo ≤ i + 1) (hi : i < n)
    (hblk : blocks pref ((i : Int) + 1) = false)
    (hrest : existsMax (i + 2) n (pref ++ [((i : Int) + 1)]) k = true) :
    existsMax lo n pref (k + 1) = true := by
  unfold existsMax
  refine List.any_eq_true.mpr ⟨i, List.mem_range.mpr hi, ?_⟩
  have hdec : decide (lo ≤ i + 1) = true := decide_eq_true hlo
  rw [hdec]
  simp [hblk]
  exact hrest

theorem existsMax_has :
    ∀ (k lo n : Nat) (pref P : List Int),
      P.length = k →
      StrictSorted P →
      AP3Free (ofIntList (pref ++ P)) →
      (∀ t, MemInt P t → InIcc1 n t) →
      (∀ t, MemInt P t → (lo : Int) ≤ t) →
      maximal n (pref ++ P) = true →
      existsMax lo n pref k = true
  | 0, lo, n, pref, P, hlen, _, _, _, _, hmax => by
      match P with
      | [] => simpa [existsMax] using hmax
      | _ :: _ => cases hlen
  | k + 1, lo, n, pref, [], hlen, _, _, _, _, _ => by cases hlen
  | k + 1, lo, n, pref, x :: xs, hlen, hS, hfree, hsupp, hlo, hmax => by
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
      have hloi : lo ≤ i + 1 := by
        have : (i : Int) + 1 = x := hix
        have : (lo : Int) ≤ (i : Int) + 1 := by
          have := hlo x (Or.inl rfl)
          omega
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
      have hfree' : AP3Free (ofIntList ((pref ++ [x]) ++ xs)) := by
        have heq : pref ++ (x :: xs) = (pref ++ [x]) ++ xs :=
          (List.append_assoc pref [x] xs).symm
        rw [← heq]
        exact hfree
      have hmax' : maximal n ((pref ++ [x]) ++ xs) = true := by
        have heq : pref ++ (x :: xs) = (pref ++ [x]) ++ xs :=
          (List.append_assoc pref [x] xs).symm
        rw [← heq]
        exact hmax
      have ih :=
        existsMax_has k (i + 2) n (pref ++ [x]) xs hlen' hS' hfree' hsupp' hlo' hmax'
      have hblk : blocks pref x = false :=
        blocks_eq_false_of_AP3Free pref x xs hfree
      have hxeq : x = (i : Int) + 1 := hix.symm
      have hblk' : blocks pref ((i : Int) + 1) = false := by simpa [hxeq] using hblk
      have ih' : existsMax (i + 2) n (pref ++ [((i : Int) + 1)]) k = true := by
        simpa [hxeq] using ih
      exact existsMax_step lo n k i pref hloi hi_lt hblk' ih'

theorem anyMaximalSearch_of_sorted (n k : Nat) (P : List Int)
    (hlen : P.length = k)
    (hS : StrictSorted P)
    (h : MaximalAP3Free n (ofIntList P)) :
    anyMaximalSearch n k = true := by
  have hsupp : ∀ t, MemInt P t → InIcc1 n t := by
    intro t ht
    exact h.1 t ((ofIntList_of_memInt P t).mpr ht)
  have hlo : ∀ t, MemInt P t → (1 : Int) ≤ t := by
    intro t ht
    exact (hsupp t ht).1
  have hfree : AP3Free (ofIntList ([] ++ P)) := by
    simpa using h.2.1
  have hmax : maximal n P = true := maximal_complete n P h
  have hmem := existsMax_has k 1 n [] P hlen hS hfree hsupp hlo (by simpa using hmax)
  unfold anyMaximalSearch
  exact hmem

theorem anyMaximalSearch_of_HasMaximal (n k : Nat)
    (h : HasMaximalOfSize n k) :
    anyMaximalSearch n k = true := by
  obtain ⟨A, P, hA, hN, hlen, hiff⟩ := h
  have hP := MaximalAP3Free_ofIntList n P A hA hiff
  have hsort := MaximalAP3Free_sort n P hP
  have hlen' : (sortList P).length = k := by
    rw [length_sortList P, hlen]
  have hS := strictSorted_sortList P hN
  exact anyMaximalSearch_of_sorted n k (sortList P) hlen' hS hsort

theorem not_HasMaximalOfSize_of_search (n k : Nat)
    (hfalse : anyMaximalSearch n k = false) :
    ¬ HasMaximalOfSize n k := by
  intro h
  have := anyMaximalSearch_of_HasMaximal n k h
  exact Bool.false_ne_true (hfalse.symm.trans this)

theorem anyMaximalSearch5_33 : anyMaximalSearch 33 5 = false := by native_decide
theorem anyMaximalSearch6_33 : anyMaximalSearch 33 6 = false := by native_decide
theorem anyMaximalSearch7_33 : anyMaximalSearch 33 7 = false := by native_decide

theorem nodupInt_cert33 : NodupInt [1, 2, 4, 5, 13, 14, 16, 17] := by
  refine ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, trivial⟩⟩⟩⟩⟩⟩⟩⟩
  · intro h; rcases h with h | h | h | h | h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h | h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h <;> first | omega | cases h
  · intro h; cases h

theorem HasMaximalOfSize_33_8 : HasMaximalOfSize 33 8 :=
  ⟨ofIntList [1, 2, 4, 5, 13, 14, 16, 17], [1, 2, 4, 5, 13, 14, 16, 17],
    maximal_of_cert_n33, nodupInt_cert33, rfl,
    ofIntList_of_memInt [1, 2, 4, 5, 13, 14, 16, 17]⟩

theorem sat3_eq_eight_of (n : Nat) (hn : 1 ≤ n) (hn23 : 23 ≤ n)
    (h5 : anyMaximalSearch n 5 = false)
    (h6 : anyMaximalSearch n 6 = false)
    (h7 : anyMaximalSearch n 7 = false)
    (h8 : HasMaximalOfSize n 8) :
    sat3 n hn = 8 := by
  have hspec := sat3_spec n hn
  have hle : sat3 n hn ≤ 8 := hspec.2.1 8 h8
  have hge : 8 ≤ sat3 n hn := by
    have hk := hspec.2.2.2.1
    have hcases :
        sat3 n hn = 1 ∨ sat3 n hn = 2 ∨ sat3 n hn = 3 ∨
        sat3 n hn = 4 ∨ sat3 n hn = 5 ∨ sat3 n hn = 6 ∨
        sat3 n hn = 7 ∨ 8 ≤ sat3 n hn := by omega
    rcases hcases with h1 | h2 | h3 | h4' | h5' | h6' | h7' | h8'
    · have hsz : HasMaximalOfSize n 1 := by simpa [h1] using hspec.1
      have hpb := HasMaximalOfSize_pairBound n 1 hsz
      have : pairBound 1 = 1 := by simp [pairBound]
      omega
    · have hsz : HasMaximalOfSize n 2 := by simpa [h2] using hspec.1
      exact (not_HasMaximalOfSize_2_of_gt_five n
        (Nat.le_trans (by decide : 6 ≤ 23) hn23) hsz).elim
    · have hsz : HasMaximalOfSize n 3 := by simpa [h3] using hspec.1
      exact (not_HasMaximalOfSize_3_of_gt_twelve n
        (Nat.le_trans (by decide : 13 ≤ 23) hn23) hsz).elim
    · have hsz : HasMaximalOfSize n 4 := by simpa [h4'] using hspec.1
      exact (not_HasMaximalOfSize_4_of_gt_twentytwo n hn23 hsz).elim
    · have hsz : HasMaximalOfSize n 5 := by simpa [h5'] using hspec.1
      exact (not_HasMaximalOfSize_of_search n 5 h5 hsz).elim
    · have hsz : HasMaximalOfSize n 6 := by simpa [h6'] using hspec.1
      exact (not_HasMaximalOfSize_of_search n 6 h6 hsz).elim
    · have hsz : HasMaximalOfSize n 7 := by simpa [h7'] using hspec.1
      exact (not_HasMaximalOfSize_of_search n 7 h7 hsz).elim
    · exact h8'
  omega

theorem sat3_eq_thirtythree : sat3 33 (by decide) = 8 :=
  sat3_eq_eight_of 33 (by decide) (by decide)
    anyMaximalSearch5_33 anyMaximalSearch6_33 anyMaximalSearch7_33
    HasMaximalOfSize_33_8

theorem pairBound_five : pairBound 5 = 35 := by
  simp [pairBound]

theorem not_HasMaximalOfSize_5_of_gt_thirtyfive (n : Nat) (hn : 36 ≤ n) :
    ¬ HasMaximalOfSize n 5 := by
  intro h
  have := HasMaximalOfSize_pairBound n 5 h
  have : pairBound 5 = 35 := pairBound_five
  omega

theorem sat3_eq_eight_of_pair5 (n : Nat) (hn : 1 ≤ n) (hn36 : 36 ≤ n)
    (h6 : anyMaximalSearch n 6 = false)
    (h7 : anyMaximalSearch n 7 = false)
    (h8 : HasMaximalOfSize n 8) :
    sat3 n hn = 8 := by
  have hspec := sat3_spec n hn
  have hle : sat3 n hn ≤ 8 := hspec.2.1 8 h8
  have hge : 8 ≤ sat3 n hn := by
    have hk := hspec.2.2.2.1
    have hcases :
        sat3 n hn = 1 ∨ sat3 n hn = 2 ∨ sat3 n hn = 3 ∨
        sat3 n hn = 4 ∨ sat3 n hn = 5 ∨ sat3 n hn = 6 ∨
        sat3 n hn = 7 ∨ 8 ≤ sat3 n hn := by omega
    rcases hcases with h1 | h2 | h3 | h4' | h5' | h6' | h7' | h8'
    · have hsz : HasMaximalOfSize n 1 := by simpa [h1] using hspec.1
      have hpb := HasMaximalOfSize_pairBound n 1 hsz
      have : pairBound 1 = 1 := by simp [pairBound]
      omega
    · have hsz : HasMaximalOfSize n 2 := by simpa [h2] using hspec.1
      exact (not_HasMaximalOfSize_2_of_gt_five n
        (Nat.le_trans (by decide : 6 ≤ 36) hn36) hsz).elim
    · have hsz : HasMaximalOfSize n 3 := by simpa [h3] using hspec.1
      exact (not_HasMaximalOfSize_3_of_gt_twelve n
        (Nat.le_trans (by decide : 13 ≤ 36) hn36) hsz).elim
    · have hsz : HasMaximalOfSize n 4 := by simpa [h4'] using hspec.1
      exact (not_HasMaximalOfSize_4_of_gt_twentytwo n
        (Nat.le_trans (by decide : 23 ≤ 36) hn36) hsz).elim
    · have hsz : HasMaximalOfSize n 5 := by simpa [h5'] using hspec.1
      exact (not_HasMaximalOfSize_5_of_gt_thirtyfive n hn36 hsz).elim
    · have hsz : HasMaximalOfSize n 6 := by simpa [h6'] using hspec.1
      exact (not_HasMaximalOfSize_of_search n 6 h6 hsz).elim
    · have hsz : HasMaximalOfSize n 7 := by simpa [h7'] using hspec.1
      exact (not_HasMaximalOfSize_of_search n 7 h7 hsz).elim
    · exact h8'
  omega

end Sat3

