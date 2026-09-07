import Sat3.Inc

/-
  Increasing k-tuples that stay 3-AP-free at every prefix.
  Native-decide on free sets, not on all combinations.
-/

namespace Sat3

/-- True if `{a, m, x}` is a 3-AP for some `a ≠ m` in `A`. -/
def blocks (A : List Int) (x : Int) : Bool :=
  A.any fun a =>
    A.any fun m =>
      decide (a ≠ m) && decide (2 * m = a + x)

/-- Increasing free `k`-tuples from `[lo, n]`, after prefix `pref`. -/
def freeFrom (lo n : Nat) (pref : List Int) : Nat → List (List Int)
  | 0 => [pref]
  | k + 1 =>
      (List.range n).flatMap fun (i : Nat) =>
        if decide (lo ≤ i + 1) then
          if blocks pref ((i : Int) + 1) then
            []
          else
            freeFrom (i + 2) n (pref ++ [((i : Int) + 1)]) k
        else
          []

def freeK (n k : Nat) : List (List Int) :=
  freeFrom 1 n [] k

def anyMaximalFree (n k : Nat) : Bool :=
  (freeK n k).any fun A => maximal n A

theorem blocks_eq_false_of_AP3Free (pref : List Int) (x : Int) (tail : List Int)
    (h : AP3Free (ofIntList (pref ++ x :: tail))) :
    blocks pref x = false := by
  cases hblk : blocks pref x with
  | false => rfl
  | true =>
    obtain ⟨a, ha, h2⟩ := List.any_eq_true.mp hblk
    obtain ⟨m, hm, hcond⟩ := List.any_eq_true.mp h2
    have hand := (Bool.and_eq_true (decide (a ≠ m)) (decide (2 * m = a + x))).mp hcond
    have hne : a ≠ m := of_decide_eq_true hand.1
    have hsum : 2 * m = a + x := of_decide_eq_true hand.2
    have haA : ofIntList (pref ++ x :: tail) a :=
      List.mem_append.mpr (Or.inl ha)
    have hmA : ofIntList (pref ++ x :: tail) m :=
      List.mem_append.mpr (Or.inl hm)
    have hxA : ofIntList (pref ++ x :: tail) x :=
      List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
    have hmx : m ≠ x := by
      intro heq
      omega
    have hax : a ≠ x := by
      intro heq
      omega
    have hAP : IsAP3 a m x := ⟨hne, hmx, hax, hsum⟩
    exact (h a m x haA hmA hxA hAP).elim

theorem mem_freeFrom_step (lo n k i : Nat) (pref rest : List Int)
    (hlo : lo ≤ i + 1) (hi : i < n)
    (hblk : blocks pref ((i : Int) + 1) = false)
    (hrest : (pref ++ [((i : Int) + 1)]) ++ rest ∈
        freeFrom (i + 2) n (pref ++ [((i : Int) + 1)]) k) :
    pref ++ (((i : Int) + 1) :: rest) ∈ freeFrom lo n pref (k + 1) := by
  unfold freeFrom
  refine List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, ?_⟩
  have hdec : decide (lo ≤ i + 1) = true := decide_eq_true hlo
  rw [hdec]
  simp [hblk]
  have heq :
      pref ++ (((i : Int) + 1) :: rest) =
        (pref ++ [((i : Int) + 1)]) ++ rest :=
    (List.append_assoc pref [((i : Int) + 1)] rest).symm
  rw [heq]
  exact hrest

theorem freeFrom_has :
    ∀ (k lo n : Nat) (pref P : List Int),
      P.length = k →
      StrictSorted P →
      AP3Free (ofIntList (pref ++ P)) →
      (∀ t, MemInt P t → InIcc1 n t) →
      (∀ t, MemInt P t → (lo : Int) ≤ t) →
      pref ++ P ∈ freeFrom lo n pref k
  | 0, lo, n, pref, P, hlen, _, _, _, _ => by
      match P with
      | [] => simp [freeFrom]
      | _ :: _ => cases hlen
  | k + 1, lo, n, pref, [], hlen, _, _, _, _ => by cases hlen
  | k + 1, lo, n, pref, x :: xs, hlen, hS, hfree, hsupp, hlo => by
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
      have hfree' : AP3Free (ofIntList ((pref ++ [x]) ++ xs)) := by
        simpa [List.append_assoc] using hfree
      have ih := freeFrom_has k (i + 2) n (pref ++ [x]) xs hlen' hS' hfree' hsupp' hlo'
      have hblk : blocks pref x = false :=
        blocks_eq_false_of_AP3Free pref x xs hfree
      have hxeq : x = (i : Int) + 1 := hix.symm
      have hblk' : blocks pref ((i : Int) + 1) = false := by simpa [hxeq] using hblk
      have ih' :
          (pref ++ [((i : Int) + 1)]) ++ xs ∈
            freeFrom (i + 2) n (pref ++ [((i : Int) + 1)]) k := by
        simpa [hxeq] using ih
      simpa [hxeq] using mem_freeFrom_step lo n k i pref xs hloi hi_lt hblk' ih'

theorem anyMaximalFree_of_sorted (n k : Nat) (P : List Int)
    (hlen : P.length = k)
    (hS : StrictSorted P)
    (h : MaximalAP3Free n (ofIntList P)) :
    anyMaximalFree n k = true := by
  have hsupp : ∀ t, MemInt P t → InIcc1 n t := by
    intro t ht
    exact h.1 t ((ofIntList_of_memInt P t).mpr ht)
  have hlo : ∀ t, MemInt P t → (1 : Int) ≤ t := by
    intro t ht
    exact (hsupp t ht).1
  have hfree : AP3Free (ofIntList ([] ++ P)) := by
    simpa using h.2.1
  have hmem := freeFrom_has k 1 n [] P hlen hS hfree hsupp hlo
  have hmax : maximal n P = true := maximal_complete n P h
  unfold anyMaximalFree freeK
  exact List.any_eq_true.mpr ⟨P, by simpa using hmem, hmax⟩

theorem anyMaximalFree_of_HasMaximal (n k : Nat)
    (h : HasMaximalOfSize n k) :
    anyMaximalFree n k = true := by
  obtain ⟨A, P, hA, hN, hlen, hiff⟩ := h
  have hP := MaximalAP3Free_ofIntList n P A hA hiff
  have hsort := MaximalAP3Free_sort n P hP
  have hlen' : (sortList P).length = k := by
    rw [length_sortList P, hlen]
  have hS := strictSorted_sortList P hN
  exact anyMaximalFree_of_sorted n k (sortList P) hlen' hS hsort

theorem not_HasMaximalOfSize_of_free (n k : Nat)
    (hfalse : anyMaximalFree n k = false) :
    ¬ HasMaximalOfSize n k := by
  intro h
  have := anyMaximalFree_of_HasMaximal n k h
  exact Bool.false_ne_true (hfalse.symm.trans this)

theorem anyMaximalFree5_27 : anyMaximalFree 27 5 = false := by native_decide
theorem anyMaximalFree6_27 : anyMaximalFree 27 6 = false := by native_decide

theorem nodupInt_cert27 : NodupInt [1, 2, 5, 11, 12, 14, 18] := by
  refine ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, trivial⟩⟩⟩⟩⟩⟩⟩
  · intro h; rcases h with h | h | h | h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h <;> first | omega | cases h
  · intro h; cases h

theorem HasMaximalOfSize_27_7 : HasMaximalOfSize 27 7 :=
  ⟨ofIntList [1, 2, 5, 11, 12, 14, 18], [1, 2, 5, 11, 12, 14, 18],
    maximal_of_cert_n27, nodupInt_cert27, rfl,
    ofIntList_of_memInt [1, 2, 5, 11, 12, 14, 18]⟩

theorem sat3_eq_seven_of (n : Nat) (hn : 1 ≤ n) (hn23 : 23 ≤ n)
    (h5 : anyMaximalFree n 5 = false)
    (h6 : anyMaximalFree n 6 = false)
    (h7 : HasMaximalOfSize n 7) :
    sat3 n hn = 7 := by
  have hspec := sat3_spec n hn
  have hle : sat3 n hn ≤ 7 := hspec.2.1 7 h7
  have hge : 7 ≤ sat3 n hn := by
    have hk := hspec.2.2.2.1
    have hcases :
        sat3 n hn = 1 ∨ sat3 n hn = 2 ∨ sat3 n hn = 3 ∨
        sat3 n hn = 4 ∨ sat3 n hn = 5 ∨ sat3 n hn = 6 ∨
        7 ≤ sat3 n hn := by omega
    rcases hcases with h1 | h2 | h3 | h4' | h5' | h6' | h7'
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
      exact (not_HasMaximalOfSize_of_free n 5 h5 hsz).elim
    · have hsz : HasMaximalOfSize n 6 := by simpa [h6'] using hspec.1
      exact (not_HasMaximalOfSize_of_free n 6 h6 hsz).elim
    · exact h7'
  omega

theorem sat3_eq_twentyseven : sat3 27 (by decide) = 7 :=
  sat3_eq_seven_of 27 (by decide) (by decide)
    anyMaximalFree5_27 anyMaximalFree6_27 HasMaximalOfSize_27_7

theorem anyMaximalFree5_28 : anyMaximalFree 28 5 = false := by native_decide
theorem anyMaximalFree6_28 : anyMaximalFree 28 6 = false := by native_decide
theorem anyMaximalFree5_29 : anyMaximalFree 29 5 = false := by native_decide
theorem anyMaximalFree6_29 : anyMaximalFree 29 6 = false := by native_decide
theorem anyMaximalFree5_30 : anyMaximalFree 30 5 = false := by native_decide
theorem anyMaximalFree6_30 : anyMaximalFree 30 6 = false := by native_decide
theorem anyMaximalFree5_31 : anyMaximalFree 31 5 = false := by native_decide
theorem anyMaximalFree6_31 : anyMaximalFree 31 6 = false := by native_decide
theorem anyMaximalFree5_32 : anyMaximalFree 32 5 = false := by native_decide
theorem anyMaximalFree6_32 : anyMaximalFree 32 6 = false := by native_decide

theorem nodupInt_cert28 : NodupInt [1, 2, 12, 13, 15, 19, 20] := by
  refine ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, trivial⟩⟩⟩⟩⟩⟩⟩
  · intro h; rcases h with h | h | h | h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h <;> first | omega | cases h
  · intro h; cases h

theorem nodupInt_cert29 : NodupInt [1, 2, 12, 13, 15, 19, 20] :=
  nodupInt_cert28

theorem nodupInt_cert30 : NodupInt [1, 2, 13, 14, 16, 21, 22] := by
  refine ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, trivial⟩⟩⟩⟩⟩⟩⟩
  · intro h; rcases h with h | h | h | h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h <;> first | omega | cases h
  · intro h; cases h

theorem nodupInt_cert31 : NodupInt [1, 2, 13, 14, 16, 21, 22] :=
  nodupInt_cert30

theorem nodupInt_cert32 : NodupInt [2, 3, 14, 15, 17, 22, 23] := by
  refine ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, trivial⟩⟩⟩⟩⟩⟩⟩
  · intro h; rcases h with h | h | h | h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h <;> first | omega | cases h
  · intro h; cases h

theorem HasMaximalOfSize_28_7 : HasMaximalOfSize 28 7 :=
  ⟨ofIntList [1, 2, 12, 13, 15, 19, 20], [1, 2, 12, 13, 15, 19, 20],
    maximal_of_cert_n28, nodupInt_cert28, rfl,
    ofIntList_of_memInt [1, 2, 12, 13, 15, 19, 20]⟩

theorem HasMaximalOfSize_29_7 : HasMaximalOfSize 29 7 :=
  ⟨ofIntList [1, 2, 12, 13, 15, 19, 20], [1, 2, 12, 13, 15, 19, 20],
    maximal_of_cert_n29, nodupInt_cert29, rfl,
    ofIntList_of_memInt [1, 2, 12, 13, 15, 19, 20]⟩

theorem HasMaximalOfSize_30_7 : HasMaximalOfSize 30 7 :=
  ⟨ofIntList [1, 2, 13, 14, 16, 21, 22], [1, 2, 13, 14, 16, 21, 22],
    maximal_of_cert_n30, nodupInt_cert30, rfl,
    ofIntList_of_memInt [1, 2, 13, 14, 16, 21, 22]⟩

theorem HasMaximalOfSize_31_7 : HasMaximalOfSize 31 7 :=
  ⟨ofIntList [1, 2, 13, 14, 16, 21, 22], [1, 2, 13, 14, 16, 21, 22],
    maximal_of_cert_n31, nodupInt_cert31, rfl,
    ofIntList_of_memInt [1, 2, 13, 14, 16, 21, 22]⟩

theorem HasMaximalOfSize_32_7 : HasMaximalOfSize 32 7 :=
  ⟨ofIntList [2, 3, 14, 15, 17, 22, 23], [2, 3, 14, 15, 17, 22, 23],
    maximal_of_cert_n32, nodupInt_cert32, rfl,
    ofIntList_of_memInt [2, 3, 14, 15, 17, 22, 23]⟩

theorem sat3_eq_twentyeight : sat3 28 (by decide) = 7 :=
  sat3_eq_seven_of 28 (by decide) (by decide)
    anyMaximalFree5_28 anyMaximalFree6_28 HasMaximalOfSize_28_7

theorem sat3_eq_twentynine : sat3 29 (by decide) = 7 :=
  sat3_eq_seven_of 29 (by decide) (by decide)
    anyMaximalFree5_29 anyMaximalFree6_29 HasMaximalOfSize_29_7

theorem sat3_eq_thirty : sat3 30 (by decide) = 7 :=
  sat3_eq_seven_of 30 (by decide) (by decide)
    anyMaximalFree5_30 anyMaximalFree6_30 HasMaximalOfSize_30_7

theorem sat3_eq_thirtyone : sat3 31 (by decide) = 7 :=
  sat3_eq_seven_of 31 (by decide) (by decide)
    anyMaximalFree5_31 anyMaximalFree6_31 HasMaximalOfSize_31_7

theorem sat3_eq_thirtytwo : sat3 32 (by decide) = 7 :=
  sat3_eq_seven_of 32 (by decide) (by decide)
    anyMaximalFree5_32 anyMaximalFree6_32 HasMaximalOfSize_32_7

end Sat3
