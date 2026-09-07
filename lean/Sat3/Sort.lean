import Sat3.Thm

/-
  Insertion sort on `List Int`, so a nodup list of size k can be
  identified with a strictly increasing k-tuple.
-/

namespace Sat3

def insertSorted (x : Int) : List Int → List Int
  | [] => [x]
  | y :: ys =>
      if x ≤ y then x :: y :: ys else y :: insertSorted x ys

def sortList : List Int → List Int
  | [] => []
  | x :: xs => insertSorted x (sortList xs)

def StrictSorted : List Int → Prop
  | [] => True
  | [_] => True
  | x :: y :: xs => x < y ∧ StrictSorted (y :: xs)

theorem memInt_insertSorted (x : Int) :
    ∀ xs t, MemInt (insertSorted x xs) t ↔ t = x ∨ MemInt xs t
  | [], t => by
      simp [insertSorted]
      constructor
      · intro h
        rcases h with h | h
        · exact Or.inl h
        · cases h
      · intro h
        rcases h with h | h
        · exact Or.inl h
        · cases h
  | y :: ys, t => by
      unfold insertSorted
      by_cases hxy : x ≤ y
      · simp [hxy]
        constructor
        · intro h
          rcases h with h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr h)
        · intro h
          rcases h with h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr h)
      · simp [hxy]
        have ih := memInt_insertSorted x ys t
        constructor
        · intro h
          rcases h with h | h
          · exact Or.inr (Or.inl h)
          · have := ih.mp h
            rcases this with h | h
            · exact Or.inl h
            · exact Or.inr (Or.inr h)
        · intro h
          rcases h with h | h | h
          · exact Or.inr (ih.mpr (Or.inl h))
          · exact Or.inl h
          · exact Or.inr (ih.mpr (Or.inr h))

theorem memInt_sortList :
    ∀ xs t, MemInt (sortList xs) t ↔ MemInt xs t
  | [], t => Iff.rfl
  | x :: xs, t => by
      unfold sortList
      have ih := memInt_sortList xs t
      have hi := memInt_insertSorted x (sortList xs) t
      constructor
      · intro h
        have := hi.mp h
        rcases this with h | h
        · exact Or.inl h
        · exact Or.inr (ih.mp h)
      · intro h
        rcases h with h | h
        · exact hi.mpr (Or.inl h)
        · exact hi.mpr (Or.inr (ih.mpr h))

theorem ofIntList_sortList (P : List Int) (t : Int) :
    ofIntList (sortList P) t ↔ ofIntList P t := by
  have h1 := ofIntList_of_memInt (sortList P) t
  have h2 := ofIntList_of_memInt P t
  have h3 := memInt_sortList P t
  constructor
  · intro h
    exact h2.mpr (h3.mp (h1.mp h))
  · intro h
    exact h1.mpr (h3.mpr (h2.mp h))

theorem MaximalAP3Free_sort (n : Nat) (P : List Int)
    (h : MaximalAP3Free n (ofIntList P)) :
    MaximalAP3Free n (ofIntList (sortList P)) := by
  rcases h with ⟨hsupp, hfree, hcov⟩
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    exact hsupp t ((ofIntList_sortList P t).mp ht)
  · intro x y z hx hy hz hAP
    exact hfree x y z
      ((ofIntList_sortList P x).mp hx)
      ((ofIntList_sortList P y).mp hy)
      ((ofIntList_sortList P z).mp hz) hAP
  · intro t ht
    have h0 := hcov t ht
    cases h0 with
    | inl hA => exact Or.inl ((ofIntList_sortList P t).mpr hA)
    | inr hC =>
      obtain ⟨x, y, hx, hy, hf⟩ := hC
      exact Or.inr ⟨x, y,
        (ofIntList_sortList P x).mpr hx,
        (ofIntList_sortList P y).mpr hy, hf⟩

theorem length_insertSorted (x : Int) :
    ∀ xs, (insertSorted x xs).length = xs.length + 1
  | [] => rfl
  | y :: ys => by
      unfold insertSorted
      by_cases h : x ≤ y
      · simp [h]
      · simp [h, length_insertSorted x ys]

theorem length_sortList : ∀ xs, (sortList xs).length = xs.length
  | [] => rfl
  | x :: xs => by
      unfold sortList
      rw [length_insertSorted x (sortList xs), length_sortList xs]
      rfl

theorem nodupInt_insertSorted (x : Int) :
    ∀ xs, ¬ MemInt xs x → NodupInt xs → NodupInt (insertSorted x xs)
  | [], _, _ => nodupInt_singleton x
  | y :: ys, hnx, hN => by
      unfold insertSorted
      by_cases h : x ≤ y
      · simp [h]
        constructor
        · intro hm
          have : MemInt (y :: ys) x := hm
          exact hnx this
        · exact hN
      · simp [h]
        have hny : x ≠ y := by
          intro heq
          subst y
          exact h (Int.le_refl x)
        have hnx' : ¬ MemInt ys x := by
          intro hm
          exact hnx (Or.inr hm)
        constructor
        · intro hm
          have := (memInt_insertSorted x ys y).mp hm
          rcases this with hxy | hy
          · exact hny.symm hxy
          · exact hN.1 hy
        · exact nodupInt_insertSorted x ys hnx' hN.2

theorem nodupInt_sortList : ∀ xs, NodupInt xs → NodupInt (sortList xs)
  | [], _ => trivial
  | x :: xs, hN => by
      unfold sortList
      have hnx : ¬ MemInt (sortList xs) x := by
        intro h
        exact hN.1 ((memInt_sortList xs x).mp h)
      exact nodupInt_insertSorted x (sortList xs) hnx (nodupInt_sortList xs hN.2)

theorem strictSorted_nil : StrictSorted [] := trivial
theorem strictSorted_singleton (x : Int) : StrictSorted [x] := trivial

theorem strictSorted_insert (x : Int) :
    ∀ xs, StrictSorted xs →
      (¬ MemInt xs x) → StrictSorted (insertSorted x xs)
  | [], _, _ => trivial
  | [y], _, hnx => by
      unfold insertSorted
      by_cases h : x ≤ y
      · simp [h]
        constructor
        · have : x ≠ y := by
            intro heq; subst y; exact hnx (Or.inl rfl)
          omega
        · trivial
      · simp [h]
        constructor
        · omega
        · trivial
  | y :: z :: xs, hs, hnx => by
      unfold insertSorted
      by_cases h : x ≤ y
      · simp [h]
        constructor
        · have : x ≠ y := by
            intro heq; subst y; exact hnx (Or.inl rfl)
          omega
        · exact hs
      · simp [h]
        have hnx' : ¬ MemInt (z :: xs) x := by
          intro hm
          exact hnx (Or.inr hm)
        have htail : StrictSorted (insertSorted x (z :: xs)) :=
          strictSorted_insert x (z :: xs) hs.2 hnx'
        have hyz : y < z := hs.1
        -- insertSorted x (z::xs) is either x::z::xs or z::...
        unfold insertSorted at htail ⊢
        by_cases hxz : x ≤ z
        · simp [hxz] at htail ⊢
          constructor
          · omega
          · exact htail
        · simp [hxz] at htail ⊢
          constructor
          · omega
          · exact htail

theorem strictSorted_sortList :
    ∀ xs, NodupInt xs → StrictSorted (sortList xs)
  | [], _ => trivial
  | [x], _ => by
      simp [sortList, insertSorted]
      trivial
  | x :: y :: xs, hN => by
      unfold sortList
      have hS := strictSorted_sortList (y :: xs) hN.2
      have hnx : ¬ MemInt (sortList (y :: xs)) x := by
        intro h
        exact hN.1 ((memInt_sortList (y :: xs) x).mp h)
      exact strictSorted_insert x (sortList (y :: xs)) hS hnx

end Sat3
