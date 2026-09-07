import Sat3.FromDigits

/-
  Subset-sum lists. Length is 2^{length} by construction.
-/

namespace Sat3

def mapAdd (d : Nat) : List Nat → List Nat
  | [] => []
  | x :: xs => (x + d) :: mapAdd d xs

theorem mapAdd_length (d : Nat) :
    ∀ xs, (mapAdd d xs).length = xs.length
  | [] => rfl
  | _ :: xs => by
      simp [mapAdd]
      exact mapAdd_length d xs

/-- Subset sums of a digit list, starting from `{0}`. -/
def subsetSums : List Nat → List Nat
  | [] => [0]
  | d :: ds =>
      let P := subsetSums ds
      P ++ mapAdd d P

theorem subsetSums_length :
    ∀ ds, (subsetSums ds).length = 2 ^ ds.length
  | [] => by simp [subsetSums]
  | d :: ds => by
      simp [subsetSums, List.length_append, mapAdd_length]
      have ih := subsetSums_length ds
      rw [ih]
      have h2 : 2 ^ (ds.length + 1) = 2 ^ ds.length * 2 := Nat.pow_succ 2 ds.length
      omega

/-- The greedy digit list of length `k` has `2^k` subset sums
(counted with multiplicity). That is the nested-doubling bound. -/
theorem greedy_subsetSums_length (k R : Nat) (hk : 1 ≤ k)
    (hlo : Ilo k ≤ R) (hhi : R ≤ Ihi k) :
    (subsetSums (greedyDigits k R)).length = 2 ^ k := by
  have hlen := greedyDigits_length k R hk hlo hhi
  have h := subsetSums_length (greedyDigits k R)
  rw [hlen] at h
  exact h

/-- Membership in a `List Nat`, without `List.Mem`. -/
def Mem : List Nat → Nat → Prop
  | [], _ => False
  | x :: xs, y => y = x ∨ Mem xs y

theorem mem_nil (y : Nat) : ¬ Mem [] y := fun h => h

theorem mem_cons (x : Nat) (xs : List Nat) (y : Nat) :
    Mem (x :: xs) y ↔ y = x ∨ Mem xs y := Iff.rfl

theorem mem_singleton (x y : Nat) : Mem [x] y ↔ y = x := by
  constructor
  · intro h
    cases h with
    | inl h => exact h
    | inr h => cases h
  · intro h
    exact Or.inl h

theorem mem_append :
    ∀ xs ys y, Mem (xs ++ ys) y ↔ Mem xs y ∨ Mem ys y
  | [], ys, y => by
      constructor
      · intro h; exact Or.inr h
      · intro h
        cases h with
        | inl h => cases h
        | inr h => exact h
  | x :: xs, ys, y => by
      have ih := mem_append xs ys y
      constructor
      · intro h
        cases h with
        | inl h => exact Or.inl (Or.inl h)
        | inr h =>
          cases ih.mp h with
          | inl h => exact Or.inl (Or.inr h)
          | inr h => exact Or.inr h
      · intro h
        cases h with
        | inl h =>
          cases h with
          | inl h => exact Or.inl h
          | inr h => exact Or.inr (ih.mpr (Or.inl h))
        | inr h => exact Or.inr (ih.mpr (Or.inr h))

theorem mem_mapAdd (d : Nat) :
    ∀ xs y, Mem (mapAdd d xs) y ↔ ∃ x, Mem xs x ∧ y = x + d
  | [], y => by
      constructor
      · intro h; cases h
      · intro ⟨_, h, _⟩; cases h
  | x :: xs, y => by
      have ih := mem_mapAdd d xs y
      constructor
      · intro h
        cases h with
        | inl h =>
          exact ⟨x, Or.inl rfl, h⟩
        | inr h =>
          obtain ⟨x', hx, hy⟩ := ih.mp h
          exact ⟨x', Or.inr hx, hy⟩
      · intro ⟨z, hz, hy⟩
        cases hz with
        | inl hz =>
          subst z
          exact Or.inl hy
        | inr hz =>
          exact Or.inr (ih.mpr ⟨z, hz, hy⟩)

/-- Nested union starting from `A`, after applying digits `ds`. -/
theorem buildFrom_spec (A : Int → Prop) :
    ∀ ds t, buildFrom A ds t ↔
      ∃ a n, A a ∧ Mem (subsetSums ds) n ∧ t = a + (n : Int)
  | [], t => by
      constructor
      · intro h
        exact ⟨t, 0, h, Or.inl rfl, by simp⟩
      · intro ⟨a, n, hA, hn, ht⟩
        have : n = 0 := (mem_singleton 0 n).mp hn
        subst n
        simpa [buildFrom, ht] using hA
  | d :: ds, t => by
      have ih := buildFrom_spec (unionShift A (d : Int)) ds
      constructor
      · intro h
        obtain ⟨a, n, ha, hn, ht⟩ := (ih t).mp h
        have ha' : A a ∨ A (a - d) := ha
        cases ha' with
        | inl hA =>
          refine ⟨a, n, hA, ?_, ht⟩
          exact (mem_append _ _ _).mpr (Or.inl hn)
        | inr hA =>
          refine ⟨a - d, n + d, hA, ?_, ?_⟩
          · exact (mem_append _ _ _).mpr
              (Or.inr ((mem_mapAdd d _ _).mpr ⟨n, hn, rfl⟩))
          · have : t = (a - (d : Int)) + ((n + d : Nat) : Int) := by
              have hcast : ((n + d : Nat) : Int) = (n : Int) + d := by simp
              omega
            exact this
      · intro ⟨a, n, hA, hn, ht⟩
        have hn' := (mem_append (subsetSums ds) (mapAdd d (subsetSums ds)) n).mp hn
        cases hn' with
        | inl hnP =>
          have : unionShift A (d : Int) a := Or.inl hA
          exact (ih t).mpr ⟨a, n, this, hnP, ht⟩
        | inr hnP =>
          obtain ⟨m, hm, hnm⟩ := (mem_mapAdd d (subsetSums ds) n).mp hnP
          subst n
          have : unionShift A (d : Int) (a + d) := by
            refine Or.inr ?_
            simp [shift]
            have : a + (d : Int) - d = a := by omega
            simpa [this] using hA
          have ht' : t = (a + (d : Int)) + (m : Int) := by
            have hcast : ((m + d : Nat) : Int) = (m : Int) + d := by simp
            omega
          exact (ih t).mpr ⟨a + d, m, this, hm, ht'⟩

theorem subsetSums_zero :
    ∀ ds, Mem (subsetSums ds) 0
  | [] => Or.inl rfl
  | _d :: ds =>
      (mem_append _ _ _).mpr (Or.inl (subsetSums_zero ds))

/-- Points of the nested union from `{0,1}` along `ds` are subset sums
of `1 :: ds`. -/
theorem buildFrom_01_subsetSums (ds : List Nat) (t : Int)
    (h : buildFrom (fun z => z = 0 ∨ z = 1) ds t) :
    ∃ n, Mem (subsetSums (1 :: ds)) n ∧ t = (n : Int) := by
  obtain ⟨a, n, ha, hn, ht⟩ := (buildFrom_spec (fun z => z = 0 ∨ z = 1) ds t).mp h
  cases ha with
  | inl ha =>
    subst a
    refine ⟨n, ?_, ?_⟩
    · exact (mem_append _ _ _).mpr (Or.inl hn)
    · simpa using ht
  | inr ha =>
    subst a
    refine ⟨n + 1, ?_, ?_⟩
    · exact (mem_append _ _ _).mpr
        (Or.inr ((mem_mapAdd 1 _ _).mpr ⟨n, hn, rfl⟩))
    · have hcast : ((n + 1 : Nat) : Int) = (n : Int) + 1 := by simp
      omega

theorem greedyDigits_cons_one (k R : Nat) (hk : 1 ≤ k)
    (hlo : Ilo k ≤ R) (hhi : R ≤ Ihi k) :
    ∃ rest, greedyDigits k R = 1 :: rest := by
  have hadm := greedyDigits_admissible k R hk hlo hhi
  revert hadm
  cases greedyDigits k R with
  | nil =>
    intro hadm
    simp [IsAdmissible] at hadm
  | cons d rest =>
    intro hadm
    simp [IsAdmissible] at hadm
    have hd : d = 1 := hadm.1
    subst d
    exact ⟨rest, rfl⟩

/-- Every point of the greedy `R`-complete set equals an entry of
`subsetSums (greedyDigits k R)`, a list of length `2^k`. -/
theorem greedy_support (k R : Nat) (hk : 1 ≤ k)
    (hlo : Ilo k ≤ R) (hhi : R ≤ Ihi k)
    {t : Int}
    (ht : buildFrom (fun z => z = 0 ∨ z = 1) (greedyDigits k R).tail t) :
    ∃ n, Mem (subsetSums (greedyDigits k R)) n ∧ t = (n : Int) := by
  obtain ⟨rest, hrest⟩ := greedyDigits_cons_one k R hk hlo hhi
  have : (greedyDigits k R).tail = rest := by
    rw [hrest]
    rfl
  have ht' : buildFrom (fun z => z = 0 ∨ z = 1) rest t := by
    simpa [this] using ht
  obtain ⟨n, hn, ht⟩ := buildFrom_01_subsetSums rest t ht'
  refine ⟨n, ?_, ht⟩
  simpa [hrest] using hn

end Sat3
