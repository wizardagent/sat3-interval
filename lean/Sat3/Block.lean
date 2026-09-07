import Sat3.Basic

/-
  The 4-point block S(a) = {a, a+1, a+4, a+5} is 3-AP-free and its
  pair-completions fill the 16-point interval [a-5, a+10].
-/

namespace Sat3

def memS (a x : Int) : Prop :=
  x = a ∨ x = a + 1 ∨ x = a + 4 ∨ x = a + 5

def S (a : Int) : Int → Prop := fun x => memS a x

theorem S_AP3Free (a : Int) : AP3Free (S a) := by
  intro x y z hx hy hz hAP
  simp [S, memS] at hx hy hz
  rcases hx with hx | hx | hx | hx
    <;> rcases hy with hy | hy | hy | hy
    <;> rcases hz with hz | hz | hz | hz
  all_goals
    (try subst x); (try subst y); (try subst z)
    rcases hAP with ⟨hxy, hyz, hxz, hsum⟩
    omega

private theorem pair0_5 (t : Int) (h : FormsAP3 0 5 t) : CompletedBy (S 0) t :=
  ⟨0, 5, by simp [S, memS], by simp [S, memS], h⟩

private theorem pair0_4 (t : Int) (h : FormsAP3 0 4 t) : CompletedBy (S 0) t :=
  ⟨0, 4, by simp [S, memS], by simp [S, memS], h⟩

private theorem pair0_1 (t : Int) (h : FormsAP3 0 1 t) : CompletedBy (S 0) t :=
  ⟨0, 1, by simp [S, memS], by simp [S, memS], h⟩

private theorem pair1_4 (t : Int) (h : FormsAP3 1 4 t) : CompletedBy (S 0) t :=
  ⟨1, 4, by simp [S, memS], by simp [S, memS], h⟩

private theorem pair1_5 (t : Int) (h : FormsAP3 1 5 t) : CompletedBy (S 0) t :=
  ⟨1, 5, by simp [S, memS], by simp [S, memS], h⟩

private theorem pair4_5 (t : Int) (h : FormsAP3 4 5 t) : CompletedBy (S 0) t :=
  ⟨4, 5, by simp [S, memS], by simp [S, memS], h⟩

/-- Completions of pairs from `S(0)` fill `[-5,10]`. -/
theorem S0_covers (t : Int) (ht : -5 ≤ t ∧ t ≤ 10) :
    memS 0 t ∨ CompletedBy (S 0) t := by
  have hcases :
      t = -5 ∨ t = -4 ∨ t = -3 ∨ t = -2 ∨ t = -1 ∨
      t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨
      t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 8 ∨ t = 9 ∨ t = 10 := by omega
  rcases hcases with
      h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst t; refine Or.inr (pair0_5 (-5) ?_); simp [FormsAP3]
  · subst t; refine Or.inr (pair0_4 (-4) ?_); simp [FormsAP3]
  · subst t; refine Or.inr (pair1_5 (-3) ?_); simp [FormsAP3]
  · subst t; refine Or.inr (pair1_4 (-2) ?_); simp [FormsAP3]
  · subst t; refine Or.inr (pair0_1 (-1) ?_); simp [FormsAP3]
  · subst t; exact Or.inl (Or.inl rfl)
  · subst t; exact Or.inl (Or.inr (Or.inl rfl))
  · subst t; refine Or.inr (pair0_4 2 ?_); simp [FormsAP3]
  · subst t; refine Or.inr (pair1_5 3 ?_); simp [FormsAP3]
  · subst t; exact Or.inl (Or.inr (Or.inr (Or.inl rfl)))
  · subst t; exact Or.inl (Or.inr (Or.inr (Or.inr rfl)))
  · subst t; refine Or.inr (pair4_5 6 ?_); simp [FormsAP3]
  · subst t; refine Or.inr (pair1_4 7 ?_); simp [FormsAP3]
  · subst t; refine Or.inr (pair0_4 8 ?_); simp [FormsAP3]
  · subst t; refine Or.inr (pair1_5 9 ?_); simp [FormsAP3]
  · subst t; refine Or.inr (pair0_5 10 ?_); simp [FormsAP3]

/-- Translation: completions of `S(a)` fill `[a-5, a+10]`. -/
theorem S_covers_interval (a t : Int) (ht : a - 5 ≤ t ∧ t ≤ a + 10) :
    memS a t ∨ CompletedBy (S a) t := by
  have h0 : -5 ≤ t - a ∧ t - a ≤ 10 := by omega
  have h := S0_covers (t - a) h0
  cases h with
  | inl h =>
    left
    simp [memS] at h ⊢
    omega
  | inr h =>
    right
    rcases h with ⟨x, y, hx, hy, hAP⟩
    refine ⟨x + a, y + a, ?_, ?_, ?_⟩
    · simp [S, memS] at hx ⊢; omega
    · simp [S, memS] at hy ⊢; omega
    · rcases hAP with ⟨hxy, hyt, hxt, hor⟩
      refine ⟨by omega, by omega, by omega, ?_⟩
      rcases hor with h | h | h <;> omega

theorem S6_subset_16 (t : Int) (h : S 6 t) : InIcc1 16 t := by
  simp [S, memS, InIcc1] at h ⊢
  omega

theorem S6_maximal_16 : MaximalAP3Free 16 (S 6) := by
  refine ⟨S6_subset_16, S_AP3Free 6, ?_⟩
  intro t ht
  simp [InIcc1] at ht
  have : (6 : Int) - 5 ≤ t ∧ t ≤ 6 + 10 := by omega
  exact S_covers_interval 6 t this

theorem maximal_S6_bool : maximal 16 [6, 7, 10, 11] = true := by
  native_decide

def TwoBlocks (x : Int) : Prop := S 6 x ∨ S 22 x

theorem twoBlocks_subset_32 (t : Int) (h : TwoBlocks t) : InIcc1 32 t := by
  simp [TwoBlocks, S, memS, InIcc1] at h ⊢
  omega

theorem twoBlocks_AP3Free : AP3Free TwoBlocks := by
  intro x y z hx hy hz hAP
  have hx' : memS 6 x ∨ memS 22 x := by simpa [TwoBlocks, S] using hx
  have hy' : memS 6 y ∨ memS 22 y := by simpa [TwoBlocks, S] using hy
  have hz' : memS 6 z ∨ memS 22 z := by simpa [TwoBlocks, S] using hz
  rcases hx' with hx6 | hx22
  · rcases hy' with hy6 | hy22
    · rcases hz' with hz6 | hz22
      · exact S_AP3Free 6 x y z hx6 hy6 hz6 hAP
      · simp [memS] at hx6 hy6 hz22
        rcases hAP with ⟨_, _, _, hsum⟩
        omega
    · rcases hz' with hz6 | hz22
      · simp [memS] at hx6 hy22 hz6
        rcases hAP with ⟨_, _, _, hsum⟩
        omega
      · simp [memS] at hx6 hy22 hz22
        rcases hAP with ⟨_, _, _, hsum⟩
        omega
  · rcases hy' with hy6 | hy22
    · rcases hz' with hz6 | hz22
      · simp [memS] at hx22 hy6 hz6
        rcases hAP with ⟨_, _, _, hsum⟩
        omega
      · simp [memS] at hx22 hy6 hz22
        rcases hAP with ⟨_, _, _, hsum⟩
        omega
    · rcases hz' with hz6 | hz22
      · simp [memS] at hx22 hy22 hz6
        rcases hAP with ⟨_, _, _, hsum⟩
        omega
      · exact S_AP3Free 22 x y z hx22 hy22 hz22 hAP

theorem twoBlocks_maximal_32 : MaximalAP3Free 32 TwoBlocks := by
  refine ⟨twoBlocks_subset_32, twoBlocks_AP3Free, ?_⟩
  intro t ht
  simp [InIcc1] at ht
  by_cases h16 : t ≤ 16
  · have : (6 : Int) - 5 ≤ t ∧ t ≤ 6 + 10 := by omega
    have h := S_covers_interval 6 t this
    cases h with
    | inl h => exact Or.inl (Or.inl h)
    | inr h =>
      rcases h with ⟨x, y, hx, hy, hAP⟩
      exact Or.inr ⟨x, y, Or.inl hx, Or.inl hy, hAP⟩
  · have : (22 : Int) - 5 ≤ t ∧ t ≤ 22 + 10 := by omega
    have h := S_covers_interval 22 t this
    cases h with
    | inl h => exact Or.inl (Or.inr h)
    | inr h =>
      rcases h with ⟨x, y, hx, hy, hAP⟩
      exact Or.inr ⟨x, y, Or.inr hx, Or.inr hy, hAP⟩

theorem maximal_twoBlocks_bool :
    maximal 32 [6, 7, 10, 11, 22, 23, 26, 27] = true := by
  native_decide

/-- The 8-point set `S(0) ∪ S(d)` as a list. -/
def twoBlockList (d : Int) : List Int :=
  [0, 1, 4, 5, d, d + 1, d + 4, d + 5]

/-- Endpoint covering of `[-d-5, d+10]` by the eight-point set,
checked on a finite window of length `2d+16` starting at `-d-5`. -/
def twoBlockCovers (d : Nat) : Bool :=
  let A := twoBlockList (d : Int)
  let lo : Int := -((d : Int) + 5)
  let hi : Int := (d : Int) + 10
  ap3Free A &&
  (List.range (2 * d + 16)).all fun i =>
    let t : Int := lo + i
    decide (t ≤ hi) && (A.contains t || completes A t)

/-- Lemma 3.4, six distances: `S(0) ∪ S(d)` is 3-AP-free and
endpoint-covers `[-d-5, d+10]`. -/
theorem twoBlock_covers_11 : twoBlockCovers 11 = true := by native_decide
theorem twoBlock_covers_12 : twoBlockCovers 12 = true := by native_decide
theorem twoBlock_covers_13 : twoBlockCovers 13 = true := by native_decide
theorem twoBlock_covers_14 : twoBlockCovers 14 = true := by native_decide
theorem twoBlock_covers_15 : twoBlockCovers 15 = true := by native_decide
theorem twoBlock_covers_16 : twoBlockCovers 16 = true := by native_decide

end Sat3
