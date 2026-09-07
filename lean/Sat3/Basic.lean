/-
  3-AP-free subsets of `{1,...,n}` and maximality.
  No mathlib.
-/

namespace Sat3

/-- Three distinct integers in arithmetic progression (`y` the middle). -/
def IsAP3 (x y z : Int) : Prop :=
  x ≠ y ∧ y ≠ z ∧ x ≠ z ∧ 2 * y = x + z

/-- The three distinct points form a 3-AP in some order. -/
def FormsAP3 (x y t : Int) : Prop :=
  x ≠ y ∧ y ≠ t ∧ x ≠ t ∧
    (2 * x = y + t ∨ 2 * y = x + t ∨ 2 * t = x + y)

def AP3Free (A : Int → Prop) : Prop :=
  ∀ x y z, A x → A y → A z → ¬ IsAP3 x y z

def CompletedBy (A : Int → Prop) (t : Int) : Prop :=
  ∃ x y, A x ∧ A y ∧ FormsAP3 x y t

def InIcc1 (n : Nat) (t : Int) : Prop :=
  1 ≤ t ∧ t ≤ (n : Int)

def MaximalAP3Free (n : Nat) (A : Int → Prop) : Prop :=
  (∀ t, A t → InIcc1 n t) ∧
  AP3Free A ∧
  ∀ t, InIcc1 n t → A t ∨ CompletedBy A t

/-- Adjoin the new right endpoint if it is not already completed. -/
def extendRight (A : Int → Prop) (n : Nat) : Int → Prop :=
  fun t => A t ∨ (t = (n : Int) + 1 ∧ ¬ CompletedBy A t)

theorem InIcc1_of_le {n m : Nat} (h : n ≤ m) {t : Int}
    (ht : InIcc1 n t) : InIcc1 m t :=
  ⟨ht.1, Int.le_trans ht.2 (Int.ofNat_le.mpr h)⟩

theorem extendRight_mem (A : Int → Prop) (n : Nat) {t : Int}
    (ht : extendRight A n t) :
    A t ∨ t = (n : Int) + 1 := by
  cases ht with
  | inl h => exact Or.inl h
  | inr h => exact Or.inr h.1

theorem not_A_of_new (A : Int → Prop) (n : Nat)
    (hsupp : ∀ t, A t → InIcc1 n t) {t : Int}
    (ht : t = (n : Int) + 1) : ¬ A t := by
  intro hA
  have := hsupp t hA
  have : t ≤ (n : Int) := this.2
  omega

/-- Any two points of an `IsAP3` complete the third. -/
theorem formsAP3_of_isAP3 {x y z : Int} (h : IsAP3 x y z) :
    FormsAP3 x y z := by
  rcases h with ⟨hxy, hyz, hxz, hsum⟩
  exact ⟨hxy, hyz, hxz, Or.inr (Or.inl hsum)⟩

theorem formsAP3_yz_of_isAP3 {x y z : Int} (h : IsAP3 x y z) :
    FormsAP3 y z x := by
  rcases h with ⟨hxy, hyz, hxz, hsum⟩
  refine ⟨hyz, hxz.symm, hxy.symm, ?_⟩
  omega

theorem formsAP3_xz_of_isAP3 {x y z : Int} (h : IsAP3 x y z) :
    FormsAP3 x z y := by
  rcases h with ⟨hxy, hyz, hxz, hsum⟩
  refine ⟨hxz, hyz.symm, hxy, ?_⟩
  omega

/-- Lemma 9.4: a maximal set in `[n]` extends to one in `[n+1]`
by adjoining `n+1` at most. -/
theorem maximal_extend_right (n : Nat) (A : Int → Prop)
    (h : MaximalAP3Free n A) :
    MaximalAP3Free (n + 1) (extendRight A n) := by
  rcases h with ⟨hsupp, hfree, hcov⟩
  have hnew : ∀ t, t = (n : Int) + 1 → ¬ A t :=
    fun t ht => not_A_of_new A n hsupp ht
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    cases ht with
    | inl hA =>
      exact InIcc1_of_le (Nat.le_succ n) (hsupp t hA)
    | inr hN =>
      have : t = (n : Int) + 1 := hN.1
      subst t
      exact ⟨by omega, by omega⟩
  · intro x y z hx hy hz hAP
    have hx' := extendRight_mem A n hx
    have hy' := extendRight_mem A n hy
    have hz' := extendRight_mem A n hz
    rcases hx' with hxA | hxN
    · rcases hy' with hyA | hyN
      · rcases hz' with hzA | hzN
        · exact hfree x y z hxA hyA hzA hAP
        · have hzE : ¬ CompletedBy A z := by
            cases hz with
            | inl h => exact (hnew z hzN h).elim
            | inr h => exact h.2
          have hC : CompletedBy A z :=
            ⟨x, y, hxA, hyA, formsAP3_of_isAP3 hAP⟩
          exact hzE hC
      · rcases hz' with hzA | hzN
        · have hyE : ¬ CompletedBy A y := by
            cases hy with
            | inl h => exact (hnew y hyN h).elim
            | inr h => exact h.2
          have hC : CompletedBy A y :=
            ⟨x, z, hxA, hzA, formsAP3_xz_of_isAP3 hAP⟩
          exact hyE hC
        · rcases hAP with ⟨_, hyz, _, _⟩
          omega
    · rcases hy' with hyA | hyN
      · rcases hz' with hzA | hzN
        · have hxE : ¬ CompletedBy A x := by
            cases hx with
            | inl h => exact (hnew x hxN h).elim
            | inr h => exact h.2
          have hC : CompletedBy A x :=
            ⟨y, z, hyA, hzA, formsAP3_yz_of_isAP3 hAP⟩
          exact hxE hC
        · rcases hAP with ⟨_, _, hxz, _⟩
          omega
      · rcases hAP with ⟨hxy, _, _, _⟩
        omega
  · intro t ht
    by_cases hle : t ≤ (n : Int)
    · have ht' : InIcc1 n t := ⟨ht.1, hle⟩
      have h0 := hcov t ht'
      cases h0 with
      | inl hA => exact Or.inl (Or.inl hA)
      | inr hC =>
        obtain ⟨x, y, hx, hy, hf⟩ := hC
        exact Or.inr ⟨x, y, Or.inl hx, Or.inl hy, hf⟩
    · have heq : t = (n : Int) + 1 := by
        have : 1 ≤ t ∧ t ≤ (n : Int) + 1 := ht
        omega
      subst t
      by_cases hC : CompletedBy A ((n : Int) + 1)
      · obtain ⟨x, y, hx, hy, hf⟩ := hC
        exact Or.inr ⟨x, y, Or.inl hx, Or.inl hy, hf⟩
      · exact Or.inl (Or.inr ⟨rfl, hC⟩)

/-! Boolean checkers, used for concrete certificates via `native_decide`. -/

def isAP3 (x y z : Int) : Bool :=
  decide (x ≠ y) && decide (y ≠ z) && decide (x ≠ z) && decide (2 * y = x + z)

def formsAP3 (x y t : Int) : Bool :=
  decide (x ≠ y) && decide (y ≠ t) && decide (x ≠ t) &&
    (decide (2 * x = y + t) || decide (2 * y = x + t) || decide (2 * t = x + y))

def ap3Free (A : List Int) : Bool :=
  A.all fun x => A.all fun y => A.all fun z => !isAP3 x y z

def completes (A : List Int) (t : Int) : Bool :=
  A.any fun x => A.any fun y => formsAP3 x y t

def inInterval (n : Nat) (t : Int) : Bool :=
  decide (1 ≤ t) && decide (t ≤ (n : Int))

def maximal (n : Nat) (A : List Int) : Bool :=
  A.all (fun t => inInterval n t) &&
  ap3Free A &&
  (List.range n).all fun i =>
    let t : Int := i + 1
    A.contains t || completes A t

end Sat3
