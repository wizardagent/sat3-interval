import Sat3.Basic

/-
  Soundness of the boolean checkers: `maximal n A = true`
  implies `MaximalAP3Free n (ofIntList A)`.
-/

namespace Sat3

def ofIntList (A : List Int) : Int → Prop :=
  fun t => t ∈ A

theorem isAP3_of (x y z : Int) (h : IsAP3 x y z) : isAP3 x y z = true := by
  rcases h with ⟨hxy, hyz, hxz, hsum⟩
  simp [isAP3, hxy, hyz, hxz, hsum]

theorem isAP3_true (x y z : Int) (h : isAP3 x y z = true) : IsAP3 x y z := by
  have hxy : x ≠ y := by
    simp [isAP3] at h
    exact h.1.1.1
  have hyz : y ≠ z := by
    simp [isAP3] at h
    exact h.1.1.2
  have hxz : x ≠ z := by
    simp [isAP3] at h
    exact h.1.2
  have hsum : 2 * y = x + z := by
    simp [isAP3] at h
    exact h.2
  exact ⟨hxy, hyz, hxz, hsum⟩

theorem formsAP3_true (x y t : Int) (h : formsAP3 x y t = true) : FormsAP3 x y t := by
  have hxy : x ≠ y := by
    simp [formsAP3] at h
    exact h.1.1.1
  have hyt : y ≠ t := by
    simp [formsAP3] at h
    exact h.1.1.2
  have hxt : x ≠ t := by
    simp [formsAP3] at h
    exact h.1.2
  have hor : (2 * x = y + t ∨ 2 * y = x + t) ∨ 2 * t = x + y := by
    simp [formsAP3] at h
    exact h.2
  refine ⟨hxy, hyt, hxt, ?_⟩
  rcases hor with h1 | h2
  · rcases h1 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr h2)

theorem inInterval_true (n : Nat) (t : Int) (h : inInterval n t = true) :
    InIcc1 n t := by
  have h1 : 1 ≤ t := by
    simp [inInterval] at h
    exact h.1
  have h2 : t ≤ (n : Int) := by
    simp [inInterval] at h
    exact h.2
  exact ⟨h1, h2⟩

theorem ap3Free_sound (A : List Int) (h : ap3Free A = true) :
    AP3Free (ofIntList A) := by
  intro x y z hx hy hz hAP
  have hall := List.all_eq_true.mp h x hx
  have hall2 := List.all_eq_true.mp hall y hy
  have hall3 := List.all_eq_true.mp hall2 z hz
  have hfalse : isAP3 x y z = false := by simpa using hall3
  have htrue : isAP3 x y z = true := isAP3_of x y z hAP
  cases (htrue.symm.trans hfalse)

theorem completes_sound (A : List Int) (t : Int) (h : completes A t = true) :
    CompletedBy (ofIntList A) t := by
  obtain ⟨x, hx, hxy⟩ := List.any_eq_true.mp h
  obtain ⟨y, hy, hf⟩ := List.any_eq_true.mp hxy
  exact ⟨x, y, hx, hy, formsAP3_true x y t hf⟩

theorem range_mem (n : Nat) (t : Int) (ht : InIcc1 n t) :
    ∃ i, i ∈ List.range n ∧ (i : Int) + 1 = t := by
  have hge : 0 ≤ t - 1 := by
    have : 1 ≤ t := ht.1
    omega
  have hcast : ((t - 1).toNat : Int) = t - 1 := Int.toNat_of_nonneg hge
  have hlt : (t - 1).toNat < n := by
    have : t ≤ (n : Int) := ht.2
    have : (t - 1).toNat + 1 ≤ n := by
      have : ((t - 1).toNat : Int) + 1 ≤ n := by omega
      exact Int.ofNat_le.mp this
    omega
  refine ⟨(t - 1).toNat, List.mem_range.mpr hlt, ?_⟩
  omega

theorem maximal_and (n : Nat) (A : List Int) (h : maximal n A = true) :
    A.all (fun t => inInterval n t) = true ∧
    ap3Free A = true ∧
    ((List.range n).all fun i =>
      A.contains ((i : Int) + 1) || completes A ((i : Int) + 1)) = true := by
  have heq :
      maximal n A =
        (A.all (fun t => inInterval n t) &&
          ap3Free A &&
          (List.range n).all fun i =>
            A.contains ((i : Int) + 1) || completes A ((i : Int) + 1)) :=
    rfl
  rw [heq] at h
  have habc := (Bool.and_eq_true
      (A.all (fun t => inInterval n t) && ap3Free A)
      ((List.range n).all fun i =>
        A.contains ((i : Int) + 1) || completes A ((i : Int) + 1))).mp h
  have hab := (Bool.and_eq_true
      (A.all (fun t => inInterval n t)) (ap3Free A)).mp habc.1
  exact ⟨hab.1, hab.2, habc.2⟩

theorem maximal_sound (n : Nat) (A : List Int) (h : maximal n A = true) :
    MaximalAP3Free n (ofIntList A) := by
  obtain ⟨h1, h2, h3⟩ := maximal_and n A h
  refine ⟨?_, ap3Free_sound A h2, ?_⟩
  · intro t ht
    exact inInterval_true n t ((List.all_eq_true.mp h1) t ht)
  · intro t ht
    obtain ⟨i, hi, heq⟩ := range_mem n t ht
    have hcell := (List.all_eq_true.mp h3) i hi
    have hbool : t ∈ A ∨ completes A t = true := by
      simpa [heq] using hcell
    cases hbool with
    | inl hmem => exact Or.inl hmem
    | inr hcomp => exact Or.inr (completes_sound A t hcomp)

theorem inInterval_of (n : Nat) (t : Int) (h : InIcc1 n t) :
    inInterval n t = true := by
  simp [inInterval, InIcc1] at h ⊢
  exact ⟨h.1, h.2⟩

theorem formsAP3_of (x y t : Int) (h : FormsAP3 x y t) :
    formsAP3 x y t = true := by
  rcases h with ⟨hxy, hyt, hxt, hor⟩
  simp [formsAP3, hxy, hyt, hxt]
  rcases hor with h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr h)
  · exact Or.inr h

theorem completes_complete (A : List Int) (t : Int)
    (h : CompletedBy (ofIntList A) t) : completes A t = true := by
  obtain ⟨x, y, hx, hy, hf⟩ := h
  refine (List.any_eq_true.mpr ⟨x, hx, ?_⟩)
  exact List.any_eq_true.mpr ⟨y, hy, formsAP3_of x y t hf⟩

theorem ap3Free_complete (A : List Int) (h : AP3Free (ofIntList A)) :
    ap3Free A = true := by
  apply List.all_eq_true.mpr
  intro x hx
  apply List.all_eq_true.mpr
  intro y hy
  apply List.all_eq_true.mpr
  intro z hz
  have : isAP3 x y z = false := by
    by_cases hb : isAP3 x y z = true
    · have := h x y z hx hy hz (isAP3_true x y z hb)
      exact this.elim
    · exact Bool.eq_false_iff.mpr hb
  simpa using this

theorem range_of_mem (n : Nat) (i : Nat) (hi : i ∈ List.range n) :
    InIcc1 n ((i : Int) + 1) := by
  have : i < n := List.mem_range.mp hi
  simp [InIcc1]
  omega

/-- Completeness: a list-encoded maximal set is accepted by the boolean checker. -/
theorem maximal_complete (n : Nat) (A : List Int)
    (h : MaximalAP3Free n (ofIntList A)) : maximal n A = true := by
  rcases h with ⟨hsupp, hfree, hcov⟩
  have h1 : A.all (fun t => inInterval n t) = true := by
    apply List.all_eq_true.mpr
    intro t ht
    exact inInterval_of n t (hsupp t ht)
  have h2 : ap3Free A = true := ap3Free_complete A hfree
  have h3 :
      ((List.range n).all fun i =>
        A.contains ((i : Int) + 1) || completes A ((i : Int) + 1)) = true := by
    apply List.all_eq_true.mpr
    intro i hi
    have ht := range_of_mem n i hi
    have hcell := hcov ((i : Int) + 1) ht
    cases hcell with
    | inl hA =>
      have hc : A.contains ((i : Int) + 1) = true :=
        List.contains_iff_mem.mpr hA
      exact (Bool.or_eq_true _ _).mpr (Or.inl hc)
    | inr hC =>
      have hc : completes A ((i : Int) + 1) = true :=
        completes_complete A ((i : Int) + 1) hC
      exact (Bool.or_eq_true _ _).mpr (Or.inr hc)
  have hmax :
      maximal n A =
        (A.all (fun t => inInterval n t) &&
          ap3Free A &&
          (List.range n).all fun i =>
            A.contains ((i : Int) + 1) || completes A ((i : Int) + 1)) :=
    rfl
  rw [hmax, h1, h2, h3]
  decide

theorem maximal_iff (n : Nat) (A : List Int) :
    maximal n A = true ↔ MaximalAP3Free n (ofIntList A) :=
  ⟨maximal_sound n A, maximal_complete n A⟩

end Sat3
