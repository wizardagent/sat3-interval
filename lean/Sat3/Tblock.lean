import Sat3.Basic
import Sat3.Block

/-
  The template T = {0,1,4,5}. Every point of S(c) is c + t for some t in T.
-/

namespace Sat3

def memT (t : Int) : Prop :=
  t = 0 ∨ t = 1 ∨ t = 4 ∨ t = 5

theorem memS_iff_T (c x : Int) : memS c x ↔ ∃ t, memT t ∧ x = c + t := by
  constructor
  · intro h
    simp [memS] at h
    rcases h with h | h | h | h
    · exact ⟨0, Or.inl rfl, by omega⟩
    · exact ⟨1, Or.inr (Or.inl rfl), by omega⟩
    · exact ⟨4, Or.inr (Or.inr (Or.inl rfl)), by omega⟩
    · exact ⟨5, Or.inr (Or.inr (Or.inr rfl)), by omega⟩
  · rintro ⟨t, ht, hx⟩
    simp [memS, memT] at ht ⊢
    omega

theorem T_diff_bound (t t1 t2 : Int)
    (ht : memT t) (h1 : memT t1) (h2 : memT t2) :
    -10 ≤ 2 * t - t1 - t2 ∧ 2 * t - t1 - t2 ≤ 10 := by
  simp [memT] at ht h1 h2
  omega

/-- The only 3-APs in T are degenerate. -/
theorem T_degenerate (t t1 t2 : Int)
    (ht : memT t) (h1 : memT t1) (h2 : memT t2)
    (h : 2 * t = t1 + t2) : t = t1 ∧ t = t2 := by
  simp [memT] at ht h1 h2
  omega

theorem T_AP3Free : AP3Free memT := by
  intro x y z hx hy hz hAP
  rcases hAP with ⟨hxy, hyz, hxz, hsum⟩
  have := T_degenerate y x z hy hx hz (by omega)
  omega

end Sat3
