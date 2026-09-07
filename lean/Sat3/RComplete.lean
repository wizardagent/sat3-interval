import Sat3.Basic
import Sat3.Cover

/-
  R-complete sets and placement into [n]. Paper §§8–9.
-/

namespace Sat3

/-- `A ⊆ [0, R]` is *R-complete* if it is 3-AP-free and its endpoint
completions fill `[-R, 2R]`. -/
def IsRComplete (R : Int) (A : Int → Prop) : Prop :=
  (∀ z, A z → 0 ≤ z ∧ z ≤ R) ∧
  AP3Free A ∧
  EndpointCovers A (-R) (2 * R)

theorem AP3Free_shift (A : Int → Prop) (d : Int) (h : AP3Free A) :
    AP3Free (shift A d) := by
  intro x y z hx hy hz hAP
  rcases hAP with ⟨hxy, hyz, hxz, hsum⟩
  exact h (x - d) (y - d) (z - d) hx hy hz
    ⟨by omega, by omega, by omega, by omega⟩

/-- If `A` lives in `[0, S]` and `d > 2S`, then `A ∪ (A + d)` is 3-AP-free. -/
theorem separated_union_AP3Free (A : Int → Prop) (S d : Int)
    (_hS : 0 ≤ S) (hd : 2 * S < d)
    (hsupp : ∀ z, A z → 0 ≤ z ∧ z ≤ S)
    (hfree : AP3Free A) :
    AP3Free (unionShift A d) := by
  intro x y z hx hy hz hAP
  have hx' : A x ∨ A (x - d) := hx
  have hy' : A y ∨ A (y - d) := hy
  have hz' : A z ∨ A (z - d) := hz
  rcases hx' with hxL | hxR
  · rcases hy' with hyL | hyR
    · rcases hz' with hzL | hzR
      · exact hfree x y z hxL hyL hzL hAP
      · have hxbd := hsupp x hxL
        have hybd := hsupp y hyL
        have hzbd := hsupp (z - d) hzR
        rcases hAP with ⟨_, _, _, hsum⟩
        omega
    · rcases hz' with hzL | hzR
      · have hxbd := hsupp x hxL
        have hybd := hsupp (y - d) hyR
        have hzbd := hsupp z hzL
        rcases hAP with ⟨_, _, _, hsum⟩
        omega
      · have hxbd := hsupp x hxL
        have hybd := hsupp (y - d) hyR
        have hzbd := hsupp (z - d) hzR
        rcases hAP with ⟨_, _, _, hsum⟩
        omega
  · rcases hy' with hyL | hyR
    · rcases hz' with hzL | hzR
      · have hxbd := hsupp (x - d) hxR
        have hybd := hsupp y hyL
        have hzbd := hsupp z hzL
        rcases hAP with ⟨_, _, _, hsum⟩
        omega
      · have hxbd := hsupp (x - d) hxR
        have hybd := hsupp y hyL
        have hzbd := hsupp (z - d) hzR
        rcases hAP with ⟨_, _, _, hsum⟩
        omega
    · rcases hz' with hzL | hzR
      · have hxbd := hsupp (x - d) hxR
        have hybd := hsupp (y - d) hyR
        have hzbd := hsupp z hzL
        rcases hAP with ⟨_, _, _, hsum⟩
        omega
      · exact AP3Free_shift A d hfree x y z hxR hyR hzR hAP

/-- Mixed endpoints `2(A+d)-A` fill `I(A)+2d` when `d > 2S` and `A ⊆ [0,S]`. -/
theorem mixed_right_I (A : Int → Prop) (S d : Int)
    (_hS : 0 ≤ S) (hd : 2 * S < d)
    (hA : EndpointCovers A (-S) (2 * S))
    (hsupp : ∀ z, A z → 0 ≤ z ∧ z ≤ S) :
    EndpointCovers (unionShift A d) (-S + 2 * d) (2 * S + 2 * d) := by
  intro t hlo hhi
  have hu := hA (t - 2 * d) (by omega) (by omega)
  cases hu with
  | inl hmem =>
    refine Or.inr ⟨t - 2 * d, t - d, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact unionShift_of_left A d (t - 2 * d) hmem
    · have : shift A d (t - d) := by
        simp [shift]
        have : t - d - d = t - 2 * d := by omega
        rw [this]
        exact hmem
      exact unionShift_of_right A d (t - d) this
    · omega
    · omega
    · omega
    · omega
  | inr hE =>
    rcases hE with ⟨x, y, hx, hy, hxy, _htx, _hty, heq⟩
    have hxbd := hsupp x hx
    have hybd := hsupp y hy
    refine Or.inr ⟨x, y + d, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact unionShift_of_left A d x hx
    · have : shift A d (y + d) := by
        simp [shift]
        exact hy
      exact unionShift_of_right A d (y + d) this
    · intro hxy'; omega
    · intro htx'; omega
    · intro hty'; omega
    · omega

/-- Mixed endpoints `2A-(A+d)` fill `I(A)-d`. -/
theorem mixed_left_I (A : Int → Prop) (S d : Int)
    (_hS : 0 ≤ S) (hd : 2 * S < d)
    (hA : EndpointCovers A (-S) (2 * S))
    (hsupp : ∀ z, A z → 0 ≤ z ∧ z ≤ S) :
    EndpointCovers (unionShift A d) (-S - d) (2 * S - d) := by
  intro t hlo hhi
  have hu := hA (t + d) (by omega) (by omega)
  cases hu with
  | inl hmem =>
    refine Or.inr ⟨t + 2 * d, t + d, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have : shift A d (t + 2 * d) := by
        simp [shift]
        have : t + 2 * d - d = t + d := by omega
        rw [this]
        exact hmem
      exact unionShift_of_right A d (t + 2 * d) this
    · exact unionShift_of_left A d (t + d) hmem
    · omega
    · omega
    · omega
    · omega
  | inr hE =>
    rcases hE with ⟨x, y, hx, hy, hxy, _htx, _hty, heq⟩
    have hxbd := hsupp x hx
    have hybd := hsupp y hy
    refine Or.inr ⟨x + d, y, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have : shift A d (x + d) := by
        simp [shift]
        exact hx
      exact unionShift_of_right A d (x + d) this
    · exact unionShift_of_left A d y hy
    · intro hxy'; omega
    · intro htx'; omega
    · intro hty'; omega
    · omega

/-- Four-interval covering: if `A` is `S`-complete on endpoints and
`2S+1 ≤ d ≤ 3S+1`, then `A ∪ (A+d)` endpoint-covers `I` of the union. -/
theorem admissible_shift_covers (A : Int → Prop) (S d : Int)
    (hS : 0 ≤ S)
    (hdlo : 2 * S + 1 ≤ d)
    (hdhi : d ≤ 3 * S + 1)
    (hA : EndpointCovers A (-S) (2 * S))
    (hsupp : ∀ z, A z → 0 ≤ z ∧ z ≤ S) :
    EndpointCovers (unionShift A d) (-(S + d)) (2 * (S + d)) := by
  intro t hlo hhi
  have hdpos : 2 * S < d := by omega
  by_cases hL : t ≤ 2 * S - d
  · exact mixed_left_I A S d hS hdpos hA hsupp t (by omega) hL
  · by_cases hM : t ≤ 2 * S
    · have h := hA t (by omega) hM
      cases h with
      | inl hmem => exact Or.inl (unionShift_of_left A d t hmem)
      | inr hE =>
        rcases hE with ⟨x, y, hx, hy, hxy, htx, hty, heq⟩
        exact Or.inr ⟨x, y, unionShift_of_left A d x hx,
          unionShift_of_left A d y hy, hxy, htx, hty, heq⟩
    · by_cases hR : t ≤ 2 * S + d
      · have h := endpoint_covers_translate A (-S) (2 * S) d hA t
          (by omega) (by omega)
        cases h with
        | inl hmem => exact Or.inl (unionShift_of_right A d t hmem)
        | inr hE =>
          rcases hE with ⟨x, y, hx, hy, hxy, htx, hty, heq⟩
          exact Or.inr ⟨x, y, unionShift_of_right A d x hx,
            unionShift_of_right A d y hy, hxy, htx, hty, heq⟩
      · exact mixed_right_I A S d hS hdpos hA hsupp t (by omega) (by omega)

theorem unionShift_supp (A : Int → Prop) (S d : Int)
    (hd : 0 ≤ d)
    (hsupp : ∀ z, A z → 0 ≤ z ∧ z ≤ S)
    {t : Int} (ht : unionShift A d t) :
    0 ≤ t ∧ t ≤ S + d := by
  cases ht with
  | inl h =>
    have := hsupp t h
    constructor <;> omega
  | inr h =>
    have := hsupp (t - d) h
    constructor <;> omega

/-- One admissible digit: an `S`-complete set remains `(S+d)`-complete. -/
theorem rcomplete_admissible_step (A : Int → Prop) (S d : Int)
    (hS : 0 ≤ S)
    (hdlo : 2 * S + 1 ≤ d)
    (hdhi : d ≤ 3 * S + 1)
    (hR : IsRComplete S A) :
    IsRComplete (S + d) (unionShift A d) := by
  rcases hR with ⟨hsupp, hfree, hcov⟩
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    exact unionShift_supp A S d (by omega) hsupp hz
  · exact separated_union_AP3Free A S d hS (by omega) hsupp hfree
  · have hcov' := admissible_shift_covers A S d hS hdlo hdhi hcov hsupp
    intro t hlo hhi
    have : 2 * (S + d) = 2 * S + 2 * d := by omega
    exact hcov' t (by omega) (by omega)

/-- `{0,1}` is `1`-complete. -/
theorem rcomplete_01 : IsRComplete 1 (fun t => t = 0 ∨ t = 1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro z hz; omega
  · intro x y z hx hy hz hAP
    rcases hAP with ⟨hxy, hyz, hxz, hsum⟩
    omega
  · intro t hlo hhi
    have hcases : t = -1 ∨ t = 0 ∨ t = 1 ∨ t = 2 := by omega
    rcases hcases with h | h | h | h
    · subst t
      refine Or.inr ⟨1, 0, Or.inr rfl, Or.inl rfl, by omega, by omega, by omega, by omega⟩
    · subst t; exact Or.inl (Or.inl rfl)
    · subst t; exact Or.inl (Or.inr rfl)
    · subst t
      refine Or.inr ⟨0, 1, Or.inl rfl, Or.inr rfl, by omega, by omega, by omega, by omega⟩

/-- Left placement: if `R+1 ≤ n ≤ 2R+1`, then `A+1` is maximal in `[n]`. -/
theorem rcomplete_place_left (A : Int → Prop) (R : Int) (n : Nat)
    (_hR : 0 ≤ R)
    (hn1 : R + 1 ≤ (n : Int))
    (hn2 : (n : Int) ≤ 2 * R + 1)
    (hA : IsRComplete R A) :
    MaximalAP3Free n (shift A 1) := by
  rcases hA with ⟨hsupp, hfree, hcov⟩
  refine ⟨?_, AP3Free_shift A 1 hfree, ?_⟩
  · intro t ht
    have hbd := hsupp (t - 1) ht
    simp [InIcc1]
    omega
  · intro t ht
    simp [InIcc1] at ht
    have hI := endpoint_covers_translate A (-R) (2 * R) 1 hcov t
      (by omega) (by omega)
    cases hI with
    | inl hmem => exact Or.inl hmem
    | inr hE => exact Or.inr (endpoint_implies_completed _ _ hE)

/-- Right placement: if `2R+1 ≤ n ≤ 3R+1`, then `A+(n-2R)` is maximal in `[n]`. -/
theorem rcomplete_place_right (A : Int → Prop) (R : Int) (n : Nat)
    (_hR : 0 ≤ R)
    (hn1 : 2 * R + 1 ≤ (n : Int))
    (hn2 : (n : Int) ≤ 3 * R + 1)
    (hA : IsRComplete R A) :
    MaximalAP3Free n (shift A ((n : Int) - 2 * R)) := by
  rcases hA with ⟨hsupp, hfree, hcov⟩
  refine ⟨?_, AP3Free_shift A ((n : Int) - 2 * R) hfree, ?_⟩
  · intro t ht
    have hbd := hsupp (t - ((n : Int) - 2 * R)) ht
    simp [InIcc1]
    omega
  · intro t ht
    simp [InIcc1] at ht
    have hI := endpoint_covers_translate A (-R) (2 * R) ((n : Int) - 2 * R) hcov t
      (by omega) (by omega)
    cases hI with
    | inl hmem => exact Or.inl hmem
    | inr hE => exact Or.inr (endpoint_implies_completed _ _ hE)

/-- `{0,1}` placed as `{1,2}` is maximal in `[2]`. -/
theorem maximal_12_n2 :
    MaximalAP3Free 2 (shift (fun t => t = 0 ∨ t = 1) 1) :=
  rcomplete_place_left (fun t => t = 0 ∨ t = 1) 1 2
    (by decide) (by decide) (by decide) rcomplete_01

end Sat3
