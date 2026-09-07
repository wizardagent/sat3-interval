import Sat3.Basic
import Sat3.Block
import Sat3.Tblock

/-
  Endpoint covering, translation, and mixed-pair filling (paper Lemma 6.5).
-/

namespace Sat3

def EndpointCompleted (A : Int → Prop) (t : Int) : Prop :=
  ∃ x y, A x ∧ A y ∧ x ≠ y ∧ t ≠ x ∧ t ≠ y ∧ t = 2 * y - x

def EndpointCovers (A : Int → Prop) (lo hi : Int) : Prop :=
  ∀ t, lo ≤ t → t ≤ hi → A t ∨ EndpointCompleted A t

def shift (A : Int → Prop) (d : Int) : Int → Prop :=
  fun t => A (t - d)

theorem endpoint_implies_completed (A : Int → Prop) (t : Int)
    (h : EndpointCompleted A t) : CompletedBy A t := by
  rcases h with ⟨x, y, hx, hy, hxy, htx, hty, ht⟩
  exact ⟨x, y, hx, hy, hxy, by omega, by omega, Or.inr (Or.inl (by omega))⟩

theorem shift_mem (A : Int → Prop) (d x : Int) : shift A d (x + d) ↔ A x := by
  simp [shift]

theorem endpoint_covers_translate (A : Int → Prop) (lo hi d : Int)
    (h : EndpointCovers A lo hi) :
    EndpointCovers (shift A d) (lo + d) (hi + d) := by
  intro t hlo hhi
  have ht := h (t - d) (by omega) (by omega)
  cases ht with
  | inl hA =>
    exact Or.inl hA
  | inr hE =>
    rcases hE with ⟨x, y, hx, hy, hxy, htx, hty, heq⟩
    refine Or.inr ⟨x + d, y + d, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (shift_mem A d x).mpr hx
    · exact (shift_mem A d y).mpr hy
    · omega
    · omega
    · omega
    · omega

def unionShift (A : Int → Prop) (d : Int) : Int → Prop :=
  fun t => A t ∨ shift A d t

theorem unionShift_of_left (A : Int → Prop) (d t : Int) (h : A t) :
    unionShift A d t :=
  Or.inl h

theorem unionShift_of_right (A : Int → Prop) (d t : Int) (h : shift A d t) :
    unionShift A d t :=
  Or.inr h

/-- If `A` endpoint-covers `[1, d+5]` and `d > 0`, then `A ∪ (A+d)`
endpoint-covers `[1, 3d+5]`. Paper Lemma 6.5. -/
theorem mixed_fills_right (A : Int → Prop) (d : Int)
    (hd : 0 < d)
    (hA : EndpointCovers A 1 (d + 5))
    (hsupp : ∀ x, A x → 1 ≤ x ∧ x ≤ d + 5) :
    EndpointCovers (unionShift A d) 1 (3 * d + 5) := by
  intro t hlo hhi
  by_cases hL : t ≤ d + 5
  · have ht := hA t hlo hL
    cases ht with
    | inl hmem => exact Or.inl (unionShift_of_left A d t hmem)
    | inr hE =>
      rcases hE with ⟨x, y, hx, hy, hxy, htx, hty, heq⟩
      exact Or.inr ⟨x, y, unionShift_of_left A d x hx,
        unionShift_of_left A d y hy, hxy, htx, hty, heq⟩
  · by_cases hM : t ≤ 2 * d + 5
    · have ht := endpoint_covers_translate A 1 (d + 5) d hA t (by omega) (by omega)
      cases ht with
      | inl hmem => exact Or.inl (unionShift_of_right A d t hmem)
      | inr hE =>
        rcases hE with ⟨x, y, hx, hy, hxy, htx, hty, heq⟩
        exact Or.inr ⟨x, y, unionShift_of_right A d x hx,
          unionShift_of_right A d y hy, hxy, htx, hty, heq⟩
    · -- right piece: t ∈ [2d+6, 3d+5], u = t - 2d ∈ [6, d+5]
      have hu_lo : 1 ≤ t - 2 * d := by omega
      have hu_hi : t - 2 * d ≤ d + 5 := by omega
      have hu := hA (t - 2 * d) hu_lo hu_hi
      cases hu with
      | inl hmem =>
        -- t = 2(u+d) - u
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
        rcases hE with ⟨x, y, hx, hy, hxy, htx, hty, heq⟩
        -- t = 2(y+d) - x
        refine Or.inr ⟨x, y + d, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact unionShift_of_left A d x hx
        · have : shift A d (y + d) := by
            simp [shift]
            exact hy
          exact unionShift_of_right A d (y + d) this
        · -- x ≠ y+d
          intro hxy'
          have hxbd := hsupp x hx
          have hybd := hsupp y hy
          omega
        · -- t ≠ x
          intro htx'
          have hxbd := hsupp x hx
          omega
        · -- t ≠ y+d
          intro hty'
          have hybd := hsupp y hy
          omega
        · omega

/-- Distinctness of mixed parents under a diameter bound. Paper Lemma 8.3. -/
theorem mixed_parents_distinct (lo hi d x y : Int)
    (_hd : 0 < d)
    (hdiam : 2 * (hi - lo) < d)
    (hxlo : lo ≤ x) (hxhi : x ≤ hi)
    (hylo : lo ≤ y) (_hyhi : y ≤ hi)
    (_hxy : x ≠ y) :
    x ≠ y + d := by
  intro h
  omega

theorem mixed_t_ne_x (lo hi d x y : Int)
    (_hd : 0 < d)
    (hdiam : 2 * (hi - lo) < d)
    (hxlo : lo ≤ x) (hxhi : x ≤ hi)
    (hylo : lo ≤ y) (_hyhi : y ≤ hi) :
    2 * (y + d) - x ≠ x := by
  omega

theorem mixed_t_ne_yd (lo hi d x y : Int)
    (_hd : 0 < d)
    (hdiam : 2 * (hi - lo) < d)
    (hxlo : lo ≤ x) (hxhi : x ≤ hi)
    (hylo : lo ≤ y) (_hyhi : y ≤ hi) :
    2 * (y + d) - x ≠ y + d := by
  omega

/-- Mixed endpoints `2(A+d)-A` cover `[lo+2d, hi+2d]` when `2(hi-lo)<d`.
The bound is on the length of the covered interval, so this does not
apply to `I(A)` with `d = 11 * 4^k` (paper Lemma 8.3 uses the support
diameter `2(max A - min A) < d` instead). -/
theorem mixed_double_shift (A : Int → Prop) (lo hi d : Int)
    (hd : 0 < d)
    (hdiam : 2 * (hi - lo) < d)
    (hA : EndpointCovers A lo hi)
    (hsupp : ∀ z, A z → lo ≤ z ∧ z ≤ hi) :
    EndpointCovers (unionShift A d) (lo + 2 * d) (hi + 2 * d) := by
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
    rcases hE with ⟨x, y, hx, hy, hxy, htx, hty, heq⟩
    have hxbd := hsupp x hx
    have hybd := hsupp y hy
    refine Or.inr ⟨x, y + d, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact unionShift_of_left A d x hx
    · have : shift A d (y + d) := by
        simp [shift]
        exact hy
      exact unionShift_of_right A d (y + d) this
    · exact mixed_parents_distinct lo hi d x y hd hdiam hxbd.1 hxbd.2 hybd.1 hybd.2 hxy
    · intro htx'
      have := mixed_t_ne_x lo hi d x y hd hdiam hxbd.1 hxbd.2 hybd.1 hybd.2
      omega
    · intro hty'
      have := mixed_t_ne_yd lo hi d x y hd hdiam hxbd.1 hxbd.2 hybd.1 hybd.2
      omega
    · omega

end Sat3
