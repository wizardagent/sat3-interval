import Sat3.Sound
import Sat3.Cert

/-
  No 4-point maximal set in [17]. Combined with interpolation
  `sat3 17 ≤ 5` and the pair bound (no 3-point set once n > 12),
  this pins sat_3(17) = 5.
-/

namespace Sat3

def quads (n : Nat) : List (List Int) :=
  (List.range n).flatMap fun (i : Nat) =>
    (List.range n).flatMap fun (j : Nat) =>
      (List.range n).flatMap fun (k : Nat) =>
        (List.range n).map fun (l : Nat) =>
          ([(i : Int) + 1, (j : Int) + 1, (k : Int) + 1, (l : Int) + 1] : List Int)

def anyMaximal4 (n : Nat) : Bool :=
  (quads n).any fun A => maximal n A

theorem anyMaximal4_17 : anyMaximal4 17 = false := by native_decide

theorem quads_has (n : Nat) (w x y z : Int)
    (hw : InIcc1 n w) (hx : InIcc1 n x) (hy : InIcc1 n y) (hz : InIcc1 n z) :
    [w, x, y, z] ∈ quads n := by
  obtain ⟨i, hi, hiw⟩ := range_mem n w hw
  obtain ⟨j, hj, hjx⟩ := range_mem n x hx
  obtain ⟨k, hk, hky⟩ := range_mem n y hy
  obtain ⟨l, hl, hlz⟩ := range_mem n z hz
  unfold quads
  refine List.mem_flatMap.mpr ⟨i, hi, ?_⟩
  refine List.mem_flatMap.mpr ⟨j, hj, ?_⟩
  refine List.mem_flatMap.mpr ⟨k, hk, ?_⟩
  refine List.mem_map.mpr ⟨l, hl, ?_⟩
  simp [hiw, hjx, hky, hlz]

theorem anyMaximal4_of_list (n : Nat) (w x y z : Int)
    (h : MaximalAP3Free n (ofIntList [w, x, y, z])) :
    anyMaximal4 n = true := by
  have hw := h.1 w (by simp [ofIntList])
  have hx := h.1 x (by simp [ofIntList])
  have hy := h.1 y (by simp [ofIntList])
  have hz := h.1 z (by simp [ofIntList])
  have hmem := quads_has n w x y z hw hx hy hz
  have hmax : maximal n [w, x, y, z] = true := maximal_complete n [w, x, y, z] h
  unfold anyMaximal4
  exact List.any_eq_true.mpr ⟨[w, x, y, z], hmem, hmax⟩

end Sat3
