import Sat3.Sound
import Sat3.Cert
import Sat3.PairBound

/-
  No 3-point maximal set in [n] for 6 ≤ n ≤ 12.
  Combined with the pair bound (no 2-point set once n > 5)
  and the size-4 construction, this pins sat_3(n) = 4.
-/

namespace Sat3

def triples (n : Nat) : List (List Int) :=
  (List.range n).flatMap fun (i : Nat) =>
    (List.range n).flatMap fun (j : Nat) =>
      (List.range n).map fun (k : Nat) =>
        ([(i : Int) + 1, (j : Int) + 1, (k : Int) + 1] : List Int)

def anyMaximal3 (n : Nat) : Bool :=
  (triples n).any fun A => maximal n A

theorem anyMaximal3_6 : anyMaximal3 6 = false := by native_decide
theorem anyMaximal3_7 : anyMaximal3 7 = false := by native_decide
theorem anyMaximal3_8 : anyMaximal3 8 = false := by native_decide
theorem anyMaximal3_9 : anyMaximal3 9 = false := by native_decide
theorem anyMaximal3_10 : anyMaximal3 10 = false := by native_decide
theorem anyMaximal3_11 : anyMaximal3 11 = false := by native_decide
theorem anyMaximal3_12 : anyMaximal3 12 = false := by native_decide

theorem mem_range_of_inIcc1 (n : Nat) (t : Int) (h : InIcc1 n t) :
    ∃ i, i ∈ List.range n ∧ (i : Int) + 1 = t :=
  range_mem n t h

theorem triples_has (n : Nat) (x y z : Int)
    (hx : InIcc1 n x) (hy : InIcc1 n y) (hz : InIcc1 n z) :
    [x, y, z] ∈ triples n := by
  obtain ⟨i, hi, hix⟩ := mem_range_of_inIcc1 n x hx
  obtain ⟨j, hj, hjy⟩ := mem_range_of_inIcc1 n y hy
  obtain ⟨k, hk, hkz⟩ := mem_range_of_inIcc1 n z hz
  unfold triples
  refine List.mem_flatMap.mpr ⟨i, hi, ?_⟩
  refine List.mem_flatMap.mpr ⟨j, hj, ?_⟩
  refine List.mem_map.mpr ⟨k, hk, ?_⟩
  simp [hix, hjy, hkz]

theorem anyMaximal3_of_list (n : Nat) (x y z : Int)
    (h : MaximalAP3Free n (ofIntList [x, y, z])) :
    anyMaximal3 n = true := by
  have hx := h.1 x (by simp [ofIntList])
  have hy := h.1 y (by simp [ofIntList])
  have hz := h.1 z (by simp [ofIntList])
  have hmem := triples_has n x y z hx hy hz
  have hmax : maximal n [x, y, z] = true := maximal_complete n [x, y, z] h
  unfold anyMaximal3
  exact List.any_eq_true.mpr ⟨[x, y, z], hmem, hmax⟩

end Sat3
