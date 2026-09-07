import Sat3.Search

namespace Sat3

theorem anyMaximalSearch6_36 : anyMaximalSearch 36 6 = false := by native_decide
theorem anyMaximalSearch7_36 : anyMaximalSearch 36 7 = false := by native_decide

theorem nodupInt_cert36 : NodupInt [1, 2, 5, 6, 14, 15, 18, 19] := by
  refine ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, trivial⟩⟩⟩⟩⟩⟩⟩⟩
  · intro h; rcases h with h | h | h | h | h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h | h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h <;> first | omega | cases h
  · intro h; cases h

theorem HasMaximalOfSize_36_8 : HasMaximalOfSize 36 8 :=
  ⟨ofIntList [1, 2, 5, 6, 14, 15, 18, 19], [1, 2, 5, 6, 14, 15, 18, 19],
    maximal_of_cert_n36, nodupInt_cert36, rfl,
    ofIntList_of_memInt [1, 2, 5, 6, 14, 15, 18, 19]⟩

theorem sat3_eq_thirtysix : sat3 36 (by decide) = 8 :=
  sat3_eq_eight_of_pair5 36 (by decide) (by decide)
    anyMaximalSearch6_36 anyMaximalSearch7_36 HasMaximalOfSize_36_8

end Sat3
