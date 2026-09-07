import Sat3.Search

namespace Sat3

theorem anyMaximalSearch6_40 : anyMaximalSearch 40 6 = false := by native_decide
theorem anyMaximalSearch7_40 : anyMaximalSearch 40 7 = false := by native_decide

theorem nodupInt_cert40 : NodupInt [1, 2, 5, 6, 16, 17, 20, 21] := by
  refine ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, trivial⟩⟩⟩⟩⟩⟩⟩⟩
  · intro h; rcases h with h | h | h | h | h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h | h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h <;> first | omega | cases h
  · intro h; cases h

theorem HasMaximalOfSize_40_8 : HasMaximalOfSize 40 8 :=
  ⟨ofIntList [1, 2, 5, 6, 16, 17, 20, 21], [1, 2, 5, 6, 16, 17, 20, 21],
    maximal_of_cert_n40, nodupInt_cert40, rfl,
    ofIntList_of_memInt [1, 2, 5, 6, 16, 17, 20, 21]⟩

theorem sat3_eq_forty : sat3 40 (by decide) = 8 :=
  sat3_eq_eight_of_pair5 40 (by decide) (by decide)
    anyMaximalSearch6_40 anyMaximalSearch7_40 HasMaximalOfSize_40_8

end Sat3
