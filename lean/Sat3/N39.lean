import Sat3.Search

namespace Sat3

theorem anyMaximalSearch6_39 : anyMaximalSearch 39 6 = false := by native_decide
theorem anyMaximalSearch7_39 : anyMaximalSearch 39 7 = false := by native_decide

theorem nodupInt_cert39 : NodupInt [1, 2, 5, 6, 15, 16, 19, 20] := by
  refine ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, ⟨?_, trivial⟩⟩⟩⟩⟩⟩⟩⟩
  · intro h; rcases h with h | h | h | h | h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h | h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h | h <;> first | omega | cases h
  · intro h; rcases h with h | h <;> first | omega | cases h
  · intro h; cases h

theorem HasMaximalOfSize_39_8 : HasMaximalOfSize 39 8 :=
  ⟨ofIntList [1, 2, 5, 6, 15, 16, 19, 20], [1, 2, 5, 6, 15, 16, 19, 20],
    maximal_of_cert_n39, nodupInt_cert39, rfl,
    ofIntList_of_memInt [1, 2, 5, 6, 15, 16, 19, 20]⟩

theorem sat3_eq_thirtynine : sat3 39 (by decide) = 8 :=
  sat3_eq_eight_of_pair5 39 (by decide) (by decide)
    anyMaximalSearch6_39 anyMaximalSearch7_39 HasMaximalOfSize_39_8

end Sat3
